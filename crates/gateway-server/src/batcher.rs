//! Group commit for admissions and settlements.
//!
//! h5i-app's engine runs each command in its own SERIALIZABLE transaction
//! under a tenant-wide lock, so a tenant commits one command at a time. The
//! batcher keeps one worker per tenant: requests that arrive while a
//! transaction is in flight queue up, and the next transaction commits them
//! all as one kernel `Batch`, which `proofs/Theorems.lean`
//! (`batch_sequential`) shows is exactly the sequential run of its items. A
//! request's answer is the same as if it had been sent alone; only the
//! number of transactions changes.

use crate::kernel::{Gateway, GatewayStore, Unavailable};
use gateway_kernel::{BatchItem, BatchOp, Command, Error, ItemOutcome, Principal, Reply};
use h5i_app_pg::Engine;
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use tokio::sync::{mpsc, oneshot};

type Answer = Result<Result<Reply, Error>, Unavailable>;

struct Job {
    item: BatchItem,
    reply: oneshot::Sender<Answer>,
}

pub struct Batcher {
    engine: Arc<Engine<Gateway, GatewayStore>>,
    max: usize,
    workers: Mutex<HashMap<u64, mpsc::UnboundedSender<Job>>>,
}

impl Batcher {
    /// At most `max` items per transaction.
    pub fn new(engine: Arc<Engine<Gateway, GatewayStore>>, max: usize) -> Self {
        Batcher { engine, max: max.max(1), workers: Mutex::new(HashMap::new()) }
    }

    /// The item an `Admit` or `Settle` becomes, or `None` for any other command.
    pub fn item(actor: &Principal, cmd: &Command) -> Option<BatchItem> {
        let op = match cmd {
            Command::Admit { model, prompt_tokens, max_tokens, exclude } => {
                BatchOp::Admit { model: model.clone(), prompt_tokens: *prompt_tokens, max_tokens: *max_tokens, exclude: exclude.clone() }
            }
            Command::Settle { reservation, prompt_tokens, completion_tokens, status } => {
                BatchOp::Settle { reservation: *reservation, prompt_tokens: *prompt_tokens, completion_tokens: *completion_tokens, status: *status }
            }
            _ => return None,
        };
        Some(BatchItem { key: actor.key, master: actor.master, op })
    }

    /// Run `item` for `actor`'s tenant in the next batch.
    pub async fn run(&self, org: u64, item: BatchItem) -> Answer {
        let (reply, answer) = oneshot::channel();
        let job = Job { item, reply };
        let queue = {
            let mut workers = self.workers.lock().unwrap_or_else(|e| e.into_inner());
            let queue = workers.entry(org).or_insert_with(|| self.spawn(org));
            if queue.is_closed() {
                *queue = self.spawn(org);
            }
            queue.clone()
        };
        if let Err(mpsc::error::SendError(job)) = queue.send(job) {
            // The worker is gone (its task panicked): run this one alone.
            return commit(&self.engine, org, vec![job.item]).await.pop().unwrap_or_else(|| Err(Unavailable("batch lost".into())));
        }
        answer.await.unwrap_or_else(|_| Err(Unavailable("batch worker stopped".into())))
    }

    fn spawn(&self, org: u64) -> mpsc::UnboundedSender<Job> {
        let (tx, mut rx) = mpsc::unbounded_channel::<Job>();
        let (engine, max) = (self.engine.clone(), self.max);
        tokio::spawn(async move {
            while let Some(first) = rx.recv().await {
                let mut jobs = vec![first];
                while jobs.len() < max {
                    match rx.try_recv() {
                        Ok(j) => jobs.push(j),
                        Err(_) => break,
                    }
                }
                let (items, replies): (Vec<_>, Vec<_>) = jobs.into_iter().map(|j| (j.item, j.reply)).unzip();
                let answers = commit(&engine, org, items).await;
                for (reply, answer) in replies.into_iter().zip(answers) {
                    let _ = reply.send(answer);
                }
            }
        });
        tx
    }
}

/// One transaction for all `items`, as the tenant's master principal.
async fn commit(engine: &Engine<Gateway, GatewayStore>, org: u64, items: Vec<BatchItem>) -> Vec<Answer> {
    let n = items.len();
    let master = Principal { org, key: 0, master: true, now: 0 };
    match engine.execute(&master, &Command::Batch { items }).await {
        Ok(Ok(Reply::Batch(outs))) if outs.len() == n => outs.into_iter().map(|o| Ok(answer(o))).collect(),
        Ok(other) => {
            tracing::error!(?other, "unexpected batch reply");
            (0..n).map(|_| Err(Unavailable("unexpected batch reply".into()))).collect()
        }
        Err(e) => {
            let msg = e.to_string();
            (0..n).map(|_| Err(Unavailable(msg.clone()))).collect()
        }
    }
}

fn answer(o: ItemOutcome) -> Result<Reply, Error> {
    match o {
        ItemOutcome::Admitted { reservation, deployment, amount } => Ok(Reply::Admitted { reservation, deployment, amount }),
        ItemOutcome::Settled { cost } => Ok(Reply::Settled { cost }),
        ItemOutcome::Refused(e) => Err(e),
    }
}
