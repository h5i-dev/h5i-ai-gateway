// Chat with any model the signed-in key may call, streaming or not, and see
// what the gateway reports about the call: latency, cost, deployment.

import { api, chat } from "../api.js";
import { errorBox, field, h, mount } from "../dom.js";
import * as fmt from "../format.js";
import { pageHead } from "./common.js";

export function playgroundView(main, { onCleanup }) {
  const model = h("select", { disabled: true }, h("option", null, "Loading models…"));
  const stream = h("input", { type: "checkbox", checked: true });
  const temperature = h("input", { type: "number", min: "0", max: "2", step: "0.1", placeholder: "Model default" });
  const maxTokens = h("input", { type: "number", min: "1", step: "1", placeholder: "Gateway default" });
  const system = h("textarea", { rows: 3, placeholder: "Optional system prompt" });
  const prompt = h("textarea", { rows: 3, placeholder: "Send a message… (Ctrl+Enter to send)", "aria-label": "Message" });
  const send = h("button", { type: "submit", class: "primary" }, "Send");
  const stop = h("button", { type: "button", hidden: true }, "Stop");
  const clear = h("button", { type: "button", class: "ghost" }, "Clear chat");
  const transcript = h("div", { class: "transcript", role: "log", "aria-live": "polite", "aria-label": "Conversation" },
    h("p", { class: "placeholder" }, "Pick a model and send a message. Calls are charged to the key you signed in with."));
  const stats = h("dl", { class: "stats" });
  const notice = h("div");

  /** The conversation so far, as sent to the API. */
  let history = [];
  let controller = null;

  const statRows = (rows) => mount(stats, rows.flatMap(([k, v]) => [h("dt", null, k), h("dd", null, v)]));
  statRows([["Status", "—"], ["Latency", "—"], ["First token", "—"], ["Cost", "—"], ["Tokens in / out", "—"], ["Model group", "—"], ["Deployment", "—"], ["Retries / fallbacks", "—"]]);

  const bubble = (role, text) => h("div", { class: ["msg", role] }, h("span", { class: "role" }, role), h("span", { class: "text" }, text));

  async function submit(e) {
    e?.preventDefault();
    const text = prompt.value.trim();
    if (!text || controller || !model.value) return;
    if (transcript.querySelector(".placeholder")) mount(transcript);
    mount(notice);
    history.push({ role: "user", content: text });
    const asked = bubble("user", text);
    transcript.append(asked);
    prompt.value = "";
    const out = bubble("assistant", "");
    out.classList.add("streaming");
    transcript.append(out);
    transcript.scrollTop = transcript.scrollHeight;
    const body = {
      model: model.value,
      messages: [...(system.value.trim() ? [{ role: "system", content: system.value.trim() }] : []), ...history],
      stream: stream.checked,
    };
    if (stream.checked) body.stream_options = { include_usage: true };
    if (temperature.value !== "") body.temperature = Number(temperature.value);
    if (maxTokens.value !== "") body.max_tokens = Number(maxTokens.value);

    controller = new AbortController();
    send.disabled = true;
    stop.hidden = false;
    statRows([["Status", "Waiting…"]]);
    const started = performance.now();
    const textEl = out.querySelector(".text");
    try {
      const r = await chat(body, {
        signal: controller.signal,
        onDelta: (piece) => {
          textEl.textContent += piece;
          transcript.scrollTop = transcript.scrollHeight;
        },
      });
      const total = performance.now() - started;
      history.push({ role: "assistant", content: r.content });
      const cost = r.headers.get("x-litellm-response-cost");
      statRows([
        ["Status", `${r.status} · ${r.finishReason ?? "done"}`],
        ["Latency", fmt.ms(total)],
        ["First token", fmt.ms(r.firstTokenMs)],
        ["Cost", cost !== null ? fmt.usd(Number(cost)) : h("span", { title: "A streamed call is charged when the stream ends, after the headers are sent; see Spend." }, "settled after the stream")],
        ["Tokens in / out", r.usage ? `${fmt.int(r.usage.prompt_tokens)} / ${fmt.int(r.usage.completion_tokens)}` : "—"],
        ["Model group", r.headers.get("x-litellm-model-group") ?? "—"],
        ["Deployment", r.headers.get("x-litellm-model-id") ?? "—"],
        ["Retries / fallbacks", `${r.headers.get("x-litellm-attempted-retries") ?? 0} / ${r.headers.get("x-litellm-attempted-fallbacks") ?? 0}`],
      ]);
      if (!r.content) textEl.textContent = "(empty response)";
    } catch (err) {
      const aborted = err.name === "AbortError";
      // Keep what streamed so far in the history so the conversation stays coherent.
      if (textEl.textContent) history.push({ role: "assistant", content: textEl.textContent });
      else {
        out.remove();
        asked.remove();
        history.pop();
        prompt.value = text;
      }
      statRows([["Status", aborted ? "Stopped" : `Error ${err.status || ""}`.trim()], ["Latency", fmt.ms(performance.now() - started)]]);
      if (!aborted) mount(notice, errorBox(err));
    } finally {
      out.classList.remove("streaming");
      controller = null;
      send.disabled = false;
      stop.hidden = true;
      prompt.focus();
    }
  }

  const form = h("form", { class: "composer" }, prompt, h("div", { class: "row" }, h("span", { class: "grow" }, "Ctrl+Enter sends"), clear, stop, send));
  form.addEventListener("submit", submit);
  prompt.addEventListener("keydown", (e) => {
    if (e.key === "Enter" && (e.ctrlKey || e.metaKey)) submit(e);
  });
  stop.addEventListener("click", () => controller?.abort());
  clear.addEventListener("click", () => {
    controller?.abort();
    history = [];
    mount(transcript, h("p", { class: "placeholder" }, "Conversation cleared."));
    mount(notice);
  });
  onCleanup(() => controller?.abort());

  mount(main,
    pageHead("Playground", "Send chat completions through the gateway with your key: its budget, limits and model list apply."),
    h("div", { class: "playground" },
      h("section", { class: "card", "aria-label": "Chat" }, notice, transcript, form),
      h("aside", { class: "stack" },
        h("section", { class: "card", "aria-labelledby": "settings-h" },
          h("div", { class: "card-head" }, h("h2", { id: "settings-h" }, "Settings")),
          h("div", { class: "stack" },
            field("Model", model),
            h("label", { class: "check" }, stream, "Stream the response"),
            field("Temperature", temperature),
            field("Max tokens", maxTokens, "The budget reserves for this many completion tokens."),
            field("System prompt", system))),
        h("section", { class: "card", "aria-labelledby": "stats-h" },
          h("div", { class: "card-head" }, h("h2", { id: "stats-h" }, "Last call")),
          stats))));

  api("/v1/models")
    .then((r) => {
      const ids = r.data.map((m) => m.id).sort();
      if (!ids.length) {
        mount(model, h("option", { value: "" }, "No models available to this key"));
        return;
      }
      mount(model, ids.map((id) => h("option", { value: id }, id)));
      model.disabled = false;
    })
    .catch((err) => {
      mount(model, h("option", { value: "" }, "Could not load models"));
      mount(notice, errorBox(err));
    });
}
