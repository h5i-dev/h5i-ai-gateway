// The management API client. The key the operator signs in with lives in
// sessionStorage (gone when the tab closes) and goes in `Authorization`.

const STORAGE = "h5i-gateway.session";

/** An error in OpenAI's shape: `{"error": {"message", "type", "code"}}`. */
export class ApiError extends Error {
  constructor(status, message, type) {
    super(message);
    this.status = status;
    this.type = type;
  }
}

export const session = {
  /** {key, role: "master" | "admin" | "user", info} or null. */
  get() {
    try {
      return JSON.parse(sessionStorage.getItem(STORAGE));
    } catch {
      return null;
    }
  },
  set(s) {
    sessionStorage.setItem(STORAGE, JSON.stringify(s));
  },
  clear() {
    sessionStorage.removeItem(STORAGE);
  },
};

function headers(key, json) {
  const h = { Authorization: `Bearer ${key}` };
  if (json) h["Content-Type"] = "application/json";
  return h;
}

async function errorFrom(resp) {
  let message = `${resp.status} ${resp.statusText}`;
  let type;
  try {
    const body = await resp.json();
    const e = body && body.error;
    if (e && typeof e === "object") {
      message = e.message || message;
      type = e.type;
    } else if (typeof e === "string") {
      // Authentication failures arrive as {"error": "..."}.
      message = e;
      type = resp.status === 401 ? "auth_error" : undefined;
    } else if (typeof body?.detail === "string") {
      message = body.detail;
    }
  } catch {
    // Not JSON: keep the status line.
  }
  return new ApiError(resp.status, message, type);
}

/** When a call answers 401, the session is no longer valid. */
let onUnauthorized = () => {};
export function setUnauthorizedHandler(f) {
  onUnauthorized = f;
}

/**
 * Call the API. `query` values that are empty are left out.
 * Resolves with the parsed JSON; rejects with an ApiError.
 */
export async function api(path, { method = "GET", body, query, key, signal } = {}) {
  const k = key ?? session.get()?.key;
  const params = new URLSearchParams();
  for (const [name, v] of Object.entries(query || {})) {
    if (v !== undefined && v !== null && v !== "") params.set(name, v);
  }
  const qs = params.toString();
  const url = qs ? `${path}?${qs}` : path;
  let resp;
  try {
    resp = await fetch(url, { method, headers: headers(k, body !== undefined), body: body === undefined ? undefined : JSON.stringify(body), signal });
  } catch (e) {
    if (e.name === "AbortError") throw e;
    throw new ApiError(0, `Cannot reach the gateway: ${e.message}`, "network_error");
  }
  if (!resp.ok) {
    const err = await errorFrom(resp);
    if (resp.status === 401 && key === undefined) onUnauthorized(err);
    throw err;
  }
  const text = await resp.text();
  return text ? JSON.parse(text) : null;
}

export const post = (path, body) => api(path, { method: "POST", body });

/**
 * Work out who a key is: the master key, an admin key, or an ordinary key.
 * Rejects with an ApiError if the gateway does not accept it.
 */
export async function identify(key) {
  try {
    const r = await api("/key/info", { key });
    return { key, role: r.info.user_role === "proxy_admin" ? "admin" : "user", info: r.info };
  } catch (e) {
    // `/key/info` without `?key=` is the one call the master key cannot make.
    if (e.status === 400) {
      await api("/global/spend", { key });
      return { key, role: "master", info: null };
    }
    throw e;
  }
}

/**
 * A chat completion. With `stream`, parses the server-sent events and calls
 * `onDelta(text)` for each piece of content. Resolves with
 * {headers, status, content, usage, finishReason, firstTokenMs}.
 */
export async function chat(body, { onDelta = () => {}, signal } = {}) {
  const started = performance.now();
  let resp;
  try {
    resp = await fetch("/v1/chat/completions", {
      method: "POST",
      headers: headers(session.get()?.key, true),
      body: JSON.stringify(body),
      signal,
    });
  } catch (e) {
    if (e.name === "AbortError") throw e;
    throw new ApiError(0, `Cannot reach the gateway: ${e.message}`, "network_error");
  }
  if (!resp.ok) throw await errorFrom(resp);
  const out = { headers: resp.headers, status: resp.status, content: "", usage: null, finishReason: null, firstTokenMs: null };
  if (!body.stream) {
    const json = await resp.json();
    const choice = json.choices?.[0];
    out.content = choice?.message?.content ?? "";
    out.finishReason = choice?.finish_reason ?? null;
    out.usage = json.usage ?? null;
    out.firstTokenMs = performance.now() - started;
    onDelta(out.content);
    return out;
  }
  // One server-sent event: its `data:` lines are a chunk, an error, or [DONE].
  const handle = (event) => {
    const data = event
      .split(/\r?\n/)
      .filter((l) => l.startsWith("data:"))
      .map((l) => l.slice(5).replace(/^ /, ""))
      .join("\n");
    if (!data || data === "[DONE]") return;
    const chunk = JSON.parse(data);
    if (chunk.error) throw new ApiError(0, chunk.error.message || "The stream failed", chunk.error.type);
    if (chunk.usage) out.usage = chunk.usage;
    for (const c of chunk.choices || []) {
      if (c.finish_reason) out.finishReason = c.finish_reason;
      const piece = c.delta?.content;
      if (piece) {
        if (out.firstTokenMs === null) out.firstTokenMs = performance.now() - started;
        out.content += piece;
        onDelta(piece);
      }
    }
  };
  const separator = /\r?\n\r?\n/;
  if (!resp.body?.getReader) {
    // No streaming bodies in this browser: parse the events once they have all arrived.
    for (const event of (await resp.text()).split(separator)) handle(event);
    return out;
  }
  const reader = resp.body.getReader();
  const decoder = new TextDecoder();
  let buffer = "";
  for (;;) {
    const { value, done } = await reader.read();
    if (done) break;
    buffer += decoder.decode(value, { stream: true });
    const events = buffer.split(separator);
    // The last piece may be an event still arriving.
    buffer = events.pop();
    for (const event of events) handle(event);
  }
  handle(buffer + decoder.decode());
  return out;
}
