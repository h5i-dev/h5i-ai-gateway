// DOM helpers. Everything is built with createElement/textContent, never
// innerHTML, so names and messages from the API can never become markup.

const SVG_NS = "http://www.w3.org/2000/svg";

function apply(el, attrs) {
  for (const [k, v] of Object.entries(attrs || {})) {
    if (v === undefined || v === null || v === false) continue;
    if (k === "class") el.setAttribute("class", Array.isArray(v) ? v.filter(Boolean).join(" ") : v);
    else if (k === "dataset") Object.assign(el.dataset, v);
    else if (k.startsWith("on") && typeof v === "function") el.addEventListener(k.slice(2), v);
    else if (k === "checked" || k === "disabled" || k === "selected") {
      // Both the attribute (the initial state) and the property (the live one).
      el.setAttribute(k, "");
      el[k] = true;
    } else if (k === "value") {
      if (el.tagName === "INPUT" || el.tagName === "OPTION") el.setAttribute("value", String(v));
      el.value = v;
    }
    else el.setAttribute(k, v === true ? "" : String(v));
  }
}

function append(el, children) {
  for (const c of children.flat(Infinity)) {
    if (c === undefined || c === null || c === false) continue;
    el.append(c instanceof Node ? c : document.createTextNode(String(c)));
  }
}

/** An HTML element: h("button", {class: "primary", onclick}, "Save"). */
export function h(tag, attrs, ...children) {
  const el = document.createElement(tag);
  apply(el, attrs);
  append(el, children);
  return el;
}

/** An SVG element. */
export function s(tag, attrs, ...children) {
  const el = document.createElementNS(SVG_NS, tag);
  apply(el, attrs);
  append(el, children);
  return el;
}

/** Replace an element's children. */
export function mount(el, ...children) {
  el.replaceChildren();
  append(el, children);
  return el;
}

const ICONS = {
  dashboard: "M3 13h8V3H3zm10 8h8V11h-8zM3 21h8v-6H3zm10-18v6h8V3z",
  keys: "M7 14a4 4 0 1 1 3.87-5H21v3h-2v3h-3v-3h-5.13A4 4 0 0 1 7 14zm0-2a2 2 0 1 0 0-4 2 2 0 0 0 0 4z",
  teams: "M16 11a3 3 0 1 0 0-6 3 3 0 0 0 0 6zM8 11a3 3 0 1 0 0-6 3 3 0 0 0 0 6zm0 2c-2.7 0-8 1.3-8 4v3h16v-3c0-2.7-5.3-4-8-4zm8 0c-.3 0-.7 0-1.1.1 1.2.9 2.1 2.1 2.1 3.9v3h7v-3c0-2.7-5.3-4-8-4z",
  spend: "M4 20V10h3v10zm6.5 0V4h3v16zM17 20v-7h3v7z",
  playground: "M4 4h16v12H7l-3 3zm4 5h8V7H8zm0 4h5v-2H8z",
  account: "M12 12a4 4 0 1 0 0-8 4 4 0 0 0 0 8zm0 2c-2.7 0-8 1.3-8 4v2h16v-2c0-2.7-5.3-4-8-4z",
  theme: "M12 3a9 9 0 1 0 9 9 7 7 0 0 1-9-9z",
  logout: "M10 17l1.4-1.4-2.6-2.6H20v-2H8.8l2.6-2.6L10 7l-5 5zM4 5h7V3H4a2 2 0 0 0-2 2v14a2 2 0 0 0 2 2h7v-2H4z",
  copy: "M16 1H4a2 2 0 0 0-2 2v14h2V3h12zm3 4H8a2 2 0 0 0-2 2v14a2 2 0 0 0 2 2h11a2 2 0 0 0 2-2V7a2 2 0 0 0-2-2zm0 16H8V7h11z",
  refresh: "M17.6 6.4A8 8 0 1 0 19.7 14h-2.1a6 6 0 1 1-1.4-6.2L13 11h7V4z",
};

/** A decorative icon (hidden from assistive technology). */
export function icon(name) {
  return s("svg", { viewBox: "0 0 24 24", "aria-hidden": "true", focusable: "false", fill: "currentColor" }, s("path", { d: ICONS[name] || "" }));
}

/** A transient message in the corner, announced politely. */
export function toast(message, kind = "info") {
  const box = document.getElementById("toasts");
  const t = h("div", { class: ["toast", kind === "error" && "error"] }, message);
  box.append(t);
  setTimeout(() => t.remove(), kind === "error" ? 7000 : 3500);
}

/** An error, as the API reported it: message, then type and status. */
export function errorBox(err) {
  const meta = [err.type, err.status && `HTTP ${err.status}`].filter(Boolean).join(" · ");
  return h("div", { class: "alert", role: "alert" }, h("div", null, h("div", null, err.message || String(err)), meta && h("div", { class: "meta" }, meta)));
}

export function infoBox(...children) {
  return h("div", { class: "alert info", role: "note" }, h("div", null, ...children));
}

/** A button that copies `text` to the clipboard. */
export function copyButton(text, label = "Copy") {
  const b = h("button", { type: "button", class: "small" }, icon("copy"), label);
  b.addEventListener("click", async () => {
    try {
      await navigator.clipboard.writeText(text);
    } catch {
      // Clipboard API unavailable (plain HTTP on another host): fall back to a selection copy.
      const ta = h("textarea", { class: "visually-hidden" }, text);
      document.body.append(ta);
      ta.select();
      document.execCommand("copy");
      ta.remove();
    }
    b.lastChild.textContent = "Copied";
    toast("Copied to the clipboard");
    setTimeout(() => (b.lastChild.textContent = label), 2000);
  });
  return b;
}

/**
 * A modal dialog. `build(close)` returns the dialog's content; the dialog is
 * removed from the document when it closes. Resolves with the value passed
 * to `close`.
 */
export function dialog(title, build) {
  return new Promise((resolve) => {
    let result;
    const d = h("dialog", { "aria-labelledby": "dialog-title" });
    const close = (value) => {
      result = value;
      d.close();
    };
    d.addEventListener("close", () => {
      d.remove();
      resolve(result);
    });
    d.append(build(close, h("h2", { id: "dialog-title" }, title)));
    document.body.append(d);
    d.showModal();
  });
}

/** Ask before doing something irreversible. Resolves true to go ahead. */
export function confirm(title, message, action = "Delete") {
  return dialog(title, (close, heading) =>
    h("div", { class: "dialog-body" }, heading, h("p", null, message),
      h("div", { class: "dialog-actions" },
        h("button", { type: "button", onclick: () => close(false) }, "Cancel"),
        h("button", { type: "button", class: "danger solid", onclick: () => close(true) }, action))));
}

/** A labelled form field around `control` (which gets an id). */
export function field(label, control, help) {
  const id = control.id || `f-${Math.random().toString(36).slice(2, 9)}`;
  control.id = id;
  const helpEl = help && h("span", { class: "help", id: `${id}-help` }, help);
  if (helpEl) control.setAttribute("aria-describedby", helpEl.id);
  return h("div", { class: "field" }, h("label", { for: id }, label), control, helpEl);
}

/** A table: columns are {label, num?, cell(row) -> node|string}. */
export function table(columns, rows, { caption, empty = "Nothing here yet." } = {}) {
  if (!rows.length) return h("p", { class: "empty" }, empty);
  return h("div", { class: "table-wrap" },
    h("table", null,
      caption && h("caption", null, caption),
      h("thead", null, h("tr", null, columns.map((c) => h("th", { scope: "col", class: c.num && "num" }, c.label)))),
      h("tbody", null, rows.map((r) => h("tr", null, columns.map((c) => h("td", { class: [c.num && "num", c.class] }, c.cell(r))))))));
}

/** A status label: coloured shape plus text, never colour alone. */
export function status(kind, text) {
  return h("span", { class: ["status", kind] }, text);
}

/** Run `load` with the element dimmed (keeps the previous frame while refetching). */
export async function busy(el, load) {
  el.classList.add("is-loading");
  el.setAttribute("aria-busy", "true");
  try {
    return await load();
  } finally {
    el.classList.remove("is-loading");
    el.removeAttribute("aria-busy");
  }
}
