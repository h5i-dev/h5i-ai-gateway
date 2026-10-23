// Sign in with the master key or a virtual key.

import { identify, session } from "../api.js";
import { errorBox, field, h, mount } from "../dom.js";

export function loginView({ onSignedIn, themeButton }) {
  const input = h("input", { type: "password", name: "key", autocomplete: "current-password", required: true, placeholder: "sk-…", spellcheck: "false" });
  const errors = h("div", { "aria-live": "assertive" });
  const submit = h("button", { type: "submit", class: "primary" }, "Sign in");
  const form = h("form", { class: "card", "aria-labelledby": "login-title" },
    h("div", { class: "brand" }, h("img", { src: document.querySelector("link[rel=icon]").href, alt: "" }), h("div", null, h("span", { id: "login-title" }, "h5i gateway admin"))),
    h("p", null, "Sign in with the master key or a virtual key. Admin keys manage keys, teams and spend; other keys see their own limits and can use the playground."),
    errors,
    field("API key", input, "Kept in this tab's session storage only, and sent as a Bearer token."),
    submit,
    h("div", null, themeButton()));
  form.addEventListener("submit", async (e) => {
    e.preventDefault();
    const key = input.value.trim();
    if (!key) return;
    submit.disabled = true;
    submit.textContent = "Signing in…";
    mount(errors);
    try {
      session.set(await identify(key));
      onSignedIn();
    } catch (err) {
      mount(errors, errorBox(err.status === 401 || err.status === 403 ? { ...err, message: `This key was not accepted: ${err.message}`, type: err.type, status: err.status } : err));
      submit.disabled = false;
      submit.textContent = "Sign in";
      input.focus();
    }
  });
  queueMicrotask(() => input.focus());
  return h("div", { class: "login" }, form);
}
