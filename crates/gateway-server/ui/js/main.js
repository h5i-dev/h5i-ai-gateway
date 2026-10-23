// The console's shell: sign-in, navigation, theme, and the router. Routes
// are real paths under /ui (the server answers the page for any of them).

import { session, setUnauthorizedHandler } from "./api.js";
import { h, icon, mount, toast } from "./dom.js";
import { loginView } from "./views/login.js";
import { dashboardView } from "./views/dashboard.js";
import { keysView } from "./views/keys.js";
import { teamsView } from "./views/teams.js";
import { spendView } from "./views/spend.js";
import { playgroundView } from "./views/playground.js";
import { accountView } from "./views/account.js";

const BASE = "/ui";

const ROUTES = [
  { path: "/", title: "Dashboard", icon: "dashboard", view: dashboardView, admin: true },
  { path: "/keys", title: "Keys", icon: "keys", view: keysView, admin: true },
  { path: "/teams", title: "Teams", icon: "teams", view: teamsView, admin: true },
  { path: "/spend", title: "Spend", icon: "spend", view: spendView, admin: true },
  { path: "/account", title: "My key", icon: "account", view: accountView, admin: false },
  { path: "/playground", title: "Playground", icon: "playground", view: playgroundView },
];

const isAdmin = (s) => s && (s.role === "master" || s.role === "admin");
const routesFor = (s) => ROUTES.filter((r) => r.admin === undefined || r.admin === isAdmin(s));

// ---------------------------------------------------------------- theme

const THEMES = ["system", "light", "dark"];
function applyTheme(t) {
  if (t === "system") document.documentElement.removeAttribute("data-theme");
  else document.documentElement.dataset.theme = t;
}
function currentTheme() {
  const t = localStorage.getItem("h5i-gateway.theme");
  return THEMES.includes(t) ? t : "system";
}
applyTheme(currentTheme());

function themeButton() {
  const label = () => `Theme: ${currentTheme()}`;
  const text = h("span", { class: "btn-label" }, label());
  const b = h("button", { type: "button", class: "small ghost", title: "Switch between system, light and dark themes", "aria-label": label() }, icon("theme"), text);
  b.addEventListener("click", () => {
    const next = THEMES[(THEMES.indexOf(currentTheme()) + 1) % THEMES.length];
    localStorage.setItem("h5i-gateway.theme", next);
    applyTheme(next);
    text.textContent = label();
    b.setAttribute("aria-label", label());
  });
  return b;
}

// ---------------------------------------------------------------- routing

function currentPath() {
  let p = location.pathname.startsWith(BASE) ? location.pathname.slice(BASE.length) : "/";
  if (p === "" || p === "/") return "/";
  return p.replace(/\/+$/, "");
}

export function navigate(path, { replace = false } = {}) {
  const url = BASE + (path === "/" ? "/" : path);
  if (replace) history.replaceState(null, "", url);
  else history.pushState(null, "", url);
  render();
}

let teardown = null;

function signOut(message) {
  session.clear();
  if (message) toast(message, "error");
  navigate("/", { replace: true });
}

setUnauthorizedHandler((err) => {
  if (session.get()) signOut(`Signed out: ${err.message}`);
});

function sidebar(s, active) {
  const who =
    s.role === "master"
      ? h("span", null, "Signed in with the ", h("strong", null, "master key"))
      : h("span", null, `Key #${s.info?.token_id ?? "?"}`, " · ", h("strong", null, s.role === "admin" ? "admin" : "user"));
  return h("nav", { class: "sidebar", "aria-label": "Main" },
    h("div", { class: "brand" }, h("img", { src: document.querySelector("link[rel=icon]").href, alt: "" }), h("div", null, "h5i gateway", h("small", null, "admin console"))),
    h("div", { class: "nav" },
      routesFor(s).map((r) =>
        h("a", { href: BASE + (r.path === "/" ? "/" : r.path), "aria-current": r === active ? "page" : undefined, "data-link": "" }, icon(r.icon), h("span", null, r.title)))),
    h("div", { class: "sidebar-foot" },
      h("div", { class: "who" }, who),
      themeButton(),
      h("button", { type: "button", class: "small ghost", "aria-label": "Sign out", onclick: () => signOut() }, icon("logout"), h("span", { class: "btn-label" }, "Sign out"))));
}

function render() {
  if (teardown) {
    teardown();
    teardown = null;
  }
  document.getElementById("tooltip").hidden = true;
  const app = document.getElementById("app");
  app.removeAttribute("aria-busy");
  const s = session.get();
  if (!s) {
    document.title = "Sign in · h5i gateway";
    mount(app, loginView({ onSignedIn: () => navigate(currentPath(), { replace: true }), themeButton }));
    return;
  }
  const routes = routesFor(s);
  const path = currentPath();
  const route = routes.find((r) => r.path === path);
  if (!route) {
    // Unknown, or not for this kind of key: go to the first page it has.
    navigate(routes[0].path, { replace: true });
    return;
  }
  document.title = `${route.title} · h5i gateway`;
  const main = h("main", { id: "main", tabindex: "-1" });
  mount(app, h("div", { class: "shell" }, sidebar(s, route), main));
  const ctx = { session: s, navigate, onCleanup: (f) => (teardown = f) };
  route.view(main, ctx);
}

document.addEventListener("click", (e) => {
  const a = e.target.closest("a[data-link]");
  if (!a || e.metaKey || e.ctrlKey || e.shiftKey || e.button !== 0) return;
  e.preventDefault();
  const path = a.getAttribute("href").slice(BASE.length) || "/";
  navigate(path);
  document.getElementById("main")?.focus({ preventScroll: true });
});
window.addEventListener("popstate", render);

render();
window.__h5iStarted?.();
