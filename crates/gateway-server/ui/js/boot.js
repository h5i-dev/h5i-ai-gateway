// A classic script that runs before the modules: if the console fails to
// start (an old browser, a script error), say so instead of loading forever.
(function () {
  var started = false;
  function show(message) {
    if (started) return;
    var app = document.getElementById("app");
    if (!app) return;
    var box = document.createElement("div");
    box.className = "alert";
    box.setAttribute("role", "alert");
    box.textContent = "The admin console could not start: " + message;
    app.replaceChildren(box);
    app.removeAttribute("aria-busy");
  }
  window.addEventListener("error", function (e) {
    show(e.message || "a script failed to load");
  }, true);
  window.addEventListener("unhandledrejection", function (e) {
    show(String(e.reason && e.reason.message ? e.reason.message : e.reason));
  });
  window.__h5iStarted = function () {
    started = true;
  };
})();
