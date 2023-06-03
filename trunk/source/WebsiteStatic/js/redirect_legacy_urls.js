/**
 * Redirect old URLs based on query parameters ("?ui=...") to the proper URL.
 **/
function redirect_legacy_urls() {
  // Names of tools for which legacy URLs might exist. Do not modify for new tools.
  let known_tools = ["automata_library", "automizer", "buechi_automizer", "eliminator", "gemcutter", "kojak", "lasso_ranker", "ltl_automizer", "referee", "taipan"]

  let url = new URL(window.location);
  let ui = url.searchParams.get("ui");

  // Determine the URL to which we should redirect.
  let target = undefined;
  let preserve_params = false;
  switch (ui) {
    case "int":
      target = "webinterface/";
      preserve_params = true;
      break;
    case "tool":
      let tool = url.searchParams.get("tool");
      if (known_tools.indexOf(tool) >= 0) {
        target = "tools/" + tool + "/";
      } else {
        target = "";
      }
      break;
    case "awards":
    case "developers":
    case "imprint":
      target = ui + "/";
      break;
    default:
      // no redirect necessary
      return;
  }

  url.pathname = url.pathname.substring(0, url.pathname.lastIndexOf('/')+1) + target;  
  if (preserve_params) {
    url.searchParams.delete("ui");
  } else {
    url.search = "";
  }
  window.location.replace(url);
}

$(function () {
  redirect_legacy_urls();
});
