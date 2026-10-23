/**
 * Redirect old URLs based on query parameters ("?ui=...") to the proper URL.
 **/
function redirectLegacyUrls() {
  // Names of tools for which legacy URLs might exist. Do not modify for new tools.
  let tools = ['automata_library', 'automizer', 'buechi_automizer', 'eliminator', 'gemcutter', 'kojak', 'lasso_ranker', 'ltl_automizer', 'referee', 'taipan'];

  let url = new URL(window.location);
  let ui = url.searchParams.get('ui');

  // Determine the URL to which we should redirect.
  let target = undefined;
  let preserveParams = false;
  switch (ui) {
    case 'int':
      target = 'webinterface/';
      preserveParams = true;
      break;
    case 'tool':
      let tool = url.searchParams.get('tool');
      if (tools.indexOf(tool) >= 0) {
        target = tool + '/';
      } else {
        target = '';
      }
      break;
    case 'awards':
    case 'developers':
    case 'imprint':
      target = ui + '/';
      break;
    default:
      // no redirect necessary
      return;
  }

  url.pathname = url.pathname.substring(0, url.pathname.lastIndexOf('/') + 1) + target;
  if (preserveParams) {
    url.searchParams.delete('ui');
  } else {
    url.search = '';
  }
  window.location.replace(url);
}

$(function() {
  redirectLegacyUrls();
});
