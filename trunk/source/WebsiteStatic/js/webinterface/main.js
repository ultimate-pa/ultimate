/**
 * Fetches the backend "ultimate" version and displays it in the footer.
 * Retries until it succeeds
 */
function loadBackendVersion() {
  const url = _CONFIG.backend.web_bridge_url + '/version';
  const $el = $('#version_info_text');

  function tryFetch() {
    const delay = 10_000

    $el.html(`Connecting to backend...`).removeClass('text-danger').addClass('text-warning');

    $.get(url)
      .done(function(response) {
        try {
          $el.removeClass('text-warning text-danger').html('Ultimate version ' + response.ultimate_version);
        } catch (e) {
          $el.removeClass('text-warning').addClass('text-danger').html('Malformed backend response!');
          console.error(e);
          setTimeout(tryFetch, delay);
        }
      })
      .fail(function(jqXHR, textStatus, errorThrown) {
        $el.removeClass('text-warning').addClass('text-danger').html(`No connection to backend. Retrying in ${Math.round(delay / 1000)}s...`);
        console.error('Backend request failed:', textStatus, errorThrown);
        setTimeout(tryFetch, delay);
      });
  }

  tryFetch();
}


/**
 * Render the header/navigation-bar.
 */
function renderNavbar() {
  const navbarTemplate = Handlebars.compile($('#navbar_template').html());
  $('#navbar_content').append(navbarTemplate(_CONTEXT));
  $('#navbar_toggler').removeClass('d-none');

  $('#brand_title_text').text(_CONTEXT.tool.name);
  $('#brand_title').attr('href', _CONTEXT.tool.url);

  if (_CONTEXT.tool.name && _CONTEXT.tool.name.trim() !== '') {
    $('#brand_divider').removeClass('d-none');
  } else {
    $('#brand_divider').addClass('d-none');
  }
}

/**
 * Load the interactive tool interface.
 */
function loadToolInterface() {
  loadToolInterfaceTemplate();
  initEditor();
  initInterfaceControls();
  refreshNavbar();
  loadBackendVersion();
  setMessagesOrientation(_CONTEXT.msg_orientation);
  if (_CONTEXT.url.lang !== null) {
    chooseLanguage(_CONTEXT.url.lang).then(refreshNavbar);
  }
  if (_CONTEXT.url.sample !== null) {
    loadSample(_CONTEXT.url.sample);
  }
  if (_CONTEXT.url.session !== null) {
    loadUserProvidedSession(_CONTEXT.url.session);
  }
}

function getHomeUrl() {
  let url = new URL(window.location);
  let path = url.pathname;
  let leftSlash = path.lastIndexOf('/');
  url.pathname = path.substring(0, path.lastIndexOf('/', leftSlash - 1) + 1);
  url.search = '';
  return url;
}

/**
 * Inject the current context to _CONTEXT s.t:
 *
 * _CONTEXT = {
 *     url: {
 *         tool: <URL tool param>
 *     },
 *     tool: <CONFIG for tool with corresponding tool.id>,
 *     msg_orientation: _CONFIG.editor.default_msg_orientation
 * }
 */
let _CONTEXT;

function setContext() {
  const params = getUrlParams();
  let tool = {};

  // Load session if provided.
  if (params.session !== null) {
    try {
      params.session = URIDecompressArray(params.session);
      params.tool = params.session.tool;
    } catch (e) {
      alert('could not load Session provided. Malformed Link.');
      console.log(e);
    }
  }

  // Redirect non-existing tools to the home page.
  if (!(params.tool in _TOOLS)) {
    window.location.replace(getHomeUrl());
    return false;
  }

  // Set the current tool if active.
  tool = _TOOLS[params.tool];

  _CONTEXT = {
    'url': params,
    'tool': tool,
    'msg_orientation': _CONFIG.editor.default_msg_orientation,
    'sample_source': '',
  };
  return true;
}


function loadAvailableCodeSamples() {
  return $.getJSON('./code_examples/code_examples.json');
}


function bootstrap() {
  let proceed = setContext();
  if (!proceed) {
    return;
  }
  renderNavbar();

  // load the interactive mode for the active tool.
  loadAvailableCodeSamples().always(function(json) {
    _CONFIG.code_examples = json;
    loadToolInterface();
  });
}


$(function() {
  bootstrap();
});
