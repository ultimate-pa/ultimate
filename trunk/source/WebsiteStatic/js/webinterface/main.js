/**
 * Fetches the backend "ultimate" version and displays it in the settings menu.
 */
function load_backend_version() {
    $.get(_CONFIG.backend.web_bridge_url + "/version", function (response) {
        try {
            $('#version_info_text').html(
                "Ultimate version " + response.ultimate_version
            );
        } catch (e) {
            console.log("Could not read backend ultimate version.");
            console.log(e);
        }
    });
}


/**
 * Render the header/navigation-bar.
 */
function render_navbar() {
  const navbar_template = Handlebars.compile($("#navbar-template").html());
  $('#navbar_content').append(navbar_template(_CONTEXT));
  
  const navbar_breadcrumb_entry = $("#navbar_breadcrumb li a");
  navbar_breadcrumb_entry.text(_CONTEXT.tool.name);
  navbar_breadcrumb_entry.attr('href', _CONTEXT.tool.url);
}


/**
 * Load the interactive tool interface.
 * @param tool_id
 */
function load_tool_interface(tool_id) {
  load_tool_interface_template();
  init_editor();
  init_interface_controls();
  refresh_navbar();
  load_backend_version();
  set_message_orientation(_CONTEXT.msg_orientation);
  if (_CONTEXT.url.lang !== null) {
    choose_language(_CONTEXT.url.lang)
    .then(refresh_navbar);
  }
  if (_CONTEXT.url.sample !== null) {
    load_sample(_CONTEXT.url.sample);
  }
  if (_CONTEXT.url.session !== null) {
    load_user_provided_session(_CONTEXT.url.session);
  }
}

function get_home_url() {
  let url = new URL(window.location);
  let path = url.pathname;
  let last_slash = path.lastIndexOf('/');
  let prefix = path.substring(0, path.lastIndexOf('/', last_slash-1)+1);
  url.pathname = prefix;
  url.search = "";
  return url;
}

/**
 * Inject current context to _CONTEXT s.t:
 *
 * _CONTEXT = {
 *     url: {
 *         tool: <URL tool param>
 *     },
 *     tool: <CONFIG for tool with corresponding tool.id>,
 *     msg_orientation: _CONFIG.editor.default_msg_orientation
 * }
 */
var _CONTEXT;
function set_context() {
  const url_params = get_url_params();
  let tool = {};

  // Load session if provided.
  if (url_params.session !== null){
    try {
      url_params.session = URIDecompressArray(url_params.session);
      url_params.tool = url_params.session.tool;
    } catch (e) {
      alert('could not load Session provided. Malformed Link.');
      console.log(e);
    }
  }

  // Redirect non existing tools to home page.
  if (!(url_params.tool in _TOOLS)) {
    window.location.replace(get_home_url());
    return false;
  }

  // Set current tool if active.
  tool = _TOOLS[url_params.tool];

  _CONTEXT = {
    "url": url_params,
    "tool": tool,
    "msg_orientation": _CONFIG.editor.default_msg_orientation,
    "sample_source": ''
  }
  return true;
}


function load_available_code_examples() {
  return $.getJSON("./code_examples/code_examples.json");
}


function bootstrap() {
  let proceed = set_context();
  if (!proceed) {
    return;
  }
  render_navbar();

  // load the interactive mode for the active tool.
  load_available_code_examples().always(function (json) {
    _CONFIG.code_examples = json;
    load_tool_interface(_CONTEXT.tool.id);
  });
}


$(function () {
  bootstrap();
});
