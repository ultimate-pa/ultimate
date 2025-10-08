let _EDITOR;
let _DECORATIONS = [];

/**
 * Load and add the editor template to the DOM.
 */
function loadToolInterfaceTemplate() {
  let content = $('#content');
  content.removeClass('p-5');
}

/**
 * Initialize the frontend editor.
 */
function initEditor() {
  require(['vs/editor/editor.main'], function() {
    // Register custom languages
    registerBoogieLanguage(monaco);
    registerSmtLanguage(monaco);
    registerAutomataScriptLanguage(monaco);

    // Create editor
    _EDITOR = monaco.editor.create(document.getElementById('editor'), {
      value: _CONFIG.editor.init_code || '',
      language: 'c',
      theme: 'vs-light',
      automaticLayout: true,
      minimap: { enabled: false },
      scrollBeyondLastLine: false,
      glyphMargin: false,
    });
  });
}


/**
 * Clear all messages and decorations.
 */
function clearMessages() {
  $('#messages_toasts').html('');
  $('#messages').hide();
  if (_EDITOR) { // remove all hints
    monaco.editor.setModelMarkers(_EDITOR.getModel(), 'owner', []);
    _DECORATIONS = _EDITOR.deltaDecorations(_DECORATIONS, []);
  }
}


/**
 * Reset editor content.
 */
function clearEditor() {
  clearMessages();
  if (_EDITOR) _EDITOR.setValue(_CONFIG.editor.init_code);
}

/**
 * Create a link which can recreate the current session.
 * Open a modal to display the result to the user.
 */
function createPersistenceLink() {
  let modal = $('#persistence_link_modal');
  let linkInput = $('#persistence_link_input');
  let linkInputSmall = $('#persistence_link_small_input');

  modal.modal('show');
  let session_data = getUserSessionSettings();
  linkInput.val(window.location.origin + window.location.pathname
    + '?session=' + URICompressArray(session_data));

  delete session_data.code;
  linkInputSmall.val(window.location.origin + window.location.pathname
    + '?ui=int&tool=' + _CONTEXT.tool.id + '&lang=' + _CONTEXT.current_worker.language
    + '&sample=' + _CONTEXT.sample_source,
  );

  $('#copy_persistence_link_to_clipboard').on({
    click: function() {
      copyToClipboard(linkInput);
    },
  });

  $('#copy_persistence_link_small_to_clipboard').on({
    click: function() {
      copyToClipboard(linkInputSmall);
    },
  });
}


/**
 * Create a session object of the current frontend state.
 * To be consumed by `loadUserProvidedSession(user_session_settings)` to recreate the session.
 * @returns {{code: *, frontend_settings: *, language: *, worker: *, tool: *, sample_source: *}}
 */
function getUserSessionSettings() {
  let frontendSettings = getUserFrontendSettings();
  // Reduce the size of the frontend settings object to only necessary info needed for recreation.
  frontendSettings = frontendSettings.map(function(setting) {
    return {
      'id': setting.id,
      'type': setting.type,
      'value': setting.value,
    };
  });

  return {
    'tool': _CONTEXT.tool.id,
    'worker': _CONTEXT.current_worker.id,
    'language': _CONTEXT.current_worker.language,
    'frontend_settings': frontendSettings,
    'sample_source': _CONTEXT.sample_source,
    'code': _EDITOR.getValue(),
  };
}


/**
 * Synchronize the user-definable frontend settings
 * with an array of setting objects as returned by getUserFrontendSettings.
 * @param settings
 */
function setUserFrontendSettings(settings) {
  settings.forEach(function(setting) {
    if (setting.type === 'bool') {
      $('#' + setting.id).prop('checked', setting.value);
    } else if (setting.type === 'string') {
      $('#' + setting.id).prop('value', setting.value);
    } else if (setting.type === 'int') {
      $('#' + setting.id).prop('value', setting.value);
    } else {
      console.warn('skipping setting: ' + setting.id + ' (unsupported settings type ' + setting.type + ')');
      console.debug(setting);
    }
  });
}


/**
 * Recreates a session.
 * @param sessionSettings
 */
function loadUserProvidedSession(sessionSettings) {
  chooseLanguage(sessionSettings.language)
    .then(function() {
      if ('code' in sessionSettings) {
        _EDITOR.setValue(sessionSettings.code);
      }
      refreshNavbar();
      setUserFrontendSettings(sessionSettings.frontend_settings);
      if (!('code' in sessionSettings)) {
        loadSample(sessionSettings.sample_source);
      }
    });
}

/**
 * Bind the user control buttons to process events.
 */
function initInterfaceControls() {
  // Changing the tool Language.
  $('.language-selection').on({
    click: function() {
      let language = $(this).data().language;
      // is editor clearing wanted?
      //if (language !== getCurrentLanguage()) {
      //  clearEditor();
      //}
      chooseLanguage(language)
        .then(refreshNavbar);
    },
  });

  // Handle click on "Execute"
  $('#navbar_execute_interface').on({
    click: function() {
      clearMessages();
      try {
        const settings = getExecuteSettings();
        runUltimateTask(settings);
      } catch (e) {
        alert('Could not execute Ultimate: ' + e.message);
        console.log(e);
      }
    },
  });

  // Handle click on "Cancel run!"
  $('#navbar_cancel_interface').on({
    click: function() {
      clearMessages();
      try {
        setCancelSpinner(true);
        stopUltimateToolchainJob(localStorage.getItem('requestId'));
      } catch (e) {
        alert('Could not cancel Ultimate: ' + e.message);
        console.log(e);
        setExecuteSpinner(false);
      }
    },
  });

  // Highlight code by message click.
  $(document).on({
    click: function() {
      let data = $(this).data();
      jumpToLine(data.startLine);
    },
  }, '.toast');

  // Resizable Message container.
  initMessagesResize();

  $('#move_messages').on({
    click: function() {
      switch (_CONTEXT.msg_orientation) {
        case 'left':
          setMessagesOrientation('bottom');
          break;
        case 'bottom':
          setMessagesOrientation('left');
          break;
      }
    },
  });

  // Let the user create a sharable link encoding the current session.
  $('#create_persistence_link').on({
    click: function() {
      createPersistenceLink();
    },
  });

  // Handle save button for modal settings.
  $('#save_settings_btn').on('click', function() {
    const updatedSettings = getUserFrontendSettings();

    // Persist the new values
    _CONTEXT.current_worker.frontend_settings.forEach(setting => {
      const updated = updatedSettings.find(s => s.id === setting.id);
      if (updated) setting.value = updated.value;
    });

    // Clear unsaved markers
    $('#settings_modal_body .setting-unsaved').removeClass('setting-unsaved');

    console.log('User saved settings:', _CONTEXT.current_worker.frontend_settings);
    $('#settings_modal').modal('hide');
  });


  // Add search functionality after settings are rendered
  $('#settings_search').off('input').on('input', function() {
    const query = $(this).val().trim().toLowerCase();

    $('#settings_modal_body .setting-entry').each(function() {
      const entry = $(this);
      const textContent = entry.text().toLowerCase();
      const inputVal = entry.find('input, select').val()?.toString().toLowerCase() || '';

      // Reset highlights
      entry.find('label').each(function() {
        clearHighlights($(this));
      });

      if (!query) {
        if (entry.data('visible') === false) {
          entry.addClass('d-none');
        } else {
          entry.removeClass('d-none');
        }
        return;
      }

      // Apply search filter
      const showExpert = $('#toggle_expert_settings').is(':checked');

      if ((textContent.includes(query) || inputVal.includes(query)) && entry.data('visible') !== false && (entry.data('level') !== 'EXPERT' || showExpert)) {
        entry.removeClass('d-none');
        entry.find('label').each(function() {
          highlightText($(this), query);
        });
      } else {
        entry.addClass('d-none');
      }
    });

    updateEmptyMessage();
  });
}


/**
 * Initialize the resizing feature for the message column.
 */
function initMessagesResize() {
  let messagesContainer = $('#messages');
  let edges = { left: false, right: false, bottom: false, top: false };
  switch (_CONTEXT.msg_orientation) {
    case 'bottom':
      edges.top = true;
      break;
    case 'left':
      edges.left = true;
      break;
  }

  function setFlexBasis(event) {
    switch (_CONTEXT.msg_orientation) {
      case 'bottom':
        return event.rect.height;
      case 'left':
        return event.rect.width;
    }
  }

  interact('#messages')
    .resizable({
      edges: edges,
    })
    .on('resizemove', function(event) {
      messagesContainer.css('flex-basis', setFlexBasis(event) + 'px');
      if (_EDITOR) _EDITOR.layout();
    });

}


/**
 * Move the message column to "bottom" or "left".
 * @param new_orientation
 */
function setMessagesOrientation(new_orientation) {
  let content = $('#content');
  let moveMsgAction = $('#move_messages');
  content.removeClass('flex-row flex-column');

  $('#messages').css('visibility', 'visible');

  switch (new_orientation) {
    case 'left':
      content.addClass('flex-row');
      moveMsgAction.removeClass('oi-collapse-right oi-collapse-down');
      moveMsgAction.addClass('oi-collapse-down');
      break;
    case 'bottom':
      content.addClass('flex-column');
      moveMsgAction.removeClass('oi-collapse-right oi-collapse-down');
      moveMsgAction.addClass('oi-collapse-right');
      break;
  }
  _CONTEXT.msg_orientation = new_orientation;
  initMessagesResize();
  if (_EDITOR) _EDITOR.layout();
}


/**
 * Set available options for the navbar based on _CONTEXT
 */
function refreshNavbar() {
  if ('current_worker' in _CONTEXT) {
    $('#navbar_language_select_dropdown').html('Language: ' + _CONTEXT.current_worker.display);

    setAvailableCodeSamples(_CONTEXT.current_worker.id);
    setAvailableFrontendSettings();

    $('#navbar_sample_select_dropdown').removeClass('disable');
    $('#editor').removeClass('disable');
    $('#create_persistence_link').removeClass('disable');
    $('#navbar_execute_interface').removeClass('disable');
    $('#navbar_settings_button').removeClass('disable');
  } else {
    $('#navbar_sample_select_dropdown').addClass('disable');
    $('#editor').addClass('disable');
    $('#create_persistence_link').addClass('disable');
    $('#navbar_execute_interface').addClass('disable');
    $('#navbar_settings_button').addClass('disable');
  }
}

/**
 * Convert a response to a Monaco marker.
 */
function getMarkerFromMessage(message) {
  let severity;
  switch (message.logLvl) {
    case 'error':
      severity = monaco.MarkerSeverity.Error;
      break;
    case 'warning':
      severity = monaco.MarkerSeverity.Warning;
      break;
    case 'info':
      severity = monaco.MarkerSeverity.Info;
      break;
    default:
      severity = monaco.MarkerSeverity.Info;
  }

  return {
    startLineNumber: message.startLNr,
    startColumn: message.startCol + 1,
    endLineNumber: message.endLNr,
    endColumn: message.endCol + 1,
    message: message.shortDesc,
    severity: severity,
  };
}


/**
 * Process ultimate web bridge results and add them as toasts to the editor interface.
 * @param result
 */
function addResultsToEditor(result) {
  if (!_EDITOR) return;

  let messagesContainer = $('#messages_toasts');
  const editorMessageTemplate = Handlebars.compile($('#editor_message').html());

  if ('error' in result) {
    alert(result.error);
  }

  const markers = [];

  for (let key in result.results) {
    const message = result.results[key];

    // Create marker for underlining
    markers.push(getMarkerFromMessage(message));

    switch (message.logLvl) {
      case 'error':
        message.toast_classes = 'border border-danger';
        message.oi_icon = 'oi-circle-x text-danger';
        break;
      case 'warning':
        message.toast_classes = 'border border-warning';
        message.oi_icon = 'oi-warning text-warning';
        break;
      case 'info':
        message.toast_classes = 'border border-info';
        message.oi_icon = 'oi-info text-info';
        break;
    }

    messagesContainer.append(editorMessageTemplate(message));
  }

  // Set all markers
  monaco.editor.setModelMarkers(_EDITOR.getModel(), 'owner', markers);

  // Fade in results
  $('#messages').fadeIn(500);
  $('.toast').toast('show');
}


/**
 * Poll running job for results every 3 seconds.
 * Polling stops once there are results.
 */
function pollResults() {
  $.get(_CONFIG.backend.web_bridge_url + '/job/get/' + localStorage.getItem('requestId'), function(response) {
    switch (response.status.toLowerCase()) {
      case 'done':
        addResultsToEditor(response);
        setExecuteSpinner(false);
        break;
      case 'error':
        alert('Backend error: ' + response.msg);
        console.log(response);
        break;
      default:
        // wait for 3s until something useful happens
        setTimeout(pollResults, 3000);
        break;
    }
  });
}

/**
 * Stops a running toolchain job.
 * @param job_jd
 */
function stopUltimateToolchainJob(job_jd) {
  $.get(_CONFIG.backend.web_bridge_url + '/job/delete/' + job_jd, function(response) {});
}

/**
 * Initiate a ultimate run and process the result.
 * @param settings
 */
function runUltimateTask(settings) {
  setExecuteSpinner(true);

  if (_CONFIG.meta.debug_mode) {
    $.get('./test/result.json', function(response) {
      addResultsToEditor(response);
    }).fail(function() {
      alert('Could not fetch results. Server error.');
    }).always(function() {
      setExecuteSpinner(false);
    });
    return;
  }

  $.post(_CONFIG.backend.web_bridge_url, settings, function(response) {
    localStorage.setItem('requestId', response.requestId);
    localStorage.setItem('pollingActive', '1');
    pollResults();
  }).fail(function() {
    alert('Could not initiate run. Server error.');
    setExecuteSpinner(false);
  });
}


/**
 * Get current state of the user defined settings as a list of setting objects.
 * @returns {[]}
 */
function getUserFrontendSettings() {
  let result = [];
  _CONTEXT.current_worker.frontend_settings.forEach(function(setting) {
    // note: our setting.id contain dots, which have to be escaped
    let settingInput = $('[id="' + setting.id + '"]');
    switch (setting['type']) {
      case 'bool':
        setting['value'] = settingInput.is(':checked');
        break;
      case 'int':
      case 'string':
      default:
        setting['value'] = settingInput.val();
        break;
    }
    result.push(setting);
  });

  return result;
}

/**
 * Get the current settings Dict to be used as a new job for ultimate.
 * @returns {{user_settings: {}, code: string, action: string, toolchain: {id: *}}}
 */
function getExecuteSettings() {
  let settings = {
    action: 'execute',
    code: _EDITOR.getValue(),
    toolchain: {
      id: _CONTEXT.current_worker.id,
    },
    code_file_extension: _CONFIG.code_file_extensions[_CONTEXT.current_worker.language],
    user_settings: '',
    ultimate_toolchain_xml: (new XMLSerializer()).serializeToString(_CONTEXT.current_worker.ultimate_toolchain_xml),
  };

  const userSettings = getUserFrontendSettings();
  settings.user_settings = JSON.stringify({ user_settings: userSettings });
  return settings;
}


/**
 * Process a language selection.
 * @param language
 */
function chooseLanguage(language) {
  _CONTEXT.tool.languages.forEach(function(lang) {
    if (lang.language === language) {
      _CONTEXT.current_worker = { 'language': language, 'id': lang.worker, 'display': lang.display };
    }
  });

  // Load the frontend settings for the worker.
  const settingsRequest = $.getJSON('./workers/' + _CONTEXT.current_worker.id + '.json', function(response) {
    _CONTEXT.current_worker['frontend_settings'] = response;
  }).fail(function() {
    alert('Could not fetch ultimate settings json. Config error.');
  });

  // Load the ultimate toolchain file.
  const toolchainRequest = $.get('./workers/' + _CONTEXT.current_worker.id + '.xml', function(response) {
    _CONTEXT.current_worker.ultimate_toolchain_xml = response;
  }).fail(function() {
    alert('Could not fetch ultimate toolchain xml. Config error.');
  });

  if (_EDITOR) {
    let monacoLang = toMonacoLanguage(language);
    monaco.editor.setModelLanguage(_EDITOR.getModel(), monacoLang);
  }

  return $.when(settingsRequest, toolchainRequest);
}


function toMonacoLanguage(language) {
  const map = {
    Boogie: 'boogie',
    C: 'c',
    Smt: 'smt',
    automata_script: 'automata_script',
  };
  return map[language] || 'plaintext';
}

/**
 * Jump to a line in the editor.
 * @param line
 */
function jumpToLine(line) {
  if (!_EDITOR || line < 0) return;

  // Scroll into view
  _EDITOR.revealLineInCenter(line);
}

/**
 * Set available code samples to the dropdown.
 * This is adding each example associated to the worker id. This association originates from the build_examples.py
 * @param workerId
 */
function setAvailableCodeSamples(workerId) {
  let samplesMenu = $('#code_sample_dropdown_menu');
  let exampleEntries = '';

  try {
    _CONFIG.code_examples[workerId].forEach(function(example) {
      exampleEntries += '<a class="dropdown-item sample-selection" href="#" data-source="' +
        workerId + '/' + example.source + '">' + example.name + '</a>';
    });
  } catch (e) {
    console.log('Could set code examples:');
    console.log(e);
  }

  if (exampleEntries.length > 0) {
    $('#navbar_sample_select_dropdown').removeClass('disable');
  }
  samplesMenu.html(exampleEntries);
  $('.sample-selection').on({
    click: function() {
      loadSample($(this).data().source);
    },
  });
}


/**
 * Load an available sample into the editor.
 * @param source
 */
function loadSample(source) {
  $.get('./code_examples/' + source, function(data) {
    clearMessages();
    _EDITOR.setValue(data);
    _CONTEXT.sample_source = source;
  });
}


/**
 * Set the available options for the settings dropdown menu based on the current config.
 */
function setAvailableFrontendSettings() {
  let settingsMenu = $('#settings_modal_body');

  const template = Handlebars.compile($('#settings_template').html());
  const html = template({ settings: _CONTEXT.current_worker.frontend_settings });

  settingsMenu.html(html);
  updateEmptyMessage();

  bindSettingsEvents();
}

function bindSettingsEvents() {
  // Highlight unsaved changes
  $('#settings_modal_body input, #settings_modal_body select').on('input change', function() {
    const settingId = $(this).attr('id');
    const savedSetting = _CONTEXT.current_worker.frontend_settings.find(s => s.id === settingId);
    let newValue = ($(this).attr('type') === 'checkbox') ? $(this).is(':checked') : $(this).val();

    if (String(newValue) !== String(savedSetting.value ?? savedSetting.default)) {
      $(this).addClass('setting-unsaved');
      $(this).siblings('label').addClass('setting-unsaved');
    } else {
      $(this).removeClass('setting-unsaved');
      $(this).siblings('label').removeClass('setting-unsaved');
    }
  });

  // Expert toggle
  $('#toggle_expert_settings').off('change').on('change', function() {
    if ($(this).is(':checked')) {
      $('[data-level="EXPERT"]').each(function() {
        if ($(this).data('visible') !== false) {
          $(this).removeClass('d-none');
        }
      });
    } else {
      $('[data-level="EXPERT"]').addClass('d-none');
    }

    updateEmptyMessage();
  });
}

function updateEmptyMessage() {
  const visibleCount = $('#settings_modal_body .setting-entry').filter(function() {
    return !$(this).hasClass('d-none');
  }).length;

  if (visibleCount === 0) {
    $('#settings_empty_message').removeClass('d-none');
  } else {
    $('#settings_empty_message').addClass('d-none');
  }
}

function highlightText(element, query) {
  const span = element.find('.setting-label-text');
  if (!span.length) return;

  const regex = new RegExp(`(${query})`, 'gi');
  const text = span.text();
  span.html(text.replace(regex, '<span class="setting-highlight">$1</span>'));
}

function clearHighlights(element) {
  const span = element.find('.setting-label-text');
  if (!span.length) return;

  span.html(span.text());
}

/**
 * Set (active == true) or unset the spinner indicating the results are being fetched.
 * @param active
 */
function setExecuteSpinner(active) {
  const execBtn = $('#navbar_execute_interface');
  const cancelItem = $('#navbar_cancel_item');

  if (active) {
    cancelItem.removeClass('d-none');
    execBtn.html('<span class="spinner-border spinner-border-sm text-primary" role="status" aria-hidden="true"></span> Running ...');
  } else {
    cancelItem.addClass('d-none');
    execBtn.html('<span class="oi oi-play-circle align-middle"></span> Execute');
    setCancelSpinner(false);
  }
}

function setCancelSpinner(active) {
  const execBtn = $('#navbar_execute_interface');
  const cancelBtn = $('#navbar_cancel_interface');

  if (active) {
    execBtn.addClass('disable');
    cancelBtn.html('<span class="spinner-border spinner-border-sm text-primary" role="status" aria-hidden="true"></span> Canceling ...');
  } else {
    execBtn.removeClass('disable');
    cancelBtn.html('Cancel Execute');
  }
}
