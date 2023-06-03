let _EDITOR;
let Range = ace.require('ace/range').Range;


/**
 * Load an add the editor template to the DOM.
 */
function load_tool_interface_template() {
	let content = $('#content');
	content.removeClass('p-5');
	const tool_interface_template = Handlebars.compile($("#tool-interface-template").html());
	content.append(tool_interface_template(_CONFIG));
}


/**
 * Initialize the frontend editor.
 */
function init_editor() {
	_EDITOR = ace.edit("editor");
	_EDITOR.renderer.setHScrollBarAlwaysVisible(false);
	_EDITOR.setTheme("ace/theme/eclipse");
	_EDITOR.getSession().setMode('ace/mode/c_cpp'); //equv to: changeMode('c_cpp');
	_EDITOR.renderer.setShowGutter(true);
	_EDITOR.setShowPrintMargin(true);
	_EDITOR.setDisplayIndentGuides(true);
	_EDITOR.setHighlightSelectedWord(true);
	_EDITOR.setPrintMarginColumn(80);

	_EDITOR.session.setValue(_CONFIG.editor.init_code);
	_EDITOR.session.setTabSize(4);
	_EDITOR.session.setUseWrapMode(true);
	_EDITOR.on("gutterclick", process_gutter_click);
}


/**
 * Remove all messages from the results.
 */
function clear_messages() {
	let messages_container = $('#messages-toasts');
	messages_container.html('');
	_EDITOR.getSession().clearAnnotations();
}


/**
 * Truncate the editor.
 */
function clear_editor() {
	clear_messages();
	_EDITOR.session.setValue(_CONFIG.editor.init_code);
}


/**
 * Create a link which can recreate the current session.
 * Open a modal to display the result to the user.
 */
function create_persistence_link() {
	let modal = $('#persistence_link_modal');
	let link_input = $('#persistence_link_input');
	let link_input_small = $('#persistence_link_small_input');

	modal.modal('show');
	let session_data = get_user_session_settings();
	link_input.val(window.location.origin + window.location.pathname
		+ '?session=' + URICompressArray(session_data));

	delete session_data.code;
	link_input_small.val(window.location.origin + window.location.pathname
		+ '?ui=int&tool=' + _CONFIG.context.tool.id + '&lang=' + _CONFIG.context.current_worker.language
		+ '&sample=' + _CONFIG.context.sample_source
	);

	$('#copy_persistence_link_to_clipboard').on({
		click: function() {
			copy_to_clipboard(link_input);
		}
	});

	$('#copy_persistence_link_small_to_clipboard').on({
		click: function() {
			copy_to_clipboard(link_input_small);
		}
	});
}


/**
 * Create session object of current frontend state.
 * To be consumed by `load_user_provided_session(user_session_settings)` to recreate the session.
 * @returns {{code: *, frontend_settings: *, language: *, worker: *, tool: *, sample_source: *}}
 */
function get_user_session_settings() {
	let user_frontend_settings = get_user_frontend_settings();
	// Reduce the size of the frontend settings object to only necessary info needed for recreation.
	user_frontend_settings = user_frontend_settings.map(function(setting) {
		return {
			"id": setting.id,
			"type": setting.type,
			"value": setting.value
		}
	});

	return {
		"tool": _CONFIG.context.tool.id,
		"worker": _CONFIG.context.current_worker.id,
		"language": _CONFIG.context.current_worker.language,
		"frontend_settings": user_frontend_settings,
		"sample_source": _CONFIG.context.sample_source,
		"code": _EDITOR.getValue()
	}
}


/**
 * Synchronize the user definable frontend settings
 * with an array of setting objects as returned by get_user_frontend_settings.
 * @param frontend_settings
 */
function set_user_frontend_settings(frontend_settings) {
	frontend_settings.forEach(function(setting) {
		// Todo: implement range, int, ...
		if (setting.type === 'bool') {
			$('#' + setting.id).prop('checked', setting.value);
		} 
	});
}


/**
 * Recreates a session.
 * @param user_session_settings
 */
function load_user_provided_session(user_session_settings) {
	choose_language(user_session_settings.language);
	if ('code' in user_session_settings) {
		_EDITOR.session.setValue(user_session_settings.code);
	}
	refresh_navbar();
	set_user_frontend_settings(user_session_settings.frontend_settings);
	if (!('code' in user_session_settings)) {
		load_sample(user_session_settings.sample_source);
	}
}

/**
 * Bind the user control buttons to process events.
 */
function init_interface_controls() {
	// Changing the tool Language.
	$('.language-selection').on({
		click: function() {
			let language = $(this).data().language;
			if (language !== get_current_language()) {
				clear_editor();
			}
			choose_language(language);
			refresh_navbar();
		}
	});

	// Handle click on "Execute"
	$('#navbar_execute_interface').on({
		click: function() {
			clear_messages();
			try {
				const settings = get_execute_settings();
				run_ultimate_task(settings);
			} catch (e) {
				alert('Could not execute Ultimate: ' + e.message);
				console.log(e);
			}
		}
	});

	// Handle click on "Cancel run!"
	$('#navbar_cancel_interface').on({
		click: function() {
			clear_messages();
			try {
				set_canceling_spinner(true);
				stop_ultimate_toolchain_job(localStorage.getItem('requestId'));
			} catch (e) {
				alert('Could not cancel Ultimate: ' + e.message);
				console.log(e);
				set_execute_spinner(false);
			}
		}
	});

	// Highlight code by message click.
	$(document).on({
		click: function() {
			let data = $(this).data();
			highlight_code(data.startLine, data.endLine, data.startCol, data.endCol, data.type);
		}
	}, '.toast');

	// Resizable Message container.
	init_messages_resize();

	$('#move-messages').on({
		click: function() {
			switch (_CONFIG.context.msg_orientation) {
				case "left":
					set_message_orientation("bottom");
					break;
				case "bottom":
					set_message_orientation("left");
					break;
			}
		}
	});

	// Let the user create a sharable link encoding the current session.
	$('#create_persistence_link').on({
		click: function() {
			create_persistence_link();
		}
	});
}


/**
 * Initialize the resizing feature for the messages column.
 */
function init_messages_resize() {
	let messages_container = $('#messages');
	let edges = { left: false, right: false, bottom: false, top: false };
	switch (_CONFIG.context.msg_orientation) {
		case "bottom":
			edges.top = true;
			break;
		case "left":
			edges.left = true;
			break;
	}

	function set_flex_basis(event) {
		switch (_CONFIG.context.msg_orientation) {
			case "bottom":
				return event.rect.height;
			case "left":
				return event.rect.width;
		}
	}

	interact('#messages')
		.resizable({
			edges: edges,
			modifiers: [
				// minimum size
				interact.modifiers.restrictSize({
					min: { height: 400, width: 400 }
				})
			]
		})
		.on('resizemove', function(event) {
			messages_container.css("flex-basis", set_flex_basis(event) + 'px');
			_EDITOR.resize();
		});

}


/**
 * Move the message column to "bottom" or "left".
 * @param new_orientation
 */
function set_message_orientation(new_orientation) {
	let content = $('#content');
	let move_msg_action = $('#move-messages');
	content.removeClass('flex-row flex-column');
	switch (new_orientation) {
		case "left":
			content.addClass('flex-row');
			move_msg_action.removeClass("oi-collapse-right oi-collapse-down");
			move_msg_action.addClass("oi-collapse-down");
			break;
		case "bottom":
			content.addClass('flex-column');
			move_msg_action.removeClass("oi-collapse-right oi-collapse-down");
			move_msg_action.addClass("oi-collapse-right");
			break;
	}
	_CONFIG.context.msg_orientation = new_orientation;
	init_messages_resize();
	_EDITOR.resize();
}


/**
 * Set available options for the navbar based on _CONFIG.context
 */
function refresh_navbar() {
	if ("current_worker" in _CONFIG.context) {
		$('#navbar_language_select_dropdown').html('Language: ' + _CONFIG.context.current_worker.language);

		set_available_code_samples(_CONFIG.context.current_worker.id);
		set_available_frontend_settings(_CONFIG.context.current_worker.language);
		$('#navbar_execute_interface').removeClass('hidden');
	} else {
		$('#navbar_sample_select_dropdown').addClass('hidden');
		$('#navbar_execute_interface').addClass('hidden');
		$('#navbar_settings_select_dropdown').addClass('hidden');
	}
}


/**
 * Extract a code annotation from a ultimate message.
 * @param message
 * @returns {{column: *, row: number, text: *, type: *, col_end: *, row_end: *}}
 */
function get_annotation_from_message(message) {
	let annotation = {
		row: message.startLNr - 1,
		column: message.startCol,
		text: message.shortDesc,
		type: message.logLvl,
		row_end: message.endLNr,
		col_end: message.endCol
	};

	return annotation
}


/**
 * Process ultimate web bridge results and add them as toasts to the editor interface.
 * @param result
 */
function add_results_to_editor(result) {
	let message;
	let messages_container = $('#messages-toasts');
	let annotations = [];
	const editor_message_template = Handlebars.compile($("#editor-message").html());

	if ('error' in result) {
		alert(result.error);
	}

	for (let key in result.results) {
		message = result.results[key];
		annotations.push(get_annotation_from_message(message));
		switch (message.logLvl) {
			case "error": {
				message.toast_classes = "border border-danger";
				message.oi_icon = "oi-circle-x text-danger";
				break;
			}
			case "warning": {
				message.toast_classes = "border border-warning";
				message.oi_icon = "oi-warning text-warning";
				break;
			}
			case "info": {
				message.toast_classes = "border border-info";
				message.oi_icon = "oi-info text-info";
				break;
			}
		}

		_EDITOR.getSession().setAnnotations(annotations);
		messages_container.append(editor_message_template(result.results[key]));
	}
	$('.toast').toast('show');
}


function Sleep(milliseconds) {
	return new Promise(resolve => setTimeout(resolve, milliseconds));
}

/**
 * Poll running job for results every 3 seconds.
 * Polling stops once there are results.
 */
function poll_results() {
	$.get(_CONFIG.backend.web_bridge_url + '/job/get/' + localStorage.getItem('requestId'), function(response) {
		switch (response.status.toLowerCase()) {
			case 'done':
				add_results_to_editor(response);
				set_execute_spinner(false);
				break;
			case 'error':
				alert('Backend error: ' + response.msg);
				console.log(response);
				break;
			default:
				// wait for 3s until something useful happens
				setTimeout(poll_results, 3000);
				break;
		}
	});
}

/**
 * Stops a running toolchain job.
 * @param job_jd
 */
function stop_ultimate_toolchain_job(job_jd) {
	$.get(_CONFIG.backend.web_bridge_url + '/job/delete/' + job_jd, function(response) {
	});
}

/**
 * Initiate a ultimate run and process the result.
 * @param settings
 */
function run_ultimate_task(settings) {
	set_execute_spinner(true);

	if (_CONFIG.meta.debug_mode) {
		$.get('./test/result.json', function(response) {
			add_results_to_editor(response);
		}).fail(function() {
			alert("Could not fetch results. Server error.");
		}).always(function() {
			set_execute_spinner(false);
		});
		return
	}

	$.post(_CONFIG.backend.web_bridge_url, settings, function(response) {
		localStorage.setItem('requestId', response.requestId);
		localStorage.setItem('pollingActive', "1");
		poll_results();
	}).fail(function() {
		alert("Could not initiate run. Server error.");
		set_execute_spinner(false);
	});
}


/**
 * Get current state of the user defined settings as a list of setting objects.
 * @returns {[]}
 */
function get_user_frontend_settings() {
	let result = [];
	_CONFIG.context.current_worker.frontend_settings.forEach(function(setting) {
		// TODO: implement float, ... settings.
		let setting_input = $('#' + setting.id);
		switch (setting["type"]) {
			case "bool":
				setting["value"] = setting_input.is(':checked');
				break;
			case "int":
			case "string":
			default:
				setting["value"] = setting_input.val();
				break;
		}
		result.push(setting);
	});

	return result
}

/**
 * Get the current settings Dict to be used as a new job for ultimate.
 * @returns {{user_settings: {}, code: string, action: string, toolchain: {id: *}}}
 */
function get_execute_settings() {
	let settings = {
		action: 'execute',
		code: _EDITOR.getSession().getValue(),
		toolchain: {
			id: _CONFIG.context.current_worker.id
		},
		code_file_extension: _CONFIG.code_file_extensions[_CONFIG.context.current_worker.language],
		user_settings: "",
		ultimate_toolchain_xml: (new XMLSerializer()).serializeToString(_CONFIG.context.current_worker.ultimate_toolchain_xml)
	};

	const user_settings = get_user_frontend_settings();
	settings.user_settings = JSON.stringify({ user_settings });

	return settings;
}


/**
 * Process a language selection.
 * @param language
 */
function choose_language(language) {
	console.log('Set current language to ' + language);
	_CONFIG.context.tool.workers.forEach(function(worker) {
		if (worker.language === language) {
			_CONFIG.context.current_worker = worker;
		}
	});

	// Load the ultimate toolchain file.
	$.get('./ultimate_toolchain_xmls/' + _CONFIG.context.current_worker.id + '.xml', function(response) {
		_CONFIG.context.current_worker.ultimate_toolchain_xml = response;
	}).fail(function() {
		alert("Could not fetch ultimate toolchain xml. Config error.");
	});
}


/**
 * Highlight (background color pop) a section in the editor.
 * Navigates to the start of the code.
 * @param start_line
 * @param end_line
 * @param start_col
 * @param end_col
 * @param css_type
 */
function highlight_code(start_line, end_line, start_col, end_col, css_type) {
	if (start_line < 0) {
		return
	}
	// Navigate to the start ot the code if not visible.
	if (!_EDITOR.isRowFullyVisible(start_line)) {
		_EDITOR.setAnimatedScroll(false);
		_EDITOR.scrollToLine(start_line, true, true);
		_EDITOR.navigateTo(start_line - 1, start_col > 0 ? start_col : 0);
	}
	// Set marker for given range.
	let maker = _EDITOR.session.addMarker(
		new Range(start_line - 1, start_col, end_line, end_col), "color-pop-animation " + css_type, "line"
	);
	// Remove the maker after 2 seconds
	setTimeout(function(marker) {
		if (marker) _EDITOR.session.removeMarker(marker);
	}, 2000, maker);
}


/**
 * Process the event of a gutter click (the area where the line numbers are).
 * Triggers code highlight for annotation clicks.
 * @param event
 */
function process_gutter_click(event) {
	let target = event.domEvent.target;

	// Check if we clicked on an annotation.
	if (((target.className.indexOf('ace_info') !== -1) ||
		(target.className.indexOf('ace_error') !== -1) ||
		(target.className.indexOf('ace_warning') !== -1)) &&
		(_EDITOR.isFocused()) &&
		(event.clientX < 20 + target.getBoundingClientRect().left)) {

		// Trigger code highlighting for clicked annotation.
		let current_row = event.getDocumentPosition().row;
		let annotations = _EDITOR.session.getAnnotations();

		annotations.forEach(function(annotation) {
			if (annotation.row === current_row) {
				highlight_code(
					annotation.row + 1,
					annotation.row_end,
					annotation.column,
					annotation.col_end,
					annotation.type
				)
			}
		});
	}
}


/**
 * Set available code samples to the dropdown.
 * This is adding each example associated to the worker id. This association originates from the build_examples.py
 * @param worker_id
 */
function set_available_code_samples(worker_id) {
	let samples_menu = $('#code_sample_dropdown_menu');
	let example_entries = '';

	try {
		_CONFIG.code_examples[worker_id].forEach(function(example) {
			example_entries += '<a class="dropdown-item sample-selection" href="#" data-source="' +
				worker_id + '/' + example.source + '">' + example.name + '</a>';
		});
	} catch (e) {
		console.log('Could set code examples:');
		console.log(e);
	}

	if (example_entries.length > 0) {
		$('#navbar_sample_select_dropdown').removeClass('hidden');
	}
	samples_menu.html(example_entries);
	$('.sample-selection').on({
		click: function() {
			load_sample($(this).data().source);
		}
	});
}


/**
 * Load an available sample into the editor.
 * @param source
 */
function load_sample(source) {
	$.get('./code_examples/' + source, function(data) {
		clear_messages();
		_EDITOR.session.setValue(data);
		_CONFIG.context.sample_source = source;
	})
}


/**
 * Set the available options for the settings dropdown menu based on the current config.
 */
function set_available_frontend_settings(language) {
	let settings_menu = $('#settings_dropdown_menu');
	let settings_entries = '';

	_CONFIG.context.current_worker.frontend_settings.forEach(function(setting) {
		switch (setting.type) {
			case "bool":
				settings_entries += '<div class="form-check ' + (setting.visible ? "" : "hidden") + '">' +
					'<input type="checkbox" class="form-check-input" id="' + setting.id + '" ' + (setting.default ? "checked" : "") + '>' +
					'<label class="form-check-label" for="' + setting.id + '">' + setting.name + '</label>' +
					'</div>';
				break;
			case "int":
				if ('range' in setting) {
					settings_entries += '<div class="form-group ' + (setting.visible ? "" : "hidden") + '">' +
						'<label for="' + setting.id + '">' + setting.name + '</label>' +
						'<input type="range" class="custom-range" min="' + setting.range[0] + '"  max="' + setting.range[1] + '" ' +
						'id="' + setting.id + '" value="' + setting.default + '" >' +
						'<span class="slider-output">Value: ' + setting.default + '</span>' +
						'</div>';
				} else {
					settings_entries += '<div class="form-group ' + (setting.visible ? "" : "hidden") + '">' +
						'<label for="' + setting.id + '">' + setting.name + '</label>' +
						'<input type="number" class="form-control" id="' + setting.id + '" value="' + setting.default + '" >' +
						'</div>';
				}
				break;
			case "real":
				if ('range' in setting) {
					settings_entries += '<div class="form-group ' + (setting.visible ? "" : "hidden") + '">' +
						'<label for="' + setting.id + '">' + setting.name + '</label>' +
						'<input type="range" class="custom-range" min="' + setting.range[0] + '"  max="' + setting.range[1] + '" ' +
						'step="0.01" id="' + setting.id + '" value="' + setting.default + '" >' +
						'<span class="slider-output">Value: ' + setting.default + '</span>' +
						'</div>';
				} else {
					settings_entries += '<div class="form-group ' + (setting.visible ? "" : "hidden") + '">' +
						'<label for="' + setting.id + '">' + setting.name + '</label>' +
						'<input type="number" step="0.01" class="form-control" id="' + setting.id + '" value="' + setting.default + '" >' +
						'</div>';
				}
				break;
			case "string":
				if ('options' in setting) { // Create a select field when options are given.
					settings_entries += '<div class="form-group ' + (setting.visible ? "" : "hidden") + '">' +
						'<label for="' + setting.id + '">' + setting.name + '</label>' +
						'<select class="form-control" id="' + setting.id + '" >';
					for (const option of setting.options) {
						settings_entries += '<option '
							+ (option === setting.default ? "selected=\"selected\"" : "") + ' >' + option + '</option>';
					}
					settings_entries += '</select></div>';
				} else {
					settings_entries += '<div class="form-group ' + (setting.visible ? "" : "hidden") + '">' +
						'<label for="' + setting.id + '">' + setting.name + '</label>' +
						'<input type="text" class="form-control" id="' + setting.id + '" value="' + setting.default + '" >' +
						'</div>';
				}
				break;
			default:
				break;
		}
	});

	// Show the settings
	settings_menu.html(settings_entries);
	if (settings_entries.length > 0) {
		$('#settings_header').removeClass('hidden');
	} else {
		$('#settings_header').addClass('hidden');
	}
	$('#navbar_settings_select_dropdown').removeClass('hidden');

	// Prevent setting menu from closing when clicking checkboxes or selections.
	$('.form-check, .form-control').on('click', function(e) {
		e.stopPropagation();
	});

	// Bind slider updates.
	$('.custom-range').on('input change', function() {
		$(this).siblings('.slider-output').html('Value: ' + $(this).val());
	});
}

/**
 * Set (activete == true) or unset the spinner indicating the results are being fetched.
 * @param activate
 */
function set_execute_spinner(activate) {
	let exec_button = $('#navbar_execute_interface');
	let cancel_button = $('#navbar_cancel_interface');
	if (activate) {
		cancel_button.removeClass('hidden');
		exec_button.html(
			'<span class="spinner-border spinner-border-sm text-primary" role="status" aria-hidden="true"></span> Running ...'
		);
	} else {
		exec_button.html('Execute');
		set_canceling_spinner(false);
		cancel_button.addClass('hidden');
	}
}

function set_canceling_spinner(activate) {
	let cancel_button = $('#navbar_cancel_interface');
	let exec_button = $('#navbar_execute_interface');
	if (activate) {
		exec_button.addClass('hidden');
		cancel_button.html(
			'<span class="spinner-border spinner-border-sm text-primary" role="status" aria-hidden="true"></span>Canceling ... '
		);
	} else {
		exec_button.removeClass('hidden');
		cancel_button.html('(Click to cancel)');
	}
}
