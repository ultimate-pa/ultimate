const _CONFIG = {
	meta: {
		// debug_mode: if set to true, `test/result.json` will be used as a response for fetching ultimate results.
		debug_mode: false,
	},
	backend: {
		// web_bridge_url: URL to the WebBackend API.
		web_bridge_url: 'http://127.0.0.1:8080/api'
	},
	editor: {
		// Default content of the editor.
		init_code: '// Enter code here ...',
		// default_msg_orientation: one of ["bottom" | "left"], 
		//                          determines the ultimate response messages default orientation.
		default_msg_orientation: "left"
	},
	// code_file_extensions: Determines the file extension to be used as input for the ultimate tool.
	//                       The key is the language of the tool in the frontend; 
	//                       The value is the file extension to be used by ultimate.
	code_file_extensions: {
		c: '.c',
		boogie: '.bpl',
		c_pp: '.c',
		automata_script: '.ats',
		smt: '.smt2'
	},
	// tools: List of tool specific configurations. Each tool entry is a object like:
	/**
		  id: "automizer",
		  workers: [  // Each worker for this tool defines a language specific instance of the tool.
		  {
				  language: "c",  // Language mus be available in `code_file_extensions` settings.
				  id: "cAutomizer",  // Unique id for this worker.
				  frontend_settings: [  // Frontend settings will be vailable to set by the user
				{
					  name: "Check for memory leak in main procedure",  	// The name show on the website.
						id: "chck_main_mem_leak",  							// Some id unique to this setting over all workers.
						plugin_id: "de.uni_freiburg.informatik.ultimate.plugins.foo", // The plugin id of the Ultimate plugin.
						key: "the key" // The key used by Ultimate (i.e., the label)
					type: "bool",  // Setting type can be one of ("bool", "int", "string", "real")
						default: true, // default: Default state/value for the setting.
						// range: If the type is "int" or "real", a slider will be generated in the frontend.
					// range: [1, 12],
					// options: If the type is "string", a selection field will be generated in the frontend.
					// options: ["foo", "bar", "baz"]
					// visible: If true, this setting is exposed to the user.
					visible: true
				}
		}
	 */
	tools: [
		{
			// id: A mandatory unique id for the tool.
			id: "automizer",
			// workers: List of workers. Each worker for this tool defines a language specific toolchain.
			workers: [
				{
					// language: A Language that must be available in `code_file_extensions` settings.
					language: "c",
					// id: A mandatory unique id for this worker.
					id: "cAutomizer",
					// frontend_settings: A list of settings that will be available to set by the user specificly for this worker.
					frontend_settings: [
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"name": "Check absence of data races in concurrent programs",
							"key": "Check absence of data races in concurrent programs",
							"id": "cacsl2boogietranslator.check.absence.of.data.races.in.concurrent.programs",
							"visible": true,
							"default": true,
							"type": "bool"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"name": "Check absence of signed integer overflows",
							"key": "Check absence of signed integer overflows",
							"id": "cacsl2boogietranslator.check.absence.of.signed.integer.overflows",
							"visible": true,
							"default": true,
							"type": "bool"
						},
					]
				},
				{
					language: "boogie",
					id: "boogieAutomizer",
					task_id: "AUTOMIZER_BOOGIE",
					frontend_settings: []
				}
			],
		},
		{
			id: "buechi_automizer",
			workers: [
				{
					language: "c",
					id: "cBuchiAutomizer",
					task_id: "TERMINATION_C",
					frontend_settings: []
				},
				{
					language: "boogie",
					id: "boogieBuchiAutomizer",
					task_id: "TERMINATION_BOOGIE",
					frontend_settings: []
				}
			]
		},
		{
			id: "gemcutter",
			workers: [
				{
					language: "c",
					id: "cGemCutter",
					task_id: "GEMCUTTER_C",
					frontend_settings: [
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"name": "Check absence of data races in concurrent programs",
							"key": "Check absence of data races in concurrent programs",
							"id": "cacsl2boogietranslator.check.absence.of.data.races.in.concurrent.programs",
							"visible": true,
							"default": true,
							"type": "bool"
						},
					]
				},
				{
					language: "boogie",
					id: "boogieGemCutter",
					task_id: "GEMCUTTER_BOOGIE",
					frontend_settings: []
				}
			]
		},
		{
			id: "kojak",
			workers: [
				{
					language: "c",
					id: "cKojak",
					task_id: "KOJAK_C",
					frontend_settings: [
						{
							name: "Check for memory leak in main procedure",
							id: "chck_main_mem_leak",
							plugin_id: "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							key: "Check for the main procedure if all allocated memory was freed",
							type: "bool",
							default: false,
							visible: true
						},
						{
							name: "Check for overflows of signed integers",
							id: "chck_signed_int_overflow",
							plugin_id: "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							key: "Check absence of signed integer overflows",
							type: "bool",
							default: true,
							visible: true
						}
					]
				},
				{
					language: "boogie",
					id: "boogieKojak",
					task_id: "KOJAK_BOOGIE",
					frontend_settings: []
				}
			]
		},
		{
			id: "taipan",
			workers: [
				{
					language: "c",
					id: "cTaipan",
					task_id: "TAIPAN_C",
					"frontend_settings": [
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"name": "Check absence of data races in concurrent programs",
							"key": "Check absence of data races in concurrent programs",
							"id": "cacsl2boogietranslator.check.absence.of.data.races.in.concurrent.programs",
							"visible": true,
							"default": true,
							"type": "bool"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"name": "Check absence of signed integer overflows",
							"key": "Check absence of signed integer overflows",
							"id": "cacsl2boogietranslator.check.absence.of.signed.integer.overflows",
							"visible": true,
							"default": true,
							"type": "bool"
						},
				  ]
				},
				{
					language: "boogie",
					id: "boogieTaipan",
					task_id: "TAIPAN_BOOGIE",
					"frontend_settings": []
				}
			]
		},
		{
			id: "ltl_automizer",
			workers: [
				{
					language: "c",
					id: "cLTLAutomizer",
					task_id: "LTLAUTOMIZER_C",
					"frontend_settings": []
				}
			]
		},
		{
			id: "lasso_ranker",
			workers: [
				{
					language: "c",
					id: "cLassoRanker",
					task_id: "RANK_SYNTHESIS_C",
					frontend_settings: []
				},
				{
					language: "boogie",
					id: "boogieLassoRanker",
					task_id: "RANK_SYNTHESIS_BOOGIE",
					frontend_settings: []
				}
			]
		},
		{
			id: "automata_library",
			workers: [
				{
					language: "automata_script",
					id: "automataScript",
					task_id: "AUTOMATA_SCRIPT",
					frontend_settings: []
				}
			]
		},
		{
			id: "referee",
			workers: [
				{
					language: "c",
					id: "cReferee",
					task_id: "REFEREE_C",
					frontend_settings: []
				},
				{
					language: "boogie",
					id: "boogieReferee",
					task_id: "REFEREE_BOOGIE",
					frontend_settings: []
				}
			]
		},
		{
			id: "eliminator",
			workers: [
				{
					language: "smt",
					id: "smtEliminator",
					task_id: "ELIMINATOR_SMT",
					"frontend_settings": []
				}
			]
		}
	]
};
