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
		C: '.c',
		Boogie: '.bpl',
		C_pp: '.c',
		automata_script: '.ats',
		Smt: '.smt2'
	}
};
