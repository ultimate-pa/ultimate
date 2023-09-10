const _CONFIG = {
	meta: {
		// debug_mode: if set to true, `test/result.json` will be used as a response for fetching ultimate results.
		debug_mode: false,
	},
	backend: {
		// web_bridge_url: URL to the WebBackend API.
		web_bridge_url: 'https://ultimate-pa.org/api'
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
		  description: "Verification of ...",
		  languages: ["Boogie", "C"],
		  logo_url: "img/tool_logo.png",
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
	//  * Id (`id`).
	//  * Front-page entry (`name`, `description`, `languages`).
	//  * Supported languages and specific settings (`workers`).
	tools: [
		{
			// name: A Human readable name of this tool. Used as Heading in the frontend.
			name: "Automizer",
			// id: A mandatory unique id for the tool.
			id: "automizer",
			// description: Frontend description.
			description: "Verification of safety properties based on an automata-theoretic approach to software verification.",
			// languages: Supported languages to be displayed in the frontend.
			languages: ["Boogie", "C"],
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
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"name": "Check division by zero",
							"key": "Check division by zero",
							"id": "cacsl2boogietranslator.check.division.by.zero",
							"visible": true,
							"default": "IGNORE",
							"options": ["IGNORE", "ASSUME", "ASSERTandASSUME"],
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"name": "Check if freed pointer was valid",
							"key": "Check if freed pointer was valid",
							"id": "cacsl2boogietranslator.check.if.freed.pointer.was.valid",
							"visible": true,
							"default": false,
							"type": "bool"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"name": "Pointer to allocated memory at dereference",
							"key": "Pointer to allocated memory at dereference",
							"id": "cacsl2boogietranslator.pointer.to.allocated.memory.at.dereference",
							"visible": true,
							"default": "IGNORE",
							"options": ["IGNORE", "ASSUME", "ASSERTandASSUME"],
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"name": "Check array bounds for arrays that are off heap",
							"key": "Check array bounds for arrays that are off heap",
							"id": "cacsl2boogietranslator.check.array.bounds.for.arrays.that.are.off.heap",
							"visible": true,
							"default": "IGNORE",
							"options": ["IGNORE", "ASSUME", "ASSERTandASSUME"],
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"name": "Check for the main procedure if all allocated memory was freed",
							"key": "Check for the main procedure if all allocated memory was freed",
							"id": "cacsl2boogietranslator.check.for.the.main.procedure.if.all.allocated.memory.was.freed",
							"visible": false,
							"default": false,
							"type": "bool"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"name": "If two pointers are subtracted or compared they have the same base address",
							"key": "If two pointers are subtracted or compared they have the same base address",
							"id": "cacsl2boogietranslator.if.two.pointers.are.subtracted.or.compared.they.have.the.same.base.address",
							"visible": false,
							"default": "IGNORE",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"name": "Pointer base address is valid at dereference",
							"key": "Pointer base address is valid at dereference",
							"id": "cacsl2boogietranslator.pointer.base.address.is.valid.at.dereference",
							"visible": true,
							"default": "IGNORE",
							"options": ["IGNORE", "ASSUME", "ASSERTandASSUME"],
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"name": "Overapproximate operations on floating types",
							"key": "Overapproximate operations on floating types",
							"id": "cacsl2boogietranslator.overapproximate.operations.on.floating.types",
							"visible": false,
							"default": true,
							"type": "bool"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"name": "Use constant arrays",
							"key": "Use constant arrays",
							"id": "cacsl2boogietranslator.use.constant.arrays",
							"visible": false,
							"default": true,
							"type": "bool"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder",
							"name": "Size of a code block",
							"key": "Size of a code block",
							"id": "rcfgbuilder.size.of.a.code.block",
							"visible": false,
							"default": "SequenceOfStatements",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder",
							"name": "SMT solver",
							"key": "SMT solver",
							"id": "rcfgbuilder.smt.solver",
							"visible": false,
							"default": "External_DefaultMode",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "Compute Interpolants along a Counterexample",
							"key": "Compute Interpolants along a Counterexample",
							"id": "traceabstraction.compute.interpolants.along.a.counterexample",
							"visible": false,
							"default": "FPandBP",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "SMT solver",
							"key": "SMT solver",
							"id": "traceabstraction.smt.solver",
							"visible": false,
							"default": "External_ModelsAndUnsatCoreMode",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "Compute Hoare Annotation of negated interpolant automaton, abstraction and CFG",
							"key": "Compute Hoare Annotation of negated interpolant automaton, abstraction and CFG",
							"id": "traceabstraction.compute.hoare.annotation.of.negated.interpolant.automaton,.abstraction.and.cfg",
							"visible": false,
							"default": true,
							"type": "bool"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "Positions where we compute the Hoare Annotation",
							"key": "Positions where we compute the Hoare Annotation",
							"id": "traceabstraction.positions.where.we.compute.the.hoare.annotation",
							"visible": false,
							"default": "LoopsAndPotentialCycles",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "Trace refinement strategy",
							"key": "Trace refinement strategy",
							"id": "traceabstraction.trace.refinement.strategy",
							"visible": false,
							"default": "CAMEL",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "Trace refinement exception blacklist",
							"key": "Trace refinement exception blacklist",
							"id": "traceabstraction.trace.refinement.exception.blacklist",
							"visible": false,
							"default": "DEPENDING",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "Automaton type used in concurrency analysis",
							"key": "Automaton type used in concurrency analysis",
							"id": "traceabstraction.automaton.type.used.in.concurrency.analysis",
							"visible": false,
							"default": "PETRI_NET",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "Apply one-shot large block encoding in concurrent analysis",
							"key": "Apply one-shot large block encoding in concurrent analysis",
							"id": "traceabstraction.apply.one-shot.large.block.encoding.in.concurrent.analysis",
							"visible": false,
							"default": false,
							"type": "bool"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.boogie.procedureinliner",
							"name": "Ignore calls to procedures called more than once",
							"key": "Ignore calls to procedures called more than once",
							"id": "procedureinliner.ignore.calls.to.procedures.called.more.than.once",
							"visible": false,
							"default": "ONLY_FOR_SEQUENTIAL_PROGRAMS",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.blockencoding",
							"name": "Create parallel compositions if possible",
							"key": "Create parallel compositions if possible",
							"id": "blockencoding.create.parallel.compositions.if.possible",
							"visible": false,
							"default": false,
							"type": "bool"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.blockencoding",
							"name": "Rewrite not-equals",
							"key": "Rewrite not-equals",
							"id": "blockencoding.rewrite.not-equals",
							"visible": false,
							"default": false,
							"type": "bool"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.blockencoding",
							"name": "Use SBE",
							"key": "Use SBE",
							"id": "blockencoding.use.sbe",
							"visible": false,
							"default": true,
							"type": "bool"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.blockencoding",
							"name": "Minimize states even if more edges are added than removed.",
							"key": "Minimize states even if more edges are added than removed.",
							"id": "blockencoding.minimize.states.even.if.more.edges.are.added.than.removed",
							"visible": false,
							"default": false,
							"type": "bool"
						}
					]
				},
				{
					language: "boogie",
					id: "boogieAutomizer",
					task_id: "AUTOMIZER_BOOGIE",
					frontend_settings: [
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder",
							"name": "Size of a code block",
							"key": "Size of a code block",
							"id": "rcfgbuilder.size.of.a.code.block",
							"visible": false,
							"default": "SequenceOfStatements",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder",
							"name": "SMT solver",
							"key": "SMT solver",
							"id": "rcfgbuilder.smt.solver",
							"visible": false,
							"default": "External_DefaultMode",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "Compute Interpolants along a Counterexample",
							"key": "Compute Interpolants along a Counterexample",
							"id": "traceabstraction.compute.interpolants.along.a.counterexample",
							"visible": false,
							"default": "FPandBP",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "SMT solver",
							"key": "SMT solver",
							"id": "traceabstraction.smt.solver",
							"visible": false,
							"default": "External_ModelsAndUnsatCoreMode",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "Compute Hoare Annotation of negated interpolant automaton, abstraction and CFG",
							"key": "Compute Hoare Annotation of negated interpolant automaton, abstraction and CFG",
							"id": "traceabstraction.compute.hoare.annotation.of.negated.interpolant.automaton,.abstraction.and.cfg",
							"visible": false,
							"default": true,
							"type": "bool"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "Positions where we compute the Hoare Annotation",
							"key": "Positions where we compute the Hoare Annotation",
							"id": "traceabstraction.positions.where.we.compute.the.hoare.annotation",
							"visible": false,
							"default": "LoopsAndPotentialCycles",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "Trace refinement strategy",
							"key": "Trace refinement strategy",
							"id": "traceabstraction.trace.refinement.strategy",
							"visible": false,
							"default": "CAMEL",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "Trace refinement exception blacklist",
							"key": "Trace refinement exception blacklist",
							"id": "traceabstraction.trace.refinement.exception.blacklist",
							"visible": false,
							"default": "DEPENDING",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "Automaton type used in concurrency analysis",
							"key": "Automaton type used in concurrency analysis",
							"id": "traceabstraction.automaton.type.used.in.concurrency.analysis",
							"visible": false,
							"default": "PETRI_NET",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "Apply one-shot large block encoding in concurrent analysis",
							"key": "Apply one-shot large block encoding in concurrent analysis",
							"id": "traceabstraction.apply.one-shot.large.block.encoding.in.concurrent.analysis",
							"visible": false,
							"default": false,
							"type": "bool"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.boogie.procedureinliner",
							"name": "Ignore calls to procedures called more than once",
							"key": "Ignore calls to procedures called more than once",
							"id": "procedureinliner.ignore.calls.to.procedures.called.more.than.once",
							"visible": false,
							"default": "ONLY_FOR_SEQUENTIAL_PROGRAMS",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.blockencoding",
							"name": "Create parallel compositions if possible",
							"key": "Create parallel compositions if possible",
							"id": "blockencoding.create.parallel.compositions.if.possible",
							"visible": false,
							"default": false,
							"type": "bool"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.blockencoding",
							"name": "Rewrite not-equals",
							"key": "Rewrite not-equals",
							"id": "blockencoding.rewrite.not-equals",
							"visible": false,
							"default": false,
							"type": "bool"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.blockencoding",
							"name": "Use SBE",
							"key": "Use SBE",
							"id": "blockencoding.use.sbe",
							"visible": false,
							"default": true,
							"type": "bool"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.blockencoding",
							"name": "Minimize states even if more edges are added than removed.",
							"key": "Minimize states even if more edges are added than removed.",
							"id": "blockencoding.minimize.states.even.if.more.edges.are.added.than.removed",
							"visible": false,
							"default": false,
							"type": "bool"
						}
					]
				}
			],
			logo_url: "img/tool_logo.png",
		},
		{
			name: "Büchi Automizer",
			id: "buechi_automizer",
			description: "Termination analysis based on Büchi automata.",
			languages: ["Boogie", "C"],
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
			name: "GemCutter",
			id: "gemcutter",
			description: "A verifier for concurrent programs based on commutativity – the observation that for certain statements, the execution order does not matter.",
			languages: ["Boogie", "C"],
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
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"name": "Check absence of signed integer overflows",
							"key": "Check absence of signed integer overflows",
							"id": "cacsl2boogietranslator.check.absence.of.signed.integer.overflows",
							"visible": true,
							"default": true,
							"type": "bool"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"name": "Check division by zero",
							"key": "Check division by zero",
							"id": "cacsl2boogietranslator.check.division.by.zero",
							"visible": true,
							"default": "IGNORE",
							"options": ["IGNORE", "ASSUME", "ASSERTandASSUME"],
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"name": "Check if freed pointer was valid",
							"key": "Check if freed pointer was valid",
							"id": "cacsl2boogietranslator.check.if.freed.pointer.was.valid",
							"visible": true,
							"default": false,
							"type": "bool"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"name": "Pointer to allocated memory at dereference",
							"key": "Pointer to allocated memory at dereference",
							"id": "cacsl2boogietranslator.pointer.to.allocated.memory.at.dereference",
							"visible": true,
							"default": "IGNORE",
							"options": ["IGNORE", "ASSUME", "ASSERTandASSUME"],
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"name": "Check array bounds for arrays that are off heap",
							"key": "Check array bounds for arrays that are off heap",
							"id": "cacsl2boogietranslator.check.array.bounds.for.arrays.that.are.off.heap",
							"visible": true,
							"default": "IGNORE",
							"options": ["IGNORE", "ASSUME", "ASSERTandASSUME"],
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"name": "Check for the main procedure if all allocated memory was freed",
							"key": "Check for the main procedure if all allocated memory was freed",
							"id": "cacsl2boogietranslator.check.for.the.main.procedure.if.all.allocated.memory.was.freed",
							"visible": false,
							"default": false,
							"type": "bool"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"name": "If two pointers are subtracted or compared they have the same base address",
							"key": "If two pointers are subtracted or compared they have the same base address",
							"id": "cacsl2boogietranslator.if.two.pointers.are.subtracted.or.compared.they.have.the.same.base.address",
							"visible": false,
							"default": "IGNORE",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"name": "Pointer base address is valid at dereference",
							"key": "Pointer base address is valid at dereference",
							"id": "cacsl2boogietranslator.pointer.base.address.is.valid.at.dereference",
							"visible": true,
							"default": "IGNORE",
							"options": ["IGNORE", "ASSUME", "ASSERTandASSUME"],
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"name": "Overapproximate operations on floating types",
							"key": "Overapproximate operations on floating types",
							"id": "cacsl2boogietranslator.overapproximate.operations.on.floating.types",
							"visible": false,
							"default": true,
							"type": "bool"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"name": "Use constant arrays",
							"key": "Use constant arrays",
							"id": "cacsl2boogietranslator.use.constant.arrays",
							"visible": false,
							"default": true,
							"type": "bool"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder",
							"name": "Size of a code block",
							"key": "Size of a code block",
							"id": "rcfgbuilder.size.of.a.code.block",
							"visible": false,
							"default": "SequenceOfStatements",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder",
							"name": "SMT solver",
							"key": "SMT solver",
							"id": "rcfgbuilder.smt.solver",
							"visible": false,
							"default": "External_DefaultMode",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "CEGAR restart behaviour",
							"key": "CEGAR restart behaviour",
							"id": "traceabstraction.cegar.restart.behaviour",
							"visible": false,
							"default": "ONE_CEGAR_PER_THREAD_INSTANCE",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "Compute Interpolants along a Counterexample",
							"key": "Compute Interpolants along a Counterexample",
							"id": "traceabstraction.compute.interpolants.along.a.counterexample",
							"visible": false,
							"default": "FPandBP",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "SMT solver",
							"key": "SMT solver",
							"id": "traceabstraction.smt.solver",
							"visible": false,
							"default": "External_ModelsAndUnsatCoreMode",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "Compute Hoare Annotation of negated interpolant automaton, abstraction and CFG",
							"key": "Compute Hoare Annotation of negated interpolant automaton, abstraction and CFG",
							"id": "traceabstraction.compute.hoare.annotation.of.negated.interpolant.automaton,.abstraction.and.cfg",
							"visible": false,
							"default": true,
							"type": "bool"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "Positions where we compute the Hoare Annotation",
							"key": "Positions where we compute the Hoare Annotation",
							"id": "traceabstraction.positions.where.we.compute.the.hoare.annotation",
							"visible": false,
							"default": "LoopsAndPotentialCycles",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "Trace refinement strategy",
							"key": "Trace refinement strategy",
							"id": "traceabstraction.trace.refinement.strategy",
							"visible": false,
							"default": "CAMEL",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "Automaton type used in concurrency analysis",
							"key": "Automaton type used in concurrency analysis",
							"id": "traceabstraction.automaton.type.used.in.concurrency.analysis",
							"visible": false,
							"default": "PARTIAL_ORDER_FA",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "Apply one-shot large block encoding in concurrent analysis",
							"key": "Apply one-shot large block encoding in concurrent analysis",
							"id": "traceabstraction.apply.one-shot.large.block.encoding.in.concurrent.analysis",
							"visible": false,
							"default": false,
							"type": "bool"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "Partial Order Reduction in concurrent analysis",
							"key": "Partial Order Reduction in concurrent analysis",
							"id": "traceabstraction.partial.order.reduction.in.concurrent.analysis",
							"visible": false,
							"default": "PERSISTENT_SLEEP_NEW_STATES_FIXEDORDER",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "DFS Order used in POR",
							"key": "DFS Order used in POR",
							"id": "traceabstraction.dfs.order.used.in.por",
							"visible": false,
							"default": "LOOP_LOCKSTEP",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.boogie.procedureinliner",
							"name": "Ignore calls to procedures called more than once",
							"key": "Ignore calls to procedures called more than once",
							"id": "procedureinliner.ignore.calls.to.procedures.called.more.than.once",
							"visible": false,
							"default": "ONLY_FOR_SEQUENTIAL_PROGRAMS",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.blockencoding",
							"name": "Create parallel compositions if possible",
							"key": "Create parallel compositions if possible",
							"id": "blockencoding.create.parallel.compositions.if.possible",
							"visible": false,
							"default": false,
							"type": "bool"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.blockencoding",
							"name": "Use SBE",
							"key": "Use SBE",
							"id": "blockencoding.use.sbe",
							"visible": false,
							"default": true,
							"type": "bool"
						}
					]
				},
				{
					language: "boogie",
					id: "boogieGemCutter",
					task_id: "GEMCUTTER_BOOGIE",
					frontend_settings: [
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder",
							"name": "Size of a code block",
							"key": "Size of a code block",
							"id": "rcfgbuilder.size.of.a.code.block",
							"visible": false,
							"default": "SequenceOfStatements",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder",
							"name": "SMT solver",
							"key": "SMT solver",
							"id": "rcfgbuilder.smt.solver",
							"visible": false,
							"default": "External_DefaultMode",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "CEGAR restart behaviour",
							"key": "CEGAR restart behaviour",
							"id": "traceabstraction.cegar.restart.behaviour",
							"visible": false,
							"default": "ONE_CEGAR_PER_THREAD_INSTANCE",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "Compute Interpolants along a Counterexample",
							"key": "Compute Interpolants along a Counterexample",
							"id": "traceabstraction.compute.interpolants.along.a.counterexample",
							"visible": false,
							"default": "FPandBP",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "SMT solver",
							"key": "SMT solver",
							"id": "traceabstraction.smt.solver",
							"visible": false,
							"default": "External_ModelsAndUnsatCoreMode",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "Compute Hoare Annotation of negated interpolant automaton, abstraction and CFG",
							"key": "Compute Hoare Annotation of negated interpolant automaton, abstraction and CFG",
							"id": "traceabstraction.compute.hoare.annotation.of.negated.interpolant.automaton,.abstraction.and.cfg",
							"visible": false,
							"default": true,
							"type": "bool"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "Positions where we compute the Hoare Annotation",
							"key": "Positions where we compute the Hoare Annotation",
							"id": "traceabstraction.positions.where.we.compute.the.hoare.annotation",
							"visible": false,
							"default": "LoopsAndPotentialCycles",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "Trace refinement strategy",
							"key": "Trace refinement strategy",
							"id": "traceabstraction.trace.refinement.strategy",
							"visible": false,
							"default": "CAMEL",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "Automaton type used in concurrency analysis",
							"key": "Automaton type used in concurrency analysis",
							"id": "traceabstraction.automaton.type.used.in.concurrency.analysis",
							"visible": false,
							"default": "PARTIAL_ORDER_FA",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "Apply one-shot large block encoding in concurrent analysis",
							"key": "Apply one-shot large block encoding in concurrent analysis",
							"id": "traceabstraction.apply.one-shot.large.block.encoding.in.concurrent.analysis",
							"visible": false,
							"default": false,
							"type": "bool"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "Partial Order Reduction in concurrent analysis",
							"key": "Partial Order Reduction in concurrent analysis",
							"id": "traceabstraction.partial.order.reduction.in.concurrent.analysis",
							"visible": false,
							"default": "PERSISTENT_SLEEP_NEW_STATES_FIXEDORDER",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "DFS Order used in POR",
							"key": "DFS Order used in POR",
							"id": "traceabstraction.dfs.order.used.in.por",
							"visible": false,
							"default": "LOOP_LOCKSTEP",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.boogie.procedureinliner",
							"name": "Ignore calls to procedures called more than once",
							"key": "Ignore calls to procedures called more than once",
							"id": "procedureinliner.ignore.calls.to.procedures.called.more.than.once",
							"visible": false,
							"default": "ONLY_FOR_SEQUENTIAL_PROGRAMS",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.blockencoding",
							"name": "Create parallel compositions if possible",
							"key": "Create parallel compositions if possible",
							"id": "blockencoding.create.parallel.compositions.if.possible",
							"visible": false,
							"default": false,
							"type": "bool"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.blockencoding",
							"name": "Use SBE",
							"key": "Use SBE",
							"id": "blockencoding.use.sbe",
							"visible": false,
							"default": true,
							"type": "bool"
						}
					]
				}
			]
		},
		{
			name: "Kojak",
			id: "kojak",
			description: "A software model checker.",
			languages: ["Boogie", "C"],
			workers: [
				{
					language: "c",
					id: "cKojak",
					task_id: "KOJAK_C",
					frontend_settings: [
						{
							// name: Settings name displayed in the settings menu.
							name: "Check for memory leak in main procedure",
							// id: A mandatory unique id for this setting.
							id: "chck_main_mem_leak",
							// plugin_id: Ultimate plugin affected by this setting.
							plugin_id: "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							// key: Setting key as used by the plugin.
							key: "Check for the main procedure if all allocated memory was freed",
							// type: Setting type can be one of ("bool", "int", "string", "real")
							type: "bool",
							// default: Default state/value for the setting.
							default: false,
							// range: If the type is "int" or "real", a slider will be generated in the frontend.
							// range: [1, 12],
							// options: If the type is "string", a selection field will be generated in the frontend.
							// options: ["foo", "bar", "baz"]
							// visible: If true, this setting is exposed to the user.
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
			name: "Taipan",
			id: "taipan",
			description: "Verification of safety properties using trace abstraction and abstract interpretation on path programs.",
			languages: ["Boogie", "C"],
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
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.sifa",
							"name": "Call Summarizer",
							"key": "Call Summarizer",
							"id": "sifa.call.summarizer",
							"visible": false,
							"default": "TopInputCallSummarizer",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.sifa",
							"name": "Simplification Technique",
							"key": "Simplification Technique",
							"id": "sifa.simplification.technique",
							"visible": false,
							"default": "POLY_PAC",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"name": "Check division by zero",
							"key": "Check division by zero",
							"id": "cacsl2boogietranslator.check.division.by.zero",
							"visible": true,
							"default": "IGNORE",
							"options": ["IGNORE", "ASSUME", "ASSERTandASSUME"],
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"name": "Check if freed pointer was valid",
							"key": "Check if freed pointer was valid",
							"id": "cacsl2boogietranslator.check.if.freed.pointer.was.valid",
							"visible": true,
							"default": false,
							"type": "bool"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"name": "Pointer to allocated memory at dereference",
							"key": "Pointer to allocated memory at dereference",
							"id": "cacsl2boogietranslator.pointer.to.allocated.memory.at.dereference",
							"visible": true,
							"default": "IGNORE",
							"options": ["IGNORE", "ASSUME", "ASSERTandASSUME"],
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"name": "Check array bounds for arrays that are off heap",
							"key": "Check array bounds for arrays that are off heap",
							"id": "cacsl2boogietranslator.check.array.bounds.for.arrays.that.are.off.heap",
							"visible": true,
							"default": "IGNORE",
							"options": ["IGNORE", "ASSUME", "ASSERTandASSUME"],
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"name": "Check for the main procedure if all allocated memory was freed",
							"key": "Check for the main procedure if all allocated memory was freed",
							"id": "cacsl2boogietranslator.check.for.the.main.procedure.if.all.allocated.memory.was.freed",
							"visible": false,
							"default": false,
							"type": "bool"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"name": "If two pointers are subtracted or compared they have the same base address",
							"key": "If two pointers are subtracted or compared they have the same base address",
							"id": "cacsl2boogietranslator.if.two.pointers.are.subtracted.or.compared.they.have.the.same.base.address",
							"visible": false,
							"default": "IGNORE",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"name": "Pointer base address is valid at dereference",
							"key": "Pointer base address is valid at dereference",
							"id": "cacsl2boogietranslator.pointer.base.address.is.valid.at.dereference",
							"visible": true,
							"default": "IGNORE",
							"options": ["IGNORE", "ASSUME", "ASSERTandASSUME"],
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"name": "Overapproximate operations on floating types",
							"key": "Overapproximate operations on floating types",
							"id": "cacsl2boogietranslator.overapproximate.operations.on.floating.types",
							"visible": false,
							"default": true,
							"type": "bool"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"name": "Use constant arrays",
							"key": "Use constant arrays",
							"id": "cacsl2boogietranslator.use.constant.arrays",
							"visible": false,
							"default": true,
							"type": "bool"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder",
							"name": "Size of a code block",
							"key": "Size of a code block",
							"id": "rcfgbuilder.size.of.a.code.block",
							"visible": false,
							"default": "LoopFreeBlock",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder",
							"name": "SMT solver",
							"key": "SMT solver",
							"id": "rcfgbuilder.smt.solver",
							"visible": false,
							"default": "External_DefaultMode",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "Compute Interpolants along a Counterexample",
							"key": "Compute Interpolants along a Counterexample",
							"id": "traceabstraction.compute.interpolants.along.a.counterexample",
							"visible": false,
							"default": "FPandBP",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "SMT solver",
							"key": "SMT solver",
							"id": "traceabstraction.smt.solver",
							"visible": false,
							"default": "External_ModelsAndUnsatCoreMode",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "Abstract interpretation Mode",
							"key": "Abstract interpretation Mode",
							"id": "traceabstraction.abstract.interpretation.mode",
							"visible": false,
							"default": "USE_PREDICATES",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "Compute Hoare Annotation of negated interpolant automaton, abstraction and CFG",
							"key": "Compute Hoare Annotation of negated interpolant automaton, abstraction and CFG",
							"id": "traceabstraction.compute.hoare.annotation.of.negated.interpolant.automaton,.abstraction.and.cfg",
							"visible": false,
							"default": true,
							"type": "bool"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "Positions where we compute the Hoare Annotation",
							"key": "Positions where we compute the Hoare Annotation",
							"id": "traceabstraction.positions.where.we.compute.the.hoare.annotation",
							"visible": false,
							"default": "LoopsAndPotentialCycles",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "Trace refinement strategy",
							"key": "Trace refinement strategy",
							"id": "traceabstraction.trace.refinement.strategy",
							"visible": false,
							"default": "SIFA_TAIPAN",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "Trace refinement exception blacklist",
							"key": "Trace refinement exception blacklist",
							"id": "traceabstraction.trace.refinement.exception.blacklist",
							"visible": false,
							"default": "NONE",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.boogie.procedureinliner",
							"name": "User list type",
							"key": "User list type",
							"id": "procedureinliner.user.list.type",
							"visible": false,
							"default": "DISABLED",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.boogie.procedureinliner",
							"name": "Ignore calls to procedures called more than once",
							"key": "Ignore calls to procedures called more than once",
							"id": "procedureinliner.ignore.calls.to.procedures.called.more.than.once",
							"visible": false,
							"default": "ONLY_FOR_SEQUENTIAL_PROGRAMS",
							"type": "string"
						}
					]
				},
				{
					language: "boogie",
					id: "boogieTaipan",
					task_id: "TAIPAN_BOOGIE",
					"frontend_settings": [
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.sifa",
							"name": "Call Summarizer",
							"key": "Call Summarizer",
							"id": "sifa.call.summarizer",
							"visible": false,
							"default": "TopInputCallSummarizer",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.sifa",
							"name": "Simplification Technique",
							"key": "Simplification Technique",
							"id": "sifa.simplification.technique",
							"visible": false,
							"default": "POLY_PAC",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder",
							"name": "Size of a code block",
							"key": "Size of a code block",
							"id": "rcfgbuilder.size.of.a.code.block",
							"visible": false,
							"default": "LoopFreeBlock",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder",
							"name": "SMT solver",
							"key": "SMT solver",
							"id": "rcfgbuilder.smt.solver",
							"visible": false,
							"default": "External_DefaultMode",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "Compute Interpolants along a Counterexample",
							"key": "Compute Interpolants along a Counterexample",
							"id": "traceabstraction.compute.interpolants.along.a.counterexample",
							"visible": false,
							"default": "FPandBP",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "SMT solver",
							"key": "SMT solver",
							"id": "traceabstraction.smt.solver",
							"visible": false,
							"default": "External_ModelsAndUnsatCoreMode",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "Abstract interpretation Mode",
							"key": "Abstract interpretation Mode",
							"id": "traceabstraction.abstract.interpretation.mode",
							"visible": false,
							"default": "USE_PREDICATES",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "Compute Hoare Annotation of negated interpolant automaton, abstraction and CFG",
							"key": "Compute Hoare Annotation of negated interpolant automaton, abstraction and CFG",
							"id": "traceabstraction.compute.hoare.annotation.of.negated.interpolant.automaton,.abstraction.and.cfg",
							"visible": false,
							"default": true,
							"type": "bool"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "Positions where we compute the Hoare Annotation",
							"key": "Positions where we compute the Hoare Annotation",
							"id": "traceabstraction.positions.where.we.compute.the.hoare.annotation",
							"visible": false,
							"default": "LoopsAndPotentialCycles",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "Trace refinement strategy",
							"key": "Trace refinement strategy",
							"id": "traceabstraction.trace.refinement.strategy",
							"visible": false,
							"default": "SIFA_TAIPAN",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"name": "Trace refinement exception blacklist",
							"key": "Trace refinement exception blacklist",
							"id": "traceabstraction.trace.refinement.exception.blacklist",
							"visible": false,
							"default": "NONE",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.boogie.procedureinliner",
							"name": "User list type",
							"key": "User list type",
							"id": "procedureinliner.user.list.type",
							"visible": false,
							"default": "DISABLED",
							"type": "string"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.boogie.procedureinliner",
							"name": "Ignore calls to procedures called more than once",
							"key": "Ignore calls to procedures called more than once",
							"id": "procedureinliner.ignore.calls.to.procedures.called.more.than.once",
							"visible": false,
							"default": "ONLY_FOR_SEQUENTIAL_PROGRAMS",
							"type": "string"
						}
					]
				}
			]
		},
		{
			name: "LTL Automizer",
			id: "ltl_automizer",
			description: "An LTL software model checker based on Büchi programs.",
			languages: ["C"],
			workers: [
				{
					language: "c",
					id: "cLTLAutomizer",
					task_id: "LTLAUTOMIZER_C",
					"frontend_settings": [
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"default": "ASSUME",
							"visible": false,
							"name": "Pointer base address is valid at dereference",
							"options": [
								"IGNORE",
								"ASSUME",
								"ASSERTandASSUME"
							],
							"id": "cacsl2boogietranslator.pointer.base.address.is.valid.at.dereference",
							"type": "string",
							"key": "Pointer base address is valid at dereference"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"default": false,
							"visible": false,
							"name": "Check if freed pointer was valid",
							"id": "cacsl2boogietranslator.check.if.freed.pointer.was.valid",
							"type": "bool",
							"key": "Check if freed pointer was valid"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"default": false,
							"visible": false,
							"name": "Check unreachability of error function in SV-COMP mode",
							"id": "cacsl2boogietranslator.check.unreachability.of.error.function.in.sv-comp.mode",
							"type": "bool",
							"key": "Check unreachability of error function in SV-COMP mode"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"default": "ASSUME",
							"visible": false,
							"name": "If two pointers are subtracted or compared they have the same base address",
							"options": [
								"IGNORE",
								"ASSUME",
								"ASSERTandASSUME"
							],
							"id": "cacsl2boogietranslator.if.two.pointers.are.subtracted.or.compared.they.have.the.same.base.address",
							"type": "string",
							"key": "If two pointers are subtracted or compared they have the same base address"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"default": "ASSUME",
							"visible": false,
							"name": "Check array bounds for arrays that are off heap",
							"options": [
								"IGNORE",
								"ASSUME",
								"ASSERTandASSUME"
							],
							"id": "cacsl2boogietranslator.check.array.bounds.for.arrays.that.are.off.heap",
							"type": "string",
							"key": "Check array bounds for arrays that are off heap"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"default": true,
							"visible": false,
							"name": "Use constant arrays",
							"id": "cacsl2boogietranslator.use.constant.arrays",
							"type": "bool",
							"key": "Use constant arrays"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"default": "IGNORE",
							"visible": false,
							"name": "Check division by zero",
							"options": [
								"IGNORE",
								"ASSUME",
								"ASSERTandASSUME"
							],
							"id": "cacsl2boogietranslator.check.division.by.zero",
							"type": "string",
							"key": "Check division by zero"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"default": true,
							"visible": false,
							"name": "Overapproximate operations on floating types",
							"id": "cacsl2boogietranslator.overapproximate.operations.on.floating.types",
							"type": "bool",
							"key": "Overapproximate operations on floating types"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"default": "ASSUME",
							"visible": false,
							"name": "Pointer to allocated memory at dereference",
							"options": [
								"IGNORE",
								"ASSUME",
								"ASSERTandASSUME"
							],
							"id": "cacsl2boogietranslator.pointer.to.allocated.memory.at.dereference",
							"type": "string",
							"key": "Pointer to allocated memory at dereference"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"default": "CAMEL",
							"visible": false,
							"name": "Trace refinement strategy",
							"options": [
								"FIXED_PREFERENCES",
								"TAIPAN",
								"RUBBER_TAIPAN",
								"LAZY_TAIPAN",
								"TOOTHLESS_TAIPAN",
								"PENGUIN",
								"WALRUS",
								"CAMEL",
								"CAMEL_NO_AM",
								"CAMEL_SMT_AM",
								"LIZARD",
								"BADGER",
								"WOLF",
								"BEAR",
								"WARTHOG",
								"WARTHOG_NO_AM",
								"MAMMOTH",
								"MAMMOTH_NO_AM",
								"SMTINTERPOL",
								"DACHSHUND",
								"SIFA_TAIPAN",
								"TOOTHLESS_SIFA_TAIPAN",
								"MCR"
							],
							"id": "traceabstraction.trace.refinement.strategy",
							"type": "string",
							"key": "Trace refinement strategy"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer",
							"default": false,
							"visible": false,
							"name": "Try twofold refinement",
							"id": "buchiautomizer.try.twofold.refinement",
							"type": "bool",
							"key": "Try twofold refinement"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer",
							"default": false,
							"visible": false,
							"name": "Use old map elimination",
							"id": "buchiautomizer.use.old.map.elimination",
							"type": "bool",
							"key": "Use old map elimination"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.blockencoding",
							"default": true,
							"visible": false,
							"name": "Use SBE",
							"id": "blockencoding.use.sbe",
							"type": "bool",
							"key": "Use SBE"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.blockencoding",
							"default": true,
							"visible": false,
							"name": "Minimize states even if more edges are added than removed.",
							"id": "blockencoding.minimize.states.even.if.more.edges.are.added.than.removed",
							"type": "bool",
							"key": "Minimize states even if more edges are added than removed."
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.blockencoding",
							"default": true,
							"visible": false,
							"name": "Rewrite not-equals",
							"id": "blockencoding.rewrite.not-equals",
							"type": "bool",
							"key": "Rewrite not-equals"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.blockencoding",
							"default": false,
							"visible": false,
							"name": "Create parallel compositions if possible",
							"id": "blockencoding.create.parallel.compositions.if.possible",
							"type": "bool",
							"key": "Create parallel compositions if possible"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.blockencoding",
							"default": "NONE",
							"visible": false,
							"name": "Minimize states using LBE with the strategy",
							"options": [
								"NONE",
								"SINGLE",
								"SINGLE_NODE_MULTI_EDGE",
								"MULTI"
							],
							"id": "blockencoding.minimize.states.using.lbe.with.the.strategy",
							"type": "string",
							"key": "Minimize states using LBE with the strategy"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder",
							"default": "SingleStatement",
							"visible": false,
							"name": "Size of a code block",
							"options": [
								"SingleStatement",
								"SequenceOfStatements",
								"LoopFreeBlock"
							],
							"id": "rcfgbuilder.size.of.a.code.block",
							"type": "string",
							"key": "Size of a code block"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.core",
							"default": "de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierPusher\u003dERROR;",
							"visible": false,
							"name": "Log level for class",
							"id": "core.log.level.for.class",
							"type": "string",
							"key": "Log level for class"
						}
					]
				}
			]
		},
		{
			name: "Lasso Ranker",
			id: "lasso_ranker",
			description: "Synthesis of ranking functions and nontermination arguments.",
			languages: ["Boogie", "C"],
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
			name: "Automata Library",
			id: "automata_library",
			description: "Nested Word Automata, Büchi Nested Word Automata, Petri Net, Alternating Finite Automata, Tree Automata.",
			languages: ["Automata_script"],
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
			name: "Referee",
			id: "referee",
			description: "Checking validity of given invariants.",
			languages: ["Boogie", "C"],
			workers: [
				{
					language: "c",
					id: "cReferee",
					task_id: "REFEREE_C",
					"frontend_settings": [
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"default": "",
							"visible": false,
							"name": "Entry function",
							"id": "cacsl2boogietranslator_entry_function",
							"type": "string",
							"key": "Entry function"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"default": true,
							"visible": false,
							"name": "Use bitvectors instead of ints",
							"id": "cacsl2boogietranslator_use_bitvectors_instead_of_ints",
							"type": "bool",
							"key": "Use bitvectors instead of ints"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"default": "HoenickeLindenmann_4ByteResolution",
							"visible": false,
							"name": "Memory model",
							"options": [
								"HoenickeLindenmann_Original",
								"HoenickeLindenmann_1ByteResolution",
								"HoenickeLindenmann_2ByteResolution",
								"HoenickeLindenmann_4ByteResolution",
								"HoenickeLindenmann_8ByteResolution"
							],
							"id": "cacsl2boogietranslator_memory_model",
							"type": "string",
							"key": "Memory model"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"default": true,
							"visible": false,
							"name": "Adapt memory model on pointer casts if necessary",
							"id": "cacsl2boogietranslator_adapt_memory_model_on_pointer_casts_if_necessary",
							"type": "bool",
							"key": "Adapt memory model on pointer casts if necessary"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"default": false,
							"visible": false,
							"name": "Report unsoundness warnings",
							"id": "cacsl2boogietranslator_report_unsoundness_warnings",
							"type": "bool",
							"key": "Report unsoundness warnings"
						},
					]
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
			name: "Eliminator",
			id: "eliminator",
			description: "Run SMT script.",
			languages: ["Smt"],
			workers: [
				{
					language: "smt",
					id: "smtEliminator",
					task_id: "ELIMINATOR_SMT",
					"frontend_settings": [
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.source.smtparser",
							"default": "External_DefaultMode",
							"visible": false,
							"name": "SMT solver",
							"options": [
								"Internal_SMTInterpol",
								"External_PrincessInterpolationMode",
								"External_SMTInterpolInterpolationMode",
								"External_Z3InterpolationMode",
								"External_MathsatInterpolationMode",
								"External_ModelsAndUnsatCoreMode",
								"External_ModelsMode",
								"External_DefaultMode"
							],
							"id": "smtparser.smt.solver",
							"type": "string",
							"key": "SMT solver"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.source.smtparser",
							"default": "UltimateEliminator",
							"visible": false,
							"name": "SmtParser Mode",
							"options": [
								"GenericSmtSolver",
								"MSODSolver",
								"UltimateEliminator",
								"UltimateTreeAutomizer"
							],
							"id": "smtparser.smtparser.mode",
							"type": "string",
							"key": "SmtParser Mode"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.source.smtparser",
							"default": "",
							"visible": false,
							"name": "Command for external solver",
							"id": "smtparser.command.for.external.solver",
							"type": "string",
							"key": "Command for external solver"
						}
					]
				}
			]
		}
	]
};
