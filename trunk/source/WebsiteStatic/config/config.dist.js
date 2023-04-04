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
							default: true,
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
					id: "boogieAutomizer",
					task_id: "AUTOMIZER_BOOGIE",
					frontend_settings: []
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
			name: "Kojak",
			id: "kojak",
			description: "A software model checker.",
			languages: ["Boogie", "C"],
			workers: [
				{
					language: "c",
					id: "cKojak",
					task_id: "KOJAK_C",
					frontend_settings: []
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
							"default": true,
							"visible": false,
							"name": "Check absence of data races in concurrent programs",
							"id": "cacsl2boogietranslator.check.absence.of.data.races.in.concurrent.programs",
							"type": "bool",
							"key": "Check absence of data races in concurrent programs"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"default": "IGNORE",
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
							"default": "IGNORE",
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
							"default": "IGNORE",
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
							"default": "IGNORE",
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
							"plugin_id": "de.uni_freiburg.informatik.ultimate.boogie.procedureinliner",
							"default": "ONLY_FOR_SEQUENTIAL_PROGRAMS",
							"visible": false,
							"name": "Ignore calls to procedures called more than once",
							"options": [
								"ALWAYS",
								"NEVER",
								"ONLY_FOR_CONCURRENT_PROGRAMS",
								"ONLY_FOR_SEQUENTIAL_PROGRAMS"
							],
							"id": "procedureinliner.ignore.calls.to.procedures.called.more.than.once",
							"type": "string",
							"key": "Ignore calls to procedures called more than once"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.boogie.procedureinliner",
							"default": "DISABLED",
							"visible": false,
							"name": "User list type",
							"options": [
								"DISABLED",
								"BLACKLIST_RESTRICT",
								"BLACKLIST_ONLY",
								"WHITELIST_EXTEND",
								"WHITELIST_RESTRICT",
								"WHITELIST_ONLY"
							],
							"id": "procedureinliner.user.list.type",
							"type": "string",
							"key": "User list type"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"default": "External_ModelsAndUnsatCoreMode",
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
							"id": "traceabstraction.smt.solver",
							"type": "string",
							"key": "SMT solver"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"default": "FPandBP",
							"visible": false,
							"name": "Compute Interpolants along a Counterexample",
							"options": [
								"Craig_NestedInterpolation",
								"Craig_TreeInterpolation",
								"ForwardPredicates",
								"BackwardPredicates",
								"FPandBP",
								"FPandBPonlyIfFpWasNotPerfect",
								"PathInvariants",
								"PDR",
								"AcceleratedInterpolation"
							],
							"id": "traceabstraction.compute.interpolants.along.a.counterexample",
							"type": "string",
							"key": "Compute Interpolants along a Counterexample"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"default": true,
							"visible": false,
							"name": "Compute Hoare Annotation of negated interpolant automaton, abstraction and CFG",
							"id": "traceabstraction.compute.hoare.annotation.of.negated.interpolant.automaton,.abstraction.and.cfg",
							"type": "bool",
							"key": "Compute Hoare Annotation of negated interpolant automaton, abstraction and CFG"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"default": "LoopsAndPotentialCycles",
							"visible": false,
							"name": "Positions where we compute the Hoare Annotation",
							"options": [
								"All",
								"LoopsAndPotentialCycles"
							],
							"id": "traceabstraction.positions.where.we.compute.the.hoare.annotation",
							"type": "string",
							"key": "Positions where we compute the Hoare Annotation"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"default": "z3 SMTLIB2_COMPLIANT\u003dtrue -memory:2024 -smt2 -in",
							"visible": false,
							"name": "Command for external solver",
							"id": "traceabstraction.command.for.external.solver",
							"type": "string",
							"key": "Command for external solver"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"default": "NONE",
							"visible": false,
							"name": "Trace refinement exception blacklist",
							"options": [
								"NONE",
								"UNKNOWN",
								"DEPENDING",
								"ALL"
							],
							"id": "traceabstraction.trace.refinement.exception.blacklist",
							"type": "string",
							"key": "Trace refinement exception blacklist"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"default": "SIFA_TAIPAN",
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
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"default": "USE_PREDICATES",
							"visible": false,
							"name": "Abstract interpretation Mode",
							"options": [
								"NONE",
								"USE_PREDICATES",
								"USE_PATH_PROGRAM",
								"USE_CANONICAL",
								"USE_TOTAL"
							],
							"id": "traceabstraction.abstract.interpretation.mode",
							"type": "string",
							"key": "Abstract interpretation Mode"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.sifa",
							"default": "TopInputCallSummarizer",
							"visible": false,
							"name": "Call Summarizer",
							"options": [
								"TopInputCallSummarizer",
								"InterpretCallSummarizer",
								"ReUseSupersetCallSummarizer"
							],
							"id": "sifa.call.summarizer",
							"type": "string",
							"key": "Call Summarizer"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.sifa",
							"default": "POLY_PAC",
							"visible": false,
							"name": "Simplification Technique",
							"options": [
								"SIMPLIFY_BDD_PROP",
								"SIMPLIFY_BDD_FIRST_ORDER",
								"SIMPLIFY_QUICK",
								"SIMPLIFY_DDA",
								"POLY_PAC",
								"NONE"
							],
							"id": "sifa.simplification.technique",
							"type": "string",
							"key": "Simplification Technique"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder",
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
							"id": "rcfgbuilder.smt.solver",
							"type": "string",
							"key": "SMT solver"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder",
							"default": "z3 SMTLIB2_COMPLIANT\u003dtrue -memory:2024 -smt2 -in -t:2000",
							"visible": false,
							"name": "Command for external solver",
							"id": "rcfgbuilder.command.for.external.solver",
							"type": "string",
							"key": "Command for external solver"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2",
							"default": true,
							"visible": false,
							"name": "Explicit value domain",
							"id": "abstractinterpretationv2.explicit.value.domain",
							"type": "bool",
							"key": "Explicit value domain"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2",
							"default": false,
							"visible": false,
							"name": "Octagon Domain",
							"id": "abstractinterpretationv2.octagon.domain",
							"type": "bool",
							"key": "Octagon Domain"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2",
							"default": true,
							"visible": false,
							"name": "Use the RCFG-of-the-future interface",
							"id": "abstractinterpretationv2.use.the.rcfg-of-the-future.interface",
							"type": "bool",
							"key": "Use the RCFG-of-the-future interface"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2",
							"default": "PoormanAbstractDomain",
							"visible": false,
							"name": "Abstract domain for RCFG-of-the-future",
							"options": [
								"EmptyDomain",
								"VPDomain",
								"DataflowDomain",
								"LiveVariableDomain",
								"SMTTheoryDomain",
								"PoormanAbstractDomain"
							],
							"id": "abstractinterpretationv2.abstract.domain.for.rcfg-of-the-future",
							"type": "string",
							"key": "Abstract domain for RCFG-of-the-future"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2",
							"default": true,
							"visible": false,
							"name": "Check feasibility of abstract posts with an SMT solver",
							"id": "abstractinterpretationv2.check.feasibility.of.abstract.posts.with.an.smt.solver",
							"type": "bool",
							"key": "Check feasibility of abstract posts with an SMT solver"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2",
							"default": false,
							"visible": false,
							"name": "Interval Domain",
							"id": "abstractinterpretationv2.interval.domain",
							"type": "bool",
							"key": "Interval Domain"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2",
							"default": "CompoundDomain",
							"visible": false,
							"name": "Abstract domain",
							"options": [
								"EmptyDomain",
								"SignDomain",
								"IntervalDomain",
								"OctagonDomain",
								"CongruenceDomain",
								"CompoundDomain",
								"ArrayDomain",
								"ExplicitValueDomain"
							],
							"id": "abstractinterpretationv2.abstract.domain",
							"type": "string",
							"key": "Abstract domain"
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
				},
				{
					language: "boogie",
					id: "boogieTaipan",
					task_id: "TAIPAN_BOOGIE",
					"frontend_settings": [
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"default": true,
							"visible": false,
							"name": "Check absence of data races in concurrent programs",
							"id": "cacsl2boogietranslator.check.absence.of.data.races.in.concurrent.programs",
							"type": "bool",
							"key": "Check absence of data races in concurrent programs"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator",
							"default": "IGNORE",
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
							"default": "IGNORE",
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
							"default": "IGNORE",
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
							"default": "IGNORE",
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
							"plugin_id": "de.uni_freiburg.informatik.ultimate.boogie.procedureinliner",
							"default": "ONLY_FOR_SEQUENTIAL_PROGRAMS",
							"visible": false,
							"name": "Ignore calls to procedures called more than once",
							"options": [
								"ALWAYS",
								"NEVER",
								"ONLY_FOR_CONCURRENT_PROGRAMS",
								"ONLY_FOR_SEQUENTIAL_PROGRAMS"
							],
							"id": "procedureinliner.ignore.calls.to.procedures.called.more.than.once",
							"type": "string",
							"key": "Ignore calls to procedures called more than once"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.boogie.procedureinliner",
							"default": "DISABLED",
							"visible": false,
							"name": "User list type",
							"options": [
								"DISABLED",
								"BLACKLIST_RESTRICT",
								"BLACKLIST_ONLY",
								"WHITELIST_EXTEND",
								"WHITELIST_RESTRICT",
								"WHITELIST_ONLY"
							],
							"id": "procedureinliner.user.list.type",
							"type": "string",
							"key": "User list type"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"default": "External_ModelsAndUnsatCoreMode",
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
							"id": "traceabstraction.smt.solver",
							"type": "string",
							"key": "SMT solver"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"default": "FPandBP",
							"visible": false,
							"name": "Compute Interpolants along a Counterexample",
							"options": [
								"Craig_NestedInterpolation",
								"Craig_TreeInterpolation",
								"ForwardPredicates",
								"BackwardPredicates",
								"FPandBP",
								"FPandBPonlyIfFpWasNotPerfect",
								"PathInvariants",
								"PDR",
								"AcceleratedInterpolation"
							],
							"id": "traceabstraction.compute.interpolants.along.a.counterexample",
							"type": "string",
							"key": "Compute Interpolants along a Counterexample"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"default": true,
							"visible": false,
							"name": "Compute Hoare Annotation of negated interpolant automaton, abstraction and CFG",
							"id": "traceabstraction.compute.hoare.annotation.of.negated.interpolant.automaton,.abstraction.and.cfg",
							"type": "bool",
							"key": "Compute Hoare Annotation of negated interpolant automaton, abstraction and CFG"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"default": "LoopsAndPotentialCycles",
							"visible": false,
							"name": "Positions where we compute the Hoare Annotation",
							"options": [
								"All",
								"LoopsAndPotentialCycles"
							],
							"id": "traceabstraction.positions.where.we.compute.the.hoare.annotation",
							"type": "string",
							"key": "Positions where we compute the Hoare Annotation"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"default": "z3 SMTLIB2_COMPLIANT\u003dtrue -memory:2024 -smt2 -in",
							"visible": false,
							"name": "Command for external solver",
							"id": "traceabstraction.command.for.external.solver",
							"type": "string",
							"key": "Command for external solver"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"default": "NONE",
							"visible": false,
							"name": "Trace refinement exception blacklist",
							"options": [
								"NONE",
								"UNKNOWN",
								"DEPENDING",
								"ALL"
							],
							"id": "traceabstraction.trace.refinement.exception.blacklist",
							"type": "string",
							"key": "Trace refinement exception blacklist"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"default": "SIFA_TAIPAN",
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
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction",
							"default": "USE_PREDICATES",
							"visible": false,
							"name": "Abstract interpretation Mode",
							"options": [
								"NONE",
								"USE_PREDICATES",
								"USE_PATH_PROGRAM",
								"USE_CANONICAL",
								"USE_TOTAL"
							],
							"id": "traceabstraction.abstract.interpretation.mode",
							"type": "string",
							"key": "Abstract interpretation Mode"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.sifa",
							"default": "TopInputCallSummarizer",
							"visible": false,
							"name": "Call Summarizer",
							"options": [
								"TopInputCallSummarizer",
								"InterpretCallSummarizer",
								"ReUseSupersetCallSummarizer"
							],
							"id": "sifa.call.summarizer",
							"type": "string",
							"key": "Call Summarizer"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.sifa",
							"default": "POLY_PAC",
							"visible": false,
							"name": "Simplification Technique",
							"options": [
								"SIMPLIFY_BDD_PROP",
								"SIMPLIFY_BDD_FIRST_ORDER",
								"SIMPLIFY_QUICK",
								"SIMPLIFY_DDA",
								"POLY_PAC",
								"NONE"
							],
							"id": "sifa.simplification.technique",
							"type": "string",
							"key": "Simplification Technique"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder",
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
							"id": "rcfgbuilder.smt.solver",
							"type": "string",
							"key": "SMT solver"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder",
							"default": "z3 SMTLIB2_COMPLIANT\u003dtrue -memory:2024 -smt2 -in -t:2000",
							"visible": false,
							"name": "Command for external solver",
							"id": "rcfgbuilder.command.for.external.solver",
							"type": "string",
							"key": "Command for external solver"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2",
							"default": true,
							"visible": false,
							"name": "Explicit value domain",
							"id": "abstractinterpretationv2.explicit.value.domain",
							"type": "bool",
							"key": "Explicit value domain"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2",
							"default": false,
							"visible": false,
							"name": "Octagon Domain",
							"id": "abstractinterpretationv2.octagon.domain",
							"type": "bool",
							"key": "Octagon Domain"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2",
							"default": true,
							"visible": false,
							"name": "Use the RCFG-of-the-future interface",
							"id": "abstractinterpretationv2.use.the.rcfg-of-the-future.interface",
							"type": "bool",
							"key": "Use the RCFG-of-the-future interface"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2",
							"default": "PoormanAbstractDomain",
							"visible": false,
							"name": "Abstract domain for RCFG-of-the-future",
							"options": [
								"EmptyDomain",
								"VPDomain",
								"DataflowDomain",
								"LiveVariableDomain",
								"SMTTheoryDomain",
								"PoormanAbstractDomain"
							],
							"id": "abstractinterpretationv2.abstract.domain.for.rcfg-of-the-future",
							"type": "string",
							"key": "Abstract domain for RCFG-of-the-future"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2",
							"default": true,
							"visible": false,
							"name": "Check feasibility of abstract posts with an SMT solver",
							"id": "abstractinterpretationv2.check.feasibility.of.abstract.posts.with.an.smt.solver",
							"type": "bool",
							"key": "Check feasibility of abstract posts with an SMT solver"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2",
							"default": false,
							"visible": false,
							"name": "Interval Domain",
							"id": "abstractinterpretationv2.interval.domain",
							"type": "bool",
							"key": "Interval Domain"
						},
						{
							"plugin_id": "de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2",
							"default": "CompoundDomain",
							"visible": false,
							"name": "Abstract domain",
							"options": [
								"EmptyDomain",
								"SignDomain",
								"IntervalDomain",
								"OctagonDomain",
								"CongruenceDomain",
								"CompoundDomain",
								"ArrayDomain",
								"ExplicitValueDomain"
							],
							"id": "abstractinterpretationv2.abstract.domain",
							"type": "string",
							"key": "Abstract domain"
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
			description: "Nested Word Automta, Büchi Nested Word Automta, Petri Net, Alternating Finite Automata, Tree Automata.",
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
			name: "Petri Automizer",
			id: "petri_automizer",
			description: "Petri net-based analysis of concurrent programs.",
			languages: ["Boogie"],
			workers: [
				{
					language: "boogie",
					id: "boogieConcurrentTraceAbstr",
					task_id: "CONCURRENT_BOOGIE",
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
