/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences;

import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter.Format;
import de.uni_freiburg.informatik.ultimate.core.lib.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem.IUltimatePreferenceItemValidator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.RcfgPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.Artifact;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.Concurrency;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine.ExceptionHandlingCategory;

/**
 * Initializer and container of preferences for the trace abstraction plugin.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public class TraceAbstractionPreferenceInitializer extends UltimatePreferenceInitializer {
	/*
	 * labels for the different preferencess
	 */
	public static final String LABEL_INTERPROCEDUTAL = "Interprocedural analysis (Nested Interpolants)";
	public static final String LABEL_ALL_ERRORS_AT_ONCE = "Stop after first violation was found";
	public static final String LABEL_FLOYD_HOARE_AUTOMATA_REUSE = "Reuse of Floyd-Hoare automata";
	public static final String LABEL_FLOYD_HOARE_AUTOMATA_REUSE_ENHANCEMENT =
			"Enhance during reuse of Floyd-Hoare automata";
	public static final String LABEL_ITERATIONS = "Iterations until the model checker surrenders";
	public static final String LABEL_ARTIFACT = "Kind of artifact that is visualized";
	public static final String LABEL_WATCHITERATION = "Number of iteration whose artifact is visualized";
	public static final String LABEL_HOARE =
			"Compute Hoare Annotation of negated interpolant automaton, abstraction and CFG";
	public static final String LABEL_HOARE_POSITIONS = "Positions where we compute the Hoare Annotation";
	public static final String LABEL_SEPARATE_SOLVER = "Use separate solver for trace checks";
	public static final String LABEL_INTERPOLATED_LOCS = "Compute Interpolants along a Counterexample";
	public static final String LABEL_NONLINEAR_CONSTRAINTS_IN_PATHINVARIANTS =
			"Use nonlinear constraints in PathInvariants";
	public static final String LABEL_UNSAT_CORES_IN_PATHINVARIANTS = "Use unsat cores in PathInvariants";
	public static final String LABEL_WEAKEST_PRECONDITION_IN_PATHINVARIANTS =
			"Use weakest precondition in PathInvariants";
	public static final String LABEL_ABSTRACT_INTERPRETATION_FOR_PATH_INVARIANTS =
			"Use abstract interpretation in PathInvariants";
	public static final String LABEL_INTERPOLANTS_CONSOLIDATION = "Interpolants consolidation";
	public static final String LABEL_INTERPOLANT_AUTOMATON = "Interpolant automaton";
	public static final String LABEL_DUMPAUTOMATA = "Dump automata to files";
	public static final String LABEL_AUTOMATAFORMAT = "Output format of dumped automata";
	public static final String LABEL_DUMPPATH = "Dump automata to the following directory";
	public static final String LABEL_DUMP_ONLY_REUSE = "Dump only reuse-automata";
	public static final String LABEL_INTERPOLANT_AUTOMATON_ENHANCEMENT = "Interpolant automaton enhancement";
	public static final String LABEL_HOARE_TRIPLE_CHECKS = "Hoare triple checks";
	public static final String LABEL_DIFFERENCE_SENWA = "DifferenceSenwa operation instead classical Difference";
	public static final String LABEL_MINIMIZE = "Minimization of abstraction";
	public static final String LABEL_CONCURRENCY = "Automaton type used in concurrency analysis";
	public static final String LABEL_ORDER = "Order in Petri net unfolding";
	public static final String LABEL_CUTOFF = "cut-off requires same transition";
	public static final String LABEL_UNFOLDING2NET = "use unfolding as abstraction";
	public static final String LABEL_ASSERT_CODEBLOCKS_INCREMENTALLY = "Assert CodeBlocks";
	public static final String LABEL_UNSAT_CORES = "Use unsat cores";
	public static final String LABEL_LIVE_VARIABLES = "Use live variables";
	public static final String LABEL_LANGUAGE_OPERATION = "LanguageOperation";
	public static final String LABEL_ABSINT_MODE = "Abstract interpretation Mode";
	public static final String LABEL_ABSINT_ALWAYS_REFINE = "Refine always when using abstract interpretation";
	public static final String LABEL_ERROR_TRACE_RELEVANCE_ANALYSIS_NON_FLOW_SENSITIVE =
			"Highlight relevant statements in error traces";
	public static final String TOOLTIP_ERROR_TRACE_RELEVANCE_ANALYSIS_NON_FLOW_SENSITIVE =
			"Analyse error traces and identify relevant statements. Warning: For programs with floats, arrays, or pointers this analysis may take a significant amount of time.";
	public static final String LABEL_ERROR_TRACE_RELEVANCE_ANALYSIS_FLOW_SENSITIVE =
			"Flow-sensitive error trace relevance analysis";
	public static final String LABEL_SIMPLIFICATION_TECHNIQUE = "Simplification technique";
	public static final String LABEL_XNF_CONVERSION_TECHNIQUE = "Xnf conversion technique";
	public static final String LABEL_COUNTEREXAMPLE_SEARCH_STRATEGY = "Counterexample search strategy";
	public static final String LABEL_REFINEMENT_STRATEGY = "Trace refinement strategy";
	public static final String LABEL_REFINEMENT_STRATEGY_EXCEPTION_BLACKLIST = "Trace refinement exception blacklist";

	public static final String VALUE_ABSTRACTION = "Abstraction";
	public static final String VALUE_RCFG = "RecursiveControlFlowGraph";
	public static final String VALUE_INTERPOLANT_AUTOMATON = "InterpolantAutomaton";
	public static final String VALUE_NEG_INTERPOLANT_AUTOMATON = "NegatedInterpolantAutomaton";
	public static final String VALUE_ITP_WP = "StrongestPostcondition&WeakestPrecondition";
	public static final String VALUE_ITP_GUESS = "Guess Interpolants";
	public static final String VALUE_INTERPOLANT_AUTOMATON_SINGLE_TRACE = "SingleTrace";
	public static final String VALUE_INTERPOLANT_AUTOMATON_TWO_TRACK = "TwoTrack";
	public static final String VALUE_INTERPOLANT_AUTOMATON_CANONICAL =
			"With backedges to repeated locations (Canonical)";
	public static final String VALUE_INTERPOLANT_AUTOMATON_TOTAL_INTERPOLATION = "Total interpolation (Jan)";

	public static final String VALUE_FINITE_AUTOMATON = "Finite Automata";
	public static final String VALUE_PETRI_NET = "Petri Net";
	public static final String VALUE_KMM = "Ken McMillan";
	public static final String VALUE_EVR = "Esparza Römer Vogler";
	public static final String VALUE_EVR_MARK = "ERV with equal markings";

	/*
	 * default values for the different preferences
	 */
	public static final boolean DEF_INTERPROCEDUTAL = true;
	private static final FloydHoareAutomataReuse DEF_FLOYD_HOARE_AUTOMATA_REUSE = FloydHoareAutomataReuse.NONE;
	private static final FloydHoareAutomataReuseEnhancement DEF_FLOYD_HOARE_AUTOMATA_REUSE_ENHANCEMENT =
			FloydHoareAutomataReuseEnhancement.NONE;
	public static final int DEF_ITERATIONS = 1_000_000;
	public static final String DEF_ARTIFACT = VALUE_RCFG;
	public static final int DEF_WATCHITERATION = 1_000_000;
	public static final boolean DEF_HOARE = false;
	public static final HoareAnnotationPositions DEF_HOARE_POSITIONS = HoareAnnotationPositions.All;
	public static final boolean DEF_SEPARATE_SOLVER = true;
	public static final SolverMode DEF_SOLVER = SolverMode.Internal_SMTInterpol;
	public static final String DEF_EXTERNAL_SOLVER_COMMAND = RcfgPreferenceInitializer.Z3_DEFAULT;
	public static final InterpolationTechnique DEF_INTERPOLANTS = InterpolationTechnique.ForwardPredicates;
	public static final String DEF_ADDITIONAL_EDGES = VALUE_INTERPOLANT_AUTOMATON_CANONICAL;
	public static final boolean DEF_DUMPAUTOMATA = false;
	public static final Format DEF_AUTOMATAFORMAT = Format.ATS_NUMERATE;
	public static final String DEF_DUMPPATH = ".";
	public static final boolean DEF_DIFFERENCE_SENWA = false;
	public static final boolean DEF_MINIMIZE = true;
	public static final String DEF_CONCURRENCY = VALUE_FINITE_AUTOMATON;
	public static final boolean DEF_ALL_ERRORS_AT_ONCE = true;
	public static final CounterexampleSearchStrategy DEF_COUNTEREXAMPLE_SEARCH_STRATEGY =
			CounterexampleSearchStrategy.BFS;
	public static final RefinementStrategy DEF_REFINEMENT_STRATEGY = RefinementStrategy.FIXED_PREFERENCES;
	public static final RefinementStrategyExceptionBlacklist DEF_REFINEMENT_STRATEGY_EXCEPTION_BLACKLIST =
			RefinementStrategyExceptionBlacklist.DEPENDING;
	// public static final boolean DEF_ALL_ERRORS_AT_ONCE = false;

	public static final boolean DEF_CUTOFF = true;
	public static final boolean DEF_UNFOLDING2NET = false;
	public static final String DEF_ORDER = VALUE_EVR;
	public static final boolean DEF_SIMPLIFY_CODE_BLOCKS = false;
	public static final boolean DEF_PRESERVE_GOTO_EDGES = false;
	public static final AbstractInterpretationMode DEF_ABSINT_MODE = AbstractInterpretationMode.NONE;
	public static final boolean DEF_USE_AI_PATH_PROGRAM_CONSTRUCTION = false;
	public static final boolean DEF_ERROR_TRACE_RELEVANCE_ANALYSIS_NON_FLOW_SENSITIVE = false;
	public static final boolean DEF_ERROR_TRACE_RELEVANCE_ANALYSIS_FLOW_SENSITIVE = false;

	public static final SimplificationTechnique DEF_SIMPLIFICATION_TECHNIQUE = SimplificationTechnique.SIMPLIFY_DDA;
	public static final XnfConversionTechnique DEF_XNF_CONVERSION_TECHNIQUE =
			XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION;

	private static final Boolean DEF_ABSINT_ALWAYS_REFINE = Boolean.FALSE;
	private static final boolean DEF_ONLY_REUSE = false;

	private static final String DESC_DUMP_ONLY_REUSE =
			"When dumping automata is enabled, we only dump the interpolant automaton and add to that file if it "
					+ "exists s.t. it can be reused by later verification runs.";
	private static final String DESC_FLOYD_HOARE_AUTOMATA_REUSE =
			"Try to re-use interpolant automata from input files and/or previous runs. " + FloydHoareAutomataReuse.NONE
					+ " disables the re-use, all other settings enable it. You can specifiy additional .ats files as"
					+ " input and the containing NWAs will be treated as additional interpolant automata. When "
					+ LABEL_ALL_ERRORS_AT_ONCE + " is false, this setting will additionally try to re-use the automata "
					+ "from previous runs. " + FloydHoareAutomataReuse.EAGER
					+ " will compute the difference with the initial abstraction and "
					+ "all additional interpolant automatas before the first iteration of a run. "
					+ FloydHoareAutomataReuse.LAZY_IN_ORDER + " tries in each iteration after a potential "
					+ "counterexample is found if one of the re-usable interpolant automata accepts the counterexample. "
					+ "If this is the case, this automaton is substracted from the current abstraction and removed from "
					+ "the set of reusable interpolant automata.";
	private static final String DESC_FLOYD_HOARE_AUTOMATA_REUSE_ENHANCEMENT =
			"Specifies how to compute successors on-demand for re-use interpolant automata.";

	/**
	 * Constructor.
	 */
	public TraceAbstractionPreferenceInitializer() {
		super(Activator.PLUGIN_ID, "Automizer (Trace Abstraction)");
	}

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<>(LABEL_INTERPROCEDUTAL, DEF_INTERPROCEDUTAL, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_ALL_ERRORS_AT_ONCE, DEF_ALL_ERRORS_AT_ONCE, PreferenceType.Boolean),

				new UltimatePreferenceItem<>(LABEL_FLOYD_HOARE_AUTOMATA_REUSE, DEF_FLOYD_HOARE_AUTOMATA_REUSE,
						DESC_FLOYD_HOARE_AUTOMATA_REUSE, PreferenceType.Combo, FloydHoareAutomataReuse.values()),
				new UltimatePreferenceItem<>(LABEL_FLOYD_HOARE_AUTOMATA_REUSE_ENHANCEMENT,
						DEF_FLOYD_HOARE_AUTOMATA_REUSE_ENHANCEMENT, DESC_FLOYD_HOARE_AUTOMATA_REUSE_ENHANCEMENT,
						PreferenceType.Combo, FloydHoareAutomataReuseEnhancement.values()),

				new UltimatePreferenceItem<>(LABEL_ITERATIONS, DEF_ITERATIONS, PreferenceType.Integer,
						new IUltimatePreferenceItemValidator.IntegerValidator(0, 1_000_000)),
				new UltimatePreferenceItem<>(LABEL_ARTIFACT, Artifact.RCFG, PreferenceType.Combo, Artifact.values()),
				new UltimatePreferenceItem<>(LABEL_WATCHITERATION, DEF_WATCHITERATION, PreferenceType.Integer,
						new IUltimatePreferenceItemValidator.IntegerValidator(0, 1_0000_000)),
				new UltimatePreferenceItem<>(LABEL_HOARE, DEF_HOARE, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_HOARE_POSITIONS, DEF_HOARE_POSITIONS, PreferenceType.Combo,
						HoareAnnotationPositions.values()),

				new UltimatePreferenceItem<>(LABEL_SEPARATE_SOLVER, DEF_SEPARATE_SOLVER, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(RcfgPreferenceInitializer.LABEL_Solver, DEF_SOLVER, PreferenceType.Combo,
						SolverMode.values()),
				new UltimatePreferenceItem<>(RcfgPreferenceInitializer.LABEL_FakeNonIncrementalScript,
						RcfgPreferenceInitializer.DEF_FakeNonIncrementalScript, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(RcfgPreferenceInitializer.LABEL_ExtSolverCommand,
						DEF_EXTERNAL_SOLVER_COMMAND, PreferenceType.String),
				new UltimatePreferenceItem<>(RcfgPreferenceInitializer.LABEL_ExtSolverLogic,
						RcfgPreferenceInitializer.DEF_ExtSolverLogic, PreferenceType.String),
				new UltimatePreferenceItem<>(RcfgPreferenceInitializer.LABEL_DumpToFile, Boolean.FALSE,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(RcfgPreferenceInitializer.LABEL_Path, RcfgPreferenceInitializer.DEF_Path,
						PreferenceType.Directory),

				new UltimatePreferenceItem<>(LABEL_INTERPOLATED_LOCS, DEF_INTERPOLANTS, PreferenceType.Combo,
						InterpolationTechnique.values()),
				new UltimatePreferenceItem<>(LABEL_NONLINEAR_CONSTRAINTS_IN_PATHINVARIANTS, Boolean.FALSE,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_UNSAT_CORES_IN_PATHINVARIANTS, Boolean.FALSE,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_WEAKEST_PRECONDITION_IN_PATHINVARIANTS, Boolean.FALSE,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_ABSTRACT_INTERPRETATION_FOR_PATH_INVARIANTS, Boolean.FALSE,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_INTERPOLANTS_CONSOLIDATION, Boolean.FALSE, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_UNSAT_CORES, UnsatCores.CONJUNCT_LEVEL, PreferenceType.Combo,
						UnsatCores.values()),
				new UltimatePreferenceItem<>(LABEL_LIVE_VARIABLES, Boolean.TRUE, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_ASSERT_CODEBLOCKS_INCREMENTALLY,
						AssertCodeBlockOrder.NOT_INCREMENTALLY, PreferenceType.Combo, AssertCodeBlockOrder.values()),
				new UltimatePreferenceItem<>(LABEL_INTERPOLANT_AUTOMATON, InterpolantAutomaton.CANONICAL,
						PreferenceType.Combo, InterpolantAutomaton.values()),
				new UltimatePreferenceItem<>(LABEL_DUMPAUTOMATA, DEF_DUMPAUTOMATA, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_AUTOMATAFORMAT, DEF_AUTOMATAFORMAT, PreferenceType.Combo,
						Format.values()),
				new UltimatePreferenceItem<>(LABEL_DUMPPATH, DEF_DUMPPATH, PreferenceType.Directory),
				new UltimatePreferenceItem<>(LABEL_DUMP_ONLY_REUSE, DEF_ONLY_REUSE, DESC_DUMP_ONLY_REUSE,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_INTERPOLANT_AUTOMATON_ENHANCEMENT,
						InterpolantAutomatonEnhancement.PREDICATE_ABSTRACTION, PreferenceType.Combo,
						InterpolantAutomatonEnhancement.values()),
				new UltimatePreferenceItem<>(LABEL_HOARE_TRIPLE_CHECKS, HoareTripleChecks.INCREMENTAL,
						PreferenceType.Combo, HoareTripleChecks.values()),
				new UltimatePreferenceItem<>(LABEL_LANGUAGE_OPERATION, LanguageOperation.DIFFERENCE,
						PreferenceType.Combo, LanguageOperation.values()),
				new UltimatePreferenceItem<>(LABEL_DIFFERENCE_SENWA, DEF_DIFFERENCE_SENWA, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_MINIMIZE, Minimization.MINIMIZE_SEVPA, PreferenceType.Combo,
						Minimization.values()),
				new UltimatePreferenceItem<>(LABEL_CONCURRENCY, Concurrency.FINITE_AUTOMATA, PreferenceType.Combo,
						Concurrency.values()),
				new UltimatePreferenceItem<>(LABEL_ORDER, DEF_ORDER, PreferenceType.Combo,
						new String[] { VALUE_KMM, VALUE_EVR, VALUE_EVR_MARK }),
				new UltimatePreferenceItem<>(LABEL_CUTOFF, DEF_CUTOFF, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_UNFOLDING2NET, DEF_UNFOLDING2NET, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_ABSINT_MODE, DEF_ABSINT_MODE, PreferenceType.Combo,
						AbstractInterpretationMode.values()),
				new UltimatePreferenceItem<>(LABEL_ABSINT_ALWAYS_REFINE, DEF_ABSINT_ALWAYS_REFINE,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_ERROR_TRACE_RELEVANCE_ANALYSIS_NON_FLOW_SENSITIVE,
						DEF_ERROR_TRACE_RELEVANCE_ANALYSIS_NON_FLOW_SENSITIVE,
						TOOLTIP_ERROR_TRACE_RELEVANCE_ANALYSIS_NON_FLOW_SENSITIVE, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_ERROR_TRACE_RELEVANCE_ANALYSIS_FLOW_SENSITIVE,
						DEF_ERROR_TRACE_RELEVANCE_ANALYSIS_FLOW_SENSITIVE, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_SIMPLIFICATION_TECHNIQUE, DEF_SIMPLIFICATION_TECHNIQUE,
						PreferenceType.Combo, SimplificationTechnique.values()),
				new UltimatePreferenceItem<>(LABEL_XNF_CONVERSION_TECHNIQUE, DEF_XNF_CONVERSION_TECHNIQUE,
						PreferenceType.Combo, XnfConversionTechnique.values()),
				new UltimatePreferenceItem<>(LABEL_COUNTEREXAMPLE_SEARCH_STRATEGY, DEF_COUNTEREXAMPLE_SEARCH_STRATEGY,
						PreferenceType.Combo, CounterexampleSearchStrategy.values()),
				new UltimatePreferenceItem<>(LABEL_REFINEMENT_STRATEGY, DEF_REFINEMENT_STRATEGY, PreferenceType.Combo,
						RefinementStrategy.values()),
				new UltimatePreferenceItem<>(LABEL_REFINEMENT_STRATEGY_EXCEPTION_BLACKLIST,
						DEF_REFINEMENT_STRATEGY_EXCEPTION_BLACKLIST, PreferenceType.Combo,
						RefinementStrategyExceptionBlacklist.values()), };
	}

	/**
	 * Abstract interpretation mode.
	 */
	public enum AbstractInterpretationMode {
		NONE, USE_PREDICATES, USE_PATH_PROGRAM, USE_CANONICAL, USE_TOTAL,
	}

	/**
	 * Interpolant automaton mode.
	 */
	public enum InterpolantAutomaton {
		CANONICAL, TOTALINTERPOLATION, SINGLETRACE, TWOTRACK, TOTALINTERPOLATION2
	}

	/**
	 * Interpolation technique.
	 */
	public enum InterpolationTechnique {
		Craig_NestedInterpolation, Craig_TreeInterpolation, ForwardPredicates, BackwardPredicates, FPandBP,
		FPandBPonlyIfFpWasNotPerfect, PathInvariants
	}

	/**
	 * Minimization mode.
	 */
	public enum Minimization {
		NONE, MINIMIZE_SEVPA, SHRINK_NWA, DFA_HOPCROFT_ARRAYS, DFA_HOPCROFT_LISTS, NWA_MAX_SAT, NWA_MAX_SAT2,
		NWA_COMBINATOR_PATTERN, NWA_COMBINATOR_EVERY_KTH, RAQ_DIRECT_SIMULATION, RAQ_DIRECT_SIMULATION_B,
		NWA_OVERAPPROXIMATION, NWA_COMBINATOR_MULTI_DEFAULT, NWA_COMBINATOR_MULTI_SIMULATION, DELAYED_SIMULATION,
		FAIR_SIMULATION_WITH_SCC, FAIR_SIMULATION_WITHOUT_SCC, FAIR_DIRECT_SIMULATION, RAQ_DELAYED_SIMULATION,
		RAQ_DELAYED_SIMULATION_B, FULLMULTIPEBBLE_DELAYED_SIMULATION, FULLMULTIPEBBLE_DIRECT_SIMULATION,
	}

	/**
	 * Code block assertion order. Determines in which order the different codeblocks of a trace are asserted during a
	 * trace check.
	 */
	public enum AssertCodeBlockOrder {
		/**
		 * Assert all codeblocks at once.
		 */
		NOT_INCREMENTALLY,

		/**
		 * Assert in two steps. First, assert all codeblocks that do not occur in the first loop of the trace. Second,
		 * assert the rest.
		 */
		OUTSIDE_LOOP_FIRST1,

		/**
		 * Assert codeblocks according to their "depth". Codeblocks outside of loops have depth 0, codeblocks within a
		 * loop have depth i + 1 where i is the depth of the loop codeblock.
		 *
		 * Assert all codeblocks in the order of their depth starting with depth 0.
		 */
		OUTSIDE_LOOP_FIRST2,

		/**
		 * Similar to {@link AssertCodeBlockOrder#OUTSIDE_LOOP_FIRST2}, but in reverse order (start with the deepest
		 * codeblocks).
		 */
		INSIDE_LOOP_FIRST1,

		/**
		 * Similar to {@link AssertCodeBlockOrder#OUTSIDE_LOOP_FIRST2} and
		 * {@link AssertCodeBlockOrder#INSIDE_LOOP_FIRST1} in that it also uses the depth of a codeblock. This setting
		 * alternates between depths, starting with depth 0, then asserting the maximal depth, then depth 1, etc.
		 */
		MIX_INSIDE_OUTSIDE,

		/**
		 * Assert in two steps: First terms with small constants (currently, terms that contain constants smaller than
		 * 10), then the rest.
		 */
		TERMS_WITH_SMALL_CONSTANTS_FIRST
	}

	/**
	 * Unsatisfiable core mode.
	 */
	public enum UnsatCores {
		IGNORE, STATEMENT_LEVEL, CONJUNCT_LEVEL
	}

	/**
	 * Language operation during refinement.
	 */
	public enum LanguageOperation {
		DIFFERENCE, INCREMENTAL_INCLUSION_VIA_DIFFERENCE, INCREMENTAL_INCLUSION_2,
		INCREMENTAL_INCLUSION_2_DEADEND_REMOVE, INCREMENTAL_INCLUSION_2_DEADEND_REMOVE_ANTICHAIN,
		INCREMENTAL_INCLUSION_2_DEADEND_REMOVE_ANTICHAIN_2STACKS,
		INCREMENTAL_INCLUSION_2_DEADEND_REMOVE_ANTICHAIN_2STACKS_MULTIPLECE, INCREMENTAL_INCLUSION_3,
		INCREMENTAL_INCLUSION_3_2, INCREMENTAL_INCLUSION_4, INCREMENTAL_INCLUSION_4_2, INCREMENTAL_INCLUSION_5,
		INCREMENTAL_INCLUSION_5_2,
	}

	/**
	 * Hoare triple check mode.
	 */
	public enum HoareTripleChecks {
		MONOLITHIC, INCREMENTAL
	}

	/**
	 * Hoare annotation position.
	 */
	public enum HoareAnnotationPositions {
		All, LoopsAndPotentialCycles,
	}

	/**
	 * Search strategy for counterexamples in the remainder language of the current abstraction (automaton).
	 *
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	public enum CounterexampleSearchStrategy {
		/**
		 * Breadth-first search (finds the shortest counterexample).
		 */
		BFS,
		/**
		 * Depth-first search.
		 */
		DFS
	}

	/**
	 * Strategy used for trace check and trace refinement (i.e., interpolant automaton construction).
	 *
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	public enum RefinementStrategy {
		/**
		 * Simple strategy that reads the information from the settings.
		 */
		FIXED_PREFERENCES,
		/**
		 * Taipan strategy.
		 */
		TAIPAN,
		/**
		 * Taipan without abstract interpretation
		 */
		RUBBER_TAIPAN,
		/**
		 * Taipan with abstract interpretation last
		 */
		LAZY_TAIPAN,
		/**
		 * Taipan with abstract interpretation only (no SMT solver)
		 */
		TOOTHLESS_TAIPAN,
		/**
		 * Multi track strategy that tries 1. Craig interpolation with SMTInterpol, and 2. Sp/Wp interpolation with Z3.
		 */
		PENGUIN,
		/**
		 * Multi track strategy that tries Sp/Wp interpolation with CVC4, Z3 and Mathsat with a high interpolant
		 * threshold
		 */
		WALRUS,

		CAMEL,
		/**
		 * Multi track strategy that tries Sp/Wp interpolation with CVC4, Z3 and Mathsat with a low interpolant
		 * threshold
		 */
		WOLF,
		/**
		 * Multi track strategy that tries Sp interpolation with CVC4, Z3 and Mathsat with a high interpolant threshold
		 */
		WARTHOG,
	}

	/**
	 * Specifies which categories of exceptions to throw. All other categories are ignored.
	 *
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 * @see ExceptionHandlingCategory
	 */
	public enum RefinementStrategyExceptionBlacklist {
		/**
		 * Throw no exceptions.
		 */
		NONE,
		/**
		 * Throw only unknown exceptions.
		 */
		UNKNOWN,
		/**
		 * Throw unknown exceptions and known exceptions that are categorized as "sometimes good, sometimes bad".
		 */
		DEPENDING,
		/**
		 * Throw all exceptions.
		 */
		ALL
	}

	/**
	 * Reuse Floyd-Hoare that were built for one error location for succeeding error locations.
	 *
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 *
	 */
	public enum FloydHoareAutomataReuse {
		/**
		 * No reuse.
		 */
		NONE,
		/**
		 * Take initially the difference of the control flow graph and all yet constructed Floyd-Hoare automata. Extend
		 * the Floyd-Hoare automata on-demand (while difference is constructed by new edges).
		 */
		EAGER,
		/**
		 * Not yet defined...
		 */
		LAZY_IN_ORDER,
	}

	/**
	 * How should on-demand enhancement of reuse-automata behave? Has only an impact if {@link FloydHoareAutomataReuse}
	 * is not {@link FloydHoareAutomataReuse#NONE}.
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	public enum FloydHoareAutomataReuseEnhancement {
		/**
		 * Do not use any enhancement. Usually means none of the automata can be used during verifiation.
		 */
		NONE,
		/**
		 * Try to enhance the reuse automata "as usual", i.e., compute on-demand successors for all letters of the
		 * alphabet and with solver support. May be more expensive than other options, but guarantees best re-use.
		 */
		AS_USUAL,
		/**
		 * Only compute on-demand successors for letters that are in the alphabet of the current program but are not in
		 * the alphabet of the re-use automaton.
		 */
		ONLY_NEW_LETTERS,
		/**
		 * Compute on-demand successors for all letters, but do not try to use an SMT solver for Hoare triple checks
		 * involving letters that are in the alphabet of the current program but are not in the alphabet of the re-use
		 * automaton.
		 */
		ONLY_NEW_LETTERS_SOLVER,
	}
}
