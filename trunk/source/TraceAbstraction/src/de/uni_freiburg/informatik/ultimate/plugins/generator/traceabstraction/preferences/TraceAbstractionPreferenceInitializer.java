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

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter.Format;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmptyHeuristic.AStarHeuristic;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.PetriNetUnfolder.EventOrderEnum;
import de.uni_freiburg.informatik.ultimate.core.lib.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem.IUltimatePreferenceItemValidator;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItemContainer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItemGroup;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.LoopAccelerators;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerUtils.HoareTripleChecks;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrderType;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.SmtFeatureHeuristicPartitioningType;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.UnsatCores;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown.RefinementStrategyExceptionBlacklist;
import de.uni_freiburg.informatik.ultimate.lib.proofs.floydhoare.HoareAnnotationPositions;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SMTFeatureExtractionTermClassifier.ScoringMethod;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.ExternalSolver;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.PartialOrderMode;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.PartialOrderReductionFacade.OrderType;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IndependenceSettings;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IndependenceSettings.AbstractionType;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IndependenceSettings.IndependenceType;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.RcfgPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionStarter.CegarRestartBehaviour;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.errorabstraction.IErrorAutomatonBuilder.ErrorAutomatonType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.Artifact;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.Concurrency;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.LooperCheck;

/**
 * Initializer and container of preferences for the trace abstraction plugin.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public class TraceAbstractionPreferenceInitializer extends UltimatePreferenceInitializer {
	// This setting is useful to debug the proof check.
	public static final String LABEL_READ_INITIAL_PROOF_ASSERTIONS_FROM_FILE =
			"Read initial proof assertions from file if available";
	private static final boolean DEF_READ_INITIAL_PROOF_ASSERTIONS_FROM_FILE = false;

	// User Limits
	// ========================================================================

	public static final String LABEL_USERLIMIT_TRACE_HISTOGRAM = "Limit trace histogram size";
	private static final int DEF_USERLIMIT_TRACE_HISTOGRAM = 0;
	private static final String DESC_USERLIMIT_TRACE_HISTOGRAM =
			"Abort the analysis of either a single error location or the whole program if the trace histogram of the "
					+ "current counterexample is larger than this value. 0 disables this limit.";

	public static final String LABEL_USERLIMIT_TIME = "Limit analysis time";
	private static final int DEF_USERLIMIT_TIME = 0;
	private static final String DESC_USERLIMIT_TIME =
			"Abort the analysis of either a single error location or the whole program if more time than specified has "
					+ "elapsed. Time is specified in seconds. 0 disables this limit.";

	public static final String LABEL_USERLIMIT_PATH_PROGRAM = "Limit path program analysis attempts";
	private static final int DEF_USERLIMIT_PATH_PROGRAM = 0;
	private static final String DESC_USERLIMIT_PATH_PROGRAM =
			"Abort the analysis of either a single error location or the whole program if the same path program has "
					+ "been induced by spurious counterexamples more than the specified amount of times. "
					+ "0 disables this limit.";

	public static final String LABEL_USERLIMIT_ITERATIONS = "Limit iterations";
	private static final int DEF_USERLIMIT_ITERATIONS = 1_000_000;
	private static final String DESC_USERLIMIT_ITERATIONS =
			"Abort the analysis of either a single error location or the whole program if more than the specified "
					+ "amount of iterations occured. 0 disables this limit.";

	// Settings for concurrent programs
	// ========================================================================

	public static final String LABEL_ORDER_OF_ERROR_LOCATIONS = "Order of the error locations to be checked";
	private static final OrderOfErrorLocations DEF_ORDER_OF_ERROR_LOCATIONS = OrderOfErrorLocations.TOGETHER;
	private static final String DESC_ORDER_OF_ERROR_LOCATIONS =
			"Order to check the reachability for different types of error locations (for concurrent programs). "
					+ "With " + OrderOfErrorLocations.INSUFFICIENT_FIRST
					+ " we first check, if there are enough threads in our translation, before checking for errors in the program. "
					+ OrderOfErrorLocations.PROGRAM_FIRST + " and " + OrderOfErrorLocations.TOGETHER
					+ " work accordingly.";

	public static final String LABEL_CONCURRENCY = "Automaton type used in concurrency analysis";
	private static final Concurrency DEF_CONCURRENCY = Concurrency.FINITE_AUTOMATA;

	public static final String LABEL_MCR_REFINEMENT_STRATEGY = "Trace refinement strategy used in MCR";
	private static final RefinementStrategy DEF_MCR_REFINEMENT_STRATEGY = RefinementStrategy.FIXED_PREFERENCES;

	public static final String LABEL_MCR_INTERPOLANT_METHOD =
			"Method to provide additional interpolants for the MCR automaton";
	private static final McrInterpolantMethod DEF_MCR_INTERPOLANT_METHOD = McrInterpolantMethod.WP;

	// Settings for Petri net Large Block Encoding (Lipton Reduction)
	// ========================================================================

	public static final String LABEL_PETRI_LBE_ONESHOT = "Apply one-shot large block encoding in concurrent analysis";
	private static final boolean DEF_PETRI_LBE_ONESHOT = true;

	public static final String LABEL_INDEPENDENCE_PLBE =
			"Independence relation used for large block encoding in concurrent analysis";
	private static final IndependenceType DEF_INDEPENDENCE_PLBE = IndependenceType.SEMANTIC;

	public static final String LABEL_SEMICOMM_PLBE =
			"Use semi-commutativity for large block encoding in concurrent analysis";
	private static final boolean DEF_SEMICOMM_PLBE = true;

	// Settings for Partial Order Reduction (GemCutter)
	// ========================================================================

	public static final String LABEL_POR_ONESHOT = "Apply one-shot Partial Order Reduction to input program";
	private static final boolean DEF_POR_ONESHOT = false;

	public static final String LABEL_POR_MODE = "Partial Order Reduction in concurrent analysis";
	private static final PartialOrderMode DEF_POR_MODE = PartialOrderMode.NONE;

	public static final String LABEL_POR_NUM_INDEPENDENCE = "Number of independence relations to use for POR";
	private static final int DEF_POR_NUM_INDEPENDENCE = 1;

	public static final String LABEL_DUMP_INDEPENDENCE_SCRIPT = "Dump SMT script used for independence checks";
	private static final boolean DEF_DUMP_INDEPENDENCE_SCRIPT = false;

	public static final String LABEL_INDEPENDENCE_SCRIPT_DUMP_PATH =
			"Dump independence script to the following directory";
	private static final String DEF_INDEPENDENCE_SCRIPT_DUMP_PATH = "";

	public static final String LABEL_INDEPENDENCE_POR = "Independence relation used for POR in concurrent analysis";
	public static final String LABEL_POR_ABSTRACTION = "Abstraction used for commutativity in POR";
	public static final String LABEL_COND_POR = "Use conditional POR in concurrent analysis";
	public static final String LABEL_SEMICOMM_POR = "Use semi-commutativity for POR in concurrent analysis";
	public static final String LABEL_INDEPENDENCE_SOLVER_POR = "SMT solver used for commutativity in POR";
	public static final String LABEL_INDEPENDENCE_SOLVER_TIMEOUT_POR =
			"SMT solver timeout for commutativity in POR (in ms)";

	public static final String LABEL_POR_DFS_ORDER = "DFS Order used in POR";
	private static final OrderType DEF_POR_DFS_ORDER = OrderType.BY_SERIAL_NUMBER;

	public static final String LABEL_POR_DFS_RANDOM_SEED = "Random seed used by POR DFS order";
	private static final int DEF_POR_DFS_RANDOM_SEED = 0;

	public static final String LABEL_POR_COINFLIP_MODE = "Coinflip budget determination mode";
	private static final CoinflipMode DEF_POR_COINFLIP_MODE = CoinflipMode.OFF;

	public static final String LABEL_POR_COINFLIP_PROB = "Coinflip probability value";
	private static final int DEF_POR_COINFLIP_PROB = 25;

	public static final String LABEL_POR_COINFLIP_SEED = "Coinflip random seed";
	private static final int DEF_POR_COINFLIP_SEED = 0;

	public static final String LABEL_POR_COINFLIP_INCREMENT = "Coinflip probability increment";
	private static final int DEF_POR_COINFLIP_INCREMENT = 0;

	public enum CoinflipMode {
		OFF, FALLBACK, PURE, COARSE
	}

	public static final String LABEL_CON_COM_CHECKER = "Additional conditional commutativity checking";
	private static final ConComChecker DEF_CON_COM_CHECKER = ConComChecker.NONE;

	public static final String LABEL_CON_COM_CHECKER_CRITERION = "Criterion for conditional commutativity checking";
	private static final ConComCheckerCriterion DEF_CON_COM_CHECKER_CRITERION = ConComCheckerCriterion.DEFAULT;

	public static final String LABEL_CON_COM_CHECKER_TRACECHECK_MODE = "TraceCheck mode for conditional commutativity";
	private static final ConComCheckerTraceCheckMode DEF_CON_COM_CHECKER_TRACECHECK_MODE =
			ConComCheckerTraceCheckMode.GENERATOR;

	public static final String LABEL_CON_COM_CHECKER_LIMITED_CHECKS_CRITERION =
			"Use limited checks (recommended for DFS)";
	private static final boolean DEF_CON_COM_CHECKER_LIMITED_CHECKS_CRITERION = false;

	public static final String LABEL_CON_COM_CHECKER_CRITERION_LIMIT = "Limit for limited checks";
	private static final int DEF_CON_COM_CHECKER_CRITERION_LIMIT = 1;

	public static final String LABEL_CON_COM_CHECKER_RANDOM_PROB = "Probability for random criterion as percentage";
	private static final int DEF_CON_COM_CHECKER_RANDOM_PROB = 100;

	public static final String LABEL_CON_COM_CHECKER_RANDOM_SEED = "Seed for random criterion";
	private static final int DEF_CON_COM_CHECKER_RANDOM_SEED = 123;

	public static final String LABEL_CON_COM_CHECKER_CONDITION_CRITERION =
			"Use condition criterion (recommended for programs with arrays)";
	private static final boolean DEF_CON_COM_CHECKER_CONDITION_CRITERION = false;

	// Settings for PetriAutomizer
	// ========================================================================

	public static final String LABEL_LOOPER_CHECK_PETRI = "Looper check in Petri net analysis";
	private static final LooperCheck DEF_LOOPER_CHECK_PETRI = LooperCheck.SYNTACTIC;

	public static final String LABEL_CONFIGURATION_ORDER = "Order on configurations for Petri net unfoldings";
	private static final EventOrderEnum DEF_CONFIGURATION_ORDER = EventOrderEnum.ERV;

	public static final String LABEL_CUTOFF = "cut-off requires same transition";
	private static final boolean DEF_CUTOFF = false;

	public static final String LABEL_BACKFOLDING = "Use backfolding";
	private static final boolean DEF_BACKFOLDING = false;

	// ========================================================================

	public static final String LABEL_INTERPROCEDURAL = "Interprocedural analysis (Nested Interpolants)";
	private static final boolean DEF_INTERPROCEDURAL = true;

	public static final String LABEL_STOP_AFTER_FIRST_VIOLATION = "Stop after first violation was found";
	private static final boolean DEF_STOP_AFTER_FIRST_VIOLATION = true;
	private static final String DESC_STOP_AFTER_FIRST_VIOLATION =
			"Stop the analysis after the first violation was found.";

	public static final String LABEL_CEGAR_RESTART_BEHAVIOUR = "CEGAR restart behaviour";
	private static final CegarRestartBehaviour DEF_CEGAR_RESTART_BEHAVIOUR = CegarRestartBehaviour.ONLY_ONE_CEGAR;
	private static final String DESC_CEGAR_RESTART_BEHAVIOUR =
			"Control how many error locations are analyzed by a single CEGAR loop: all, only one, or other subsets.";

	public static final String LABEL_ERROR_AUTOMATON_MODE = "Error locations removal mode";
	private static final ErrorAutomatonType DEF_ERROR_AUTOMATON_MODE = ErrorAutomatonType.SIMPLE_ERROR_AUTOMATON;
	private static final String DESC_ERROR_AUTOMATON_MODE = "If \"" + LABEL_CEGAR_RESTART_BEHAVIOUR + "\" is not "
			+ "\"ONE_CEGAR_PER_ERROR_LOCATION\", i.e., if one CEGAR loop analyzes multiple error locations, reachable "
			+ "error locations are removed by refinining the abstraction with an error automaton specified by this mode.";

	public static final String LABEL_FLOYD_HOARE_AUTOMATA_REUSE = "Reuse of Floyd-Hoare automata";
	private static final FloydHoareAutomataReuse DEF_FLOYD_HOARE_AUTOMATA_REUSE = FloydHoareAutomataReuse.NONE;
	private static final String DESC_FLOYD_HOARE_AUTOMATA_REUSE =
			"Try to re-use interpolant automata from input files and/or previous runs. " + FloydHoareAutomataReuse.NONE
					+ " disables the re-use, all other settings enable it. You can specifiy additional .ats files as"
					+ " input and the containing NWAs will be treated as additional interpolant automata. When "
					+ LABEL_STOP_AFTER_FIRST_VIOLATION
					+ " is false, this setting will additionally try to re-use the automata " + "from previous runs. "
					+ FloydHoareAutomataReuse.EAGER + " will compute the difference with the initial abstraction and "
					+ "all additional interpolant automatas before the first iteration of a run. "
					+ FloydHoareAutomataReuse.LAZY_IN_ORDER + " tries in each iteration after a potential "
					+ "counterexample is found if one of the re-usable interpolant automata accepts the counterexample. "
					+ "If this is the case, this automaton is substracted from the current abstraction and removed from "
					+ "the set of reusable interpolant automata.";

	public static final String LABEL_FLOYD_HOARE_AUTOMATA_REUSE_ENHANCEMENT =
			"Enhance during reuse of Floyd-Hoare automata";
	private static final FloydHoareAutomataReuseEnhancement DEF_FLOYD_HOARE_AUTOMATA_REUSE_ENHANCEMENT =
			FloydHoareAutomataReuseEnhancement.NONE;
	private static final String DESC_FLOYD_HOARE_AUTOMATA_REUSE_ENHANCEMENT =
			"Specifies how to compute successors on-demand for re-use interpolant automata.";

	public static final String LABEL_ARTIFACT = "Kind of artifact that is visualized";

	public static final String LABEL_WATCHITERATION = "Number of iteration whose artifact is visualized";
	private static final int DEF_WATCHITERATION = 1_000_000;

	public static final String LABEL_HOARE_POSITIONS = "Positions where we compute the Hoare Annotation";
	private static final HoareAnnotationPositions DEF_HOARE_POSITIONS = HoareAnnotationPositions.None;

	// Trace Check Solver
	// ========================================================================

	public static final String LABEL_SEPARATE_SOLVER = "Use separate solver for trace checks";
	private static final boolean DEF_SEPARATE_SOLVER = true;

	public static final String LABEL_SOLVER = RcfgPreferenceInitializer.LABEL_SOLVER;
	private static final SolverMode DEF_SOLVER = SolverMode.Internal_SMTInterpol;

	public static final String LABEL_ADDITIONAL_SMT_OPTIONS = RcfgPreferenceInitializer.LABEL_ADDITIONAL_SMT_OPTIONS;
	private static final Map<String, String> DEF_ADDITIONAL_SMT_OPTIONS =
			RcfgPreferenceInitializer.DEF_ADDITIONAL_SMT_OPTIONS;

	public static final String LABEL_USE_MINIMAL_UNSAT_CORE_ENUMERATION_FOR_SMTINTERPOL =
			"Use minimal unsat core enumeration";
	private static final boolean DEF_USE_MINIMAL_UNSAT_CORE_ENUMERATION_FOR_SMTINTERPOL = false;
	private static final String DESC_USE_MINIMAL_UNSAT_CORE_ENUMERATION_FOR_SMTINTERPOL =
			"Highly experimental. " + "Enable minimal unsat core enumeration with SMTInterpol. "
					+ "You can specify which heuristics should be used by setting appropriate SMT-LIB options. "
					+ "Contact Jochen Hoenicke or Leonard Fichtner for more information.";

	// ========================================================================

	public static final String LABEL_INTERPOLATED_LOCS = "Compute Interpolants along a Counterexample";
	private static final InterpolationTechnique DEF_INTERPOLANTS = InterpolationTechnique.ForwardPredicates;

	// Path Invariants
	// ========================================================================

	public static final String LABEL_NONLINEAR_CONSTRAINTS_IN_PATHINVARIANTS =
			"Use nonlinear constraints in PathInvariants";

	public static final String LABEL_UNSAT_CORES_IN_PATHINVARIANTS = "Use unsat cores in PathInvariants";

	public static final String LABEL_WEAKEST_PRECONDITION_IN_PATHINVARIANTS =
			"Use weakest precondition in PathInvariants";

	public static final String LABEL_ABSTRACT_INTERPRETATION_FOR_PATH_INVARIANTS =
			"Use abstract interpretation in PathInvariants";

	// ========================================================================

	public static final String LABEL_INTERPOLANTS_CONSOLIDATION = "Interpolants consolidation";

	public static final String LABEL_INTERPOLANT_AUTOMATON = "Interpolant automaton";

	public static final String LABEL_INTERPOLANT_AUTOMATON_ENHANCEMENT = "Interpolant automaton enhancement";

	// Automata dumping
	// ========================================================================

	public static final String LABEL_DUMPAUTOMATA = "Dump automata to files";
	private static final boolean DEF_DUMPAUTOMATA = false;

	public static final String LABEL_AUTOMATAFORMAT = "Output format of dumped automata";
	private static final Format DEF_AUTOMATAFORMAT = Format.ATS_NUMERATE;

	public static final String LABEL_DUMPPATH = "Dump automata to the following directory";
	private static final String DEF_DUMPPATH = ".";

	public static final String LABEL_DUMP_ONLY_REUSE = "Dump only reuse-automata";
	private static final boolean DEF_ONLY_REUSE = false;
	private static final String DESC_DUMP_ONLY_REUSE =
			"When dumping automata is enabled, we only dump the interpolant automaton and add to that file if it "
					+ "exists s.t. it can be reused by later verification runs.";

	// ========================================================================

	public static final String LABEL_HOARE_TRIPLE_CHECKS = "Hoare triple checks";

	public static final String LABEL_DIFFERENCE_SENWA = "DifferenceSenwa operation instead classical Difference";
	private static final boolean DEF_DIFFERENCE_SENWA = false;

	public static final String LABEL_MINIMIZE = "Minimization of abstraction";

	public static final String LABEL_ASSERT_CODEBLOCKS_INCREMENTALLY = "Assert CodeBlocks";

	public static final String LABEL_UNSAT_CORES = "Use unsat cores";

	public static final String LABEL_LIVE_VARIABLES = "Use live variables";

	public static final String LABEL_LANGUAGE_OPERATION = "LanguageOperation";

	public static final String LABEL_ABSINT_MODE = "Abstract interpretation Mode";
	private static final AbstractInterpretationMode DEF_ABSINT_MODE = AbstractInterpretationMode.NONE;

	public static final String LABEL_ABSINT_ALWAYS_REFINE = "Refine always when using abstract interpretation";
	private static final boolean DEF_ABSINT_ALWAYS_REFINE = false;

	public static final String LABEL_COMPUTE_COUNTEREXAMPLE = "Compute trace for counterexample result";
	private static final boolean DEF_COMPUTE_COUNTEREXAMPLE = true;
	private static final String DESC_COMPUTE_COUNTEREXAMPLE = null;

	public static final String LABEL_COMPUTE_INTERPOLANT_SEQUENCE_STATISTICS =
			"Compute statistics for interpolant sequences";
	private static final boolean DEF_COMPUTE_INTERPOLANT_SEQUENCE_STATISTICS = true;
	private static final String DESC_COMPUTE_INTERPOLANT_SEQUENCE_STATISTICS = null;

	public static final String LABEL_ERROR_TRACE_RELEVANCE_ANALYSIS_MODE =
			"Highlight relevant statements in error traces";
	private static final RelevanceAnalysisMode DEF_ERROR_TRACE_RELEVANCE_ANALYSIS_MODE = RelevanceAnalysisMode.NONE;
	private static final String DESC_ERROR_TRACE_RELEVANCE_ANALYSIS_MODE =
			"Analyse error traces and identify relevant statements. Warning: For programs with floats, arrays, or"
					+ " pointers this analysis may take a significant amount of time.";

	public static final String LABEL_ERROR_TRACE_ANGELIC_VERIFICATION_ACTIVE = "Angelic verification mode";
	private static final boolean DEF_ERROR_TRACE_ANGELIC_VERIFICATION_ACTIVE = false;
	private static final String DESC_ERROR_TRACE_ANGELIC_VERIFICATION_ACTIVE =
			"Assume that unspecified inputs (e.g., external functions) return \"safe\" values during error trace "
					+ "relevance analysis.";

	public static final String LABEL_SIMPLIFICATION_TECHNIQUE = "Simplification technique";
	private static final SimplificationTechnique DEF_SIMPLIFICATION_TECHNIQUE = SimplificationTechnique.SIMPLIFY_DDA2;

	public static final String LABEL_XNF_CONVERSION_TECHNIQUE = "Xnf conversion technique";
	private static final XnfConversionTechnique DEF_XNF_CONVERSION_TECHNIQUE =
			XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION;

	public static final String LABEL_COUNTEREXAMPLE_SEARCH_STRATEGY = "Counterexample search strategy";
	private static final CounterexampleSearchStrategy DEF_COUNTEREXAMPLE_SEARCH_STRATEGY =
			CounterexampleSearchStrategy.BFS;

	public static final String LABEL_REFINEMENT_STRATEGY = "Trace refinement strategy";
	private static final RefinementStrategy DEF_REFINEMENT_STRATEGY = RefinementStrategy.FIXED_PREFERENCES;

	public static final String LABEL_ACIP_REFINEMENT_STRATEGY =
			"Trace refinement strategy used in Accelerated Interpolation";
	private static final RefinementStrategy DEF_ACIP_REFINEMENT_STRATEGY = RefinementStrategy.FIXED_PREFERENCES;

	public static final String LABEL_REFINEMENT_STRATEGY_EXCEPTION_BLACKLIST = "Trace refinement exception blacklist";
	private static final RefinementStrategyExceptionBlacklist DEF_REFINEMENT_STRATEGY_EXCEPTION_BLACKLIST =
			RefinementStrategyExceptionBlacklist.DEPENDING;
	private static final String DESC_REFINEMENT_STRATEGY_EXCEPTION_BLACKLIST =
			"Sets the category of solver result for which the verification is aborted (even if another solver is "
					+ "available). When set to " + RefinementStrategyExceptionBlacklist.ALL
					+ ", every unusable solver result aborts the verification, if set to "
					+ RefinementStrategyExceptionBlacklist.NONE + " none of them do.";

	// Path Program Dumping
	// ========================================================================

	public static final String LABEL_DUMP_PATH_PROGRAM_IF_NOT_PERFECT =
			"Dump path programs if interpolant sequence is not perfect";

	public static final String LABEL_DUMP_PATH_PROGRAM_IF_ANALYZED_TOO_OFTEN =
			"Dump path programs if already analyzed N times";

	public static final String LABEL_DUMP_PATH_PROGRAM_STOP_MODE = "Stop after dumping path program";

	// ========================================================================

	public static final String DEF_EXTERNAL_SOLVER_COMMAND = RcfgPreferenceInitializer.Z3_DEFAULT;

	public static final String LABEL_USE_PREDICATE_TRIE_BASED_PREDICATE_UNIFIER =
			"Use predicate trie based predicate unification";
	public static final boolean DEF_USE_PREDICATE_TRIE_BASED_PREDICATE_UNIFIER = false;
	public static final String DESC_USE_PREDICATE_TRIE_BASED_PREDICATE_UNIFIER =
			"Use the newer predicate-trie based predicate unification algorithm.";

	// A* Heuristic
	// ========================================================================

	public static final String LABEL_HEURISTIC_EMPTINESS_CHECK = "Use heuristic emptiness check";
	private static final boolean DEF_HEURISTIC_EMPTINESS_CHECK = false;
	private static final String DESC_HEURISTIC_EMPTINESS_CHECK =
			"Use heuristics to traverse/explorew a NWA during the check emptiness";

	public static final String LABEL_HEURISTIC_EMPTINESS_CHECK_SCORING_METHOD =
			"Scoring method to use during heuristic emptiness check";
	private static final ScoringMethod DEF_HEURISTIC_EMPTINESS_CHECK_SCORING_METHOD = ScoringMethod.DAGSIZE;
	private static final String DESC_HEURISTIC_EMPTINESS_CHECK_SCORING_METHOD =
			"Defines what Scoring method is used to score outgoing transitions of a NWA during the emptiness check.";

	public static final String LABEL_HEURISTIC_EMPTINESS_CHECK_ASTAR_HEURISTIC =
			"AStar heuristic to use during heuristic emptiness check";
	private static final AStarHeuristic DEF_HEURISTIC_EMPTINESS_CHECK_ASTAR_HEURISTIC = AStarHeuristic.ZERO;
	private static final String DESC_HEURISTIC_EMPTINESS_CHECK_ASTAR_HEURISTIC =
			"Defines which Heuristic is used by AStar during exploration of a NWA during the emptiness check.";

	public static final String LABEL_HEURISTIC_EMPTINESS_CHECK_ASTAR_RANDOM_HEURISTIC_SEED =
			"AStar random heuristic seed";
	private static final Integer DEF_HEURISTIC_EMPTINESS_CHECK_ASTAR_RANDOM_HEURISTIC_SEED = 1337;
	private static final String DESC_HEURISTIC_EMPTINESS_CHECK_ASTAR_RANDOM_HEURISTIC_SEED =
			"Defines which seed is used for RANDOM_HALF and RANDOM_FULL heuristic";

	// ========================================================================

	public static final String LABEL_SMT_FEATURE_EXTRACTION = "Extract SMT features during analysis";
	private static final boolean DEF_SMT_FEATURE_EXTRACTION = false;
	private static final String DESC_SMT_FEATURE_EXTRACTION = "We Extract SMT features during analysis and dump them.";

	public static final String LABEL_SMT_FEATURE_EXTRACTION_DUMP_PATH = "SMT feature Extraction Dump Path.";
	private static final String DEF_SMT_FEATURE_EXTRACTION_DUMP_PATH = ".";
	private static final String DESC_SMT_FEATURE_EXTRACTION_DUMP_PATH =
			"We Extract SMT features during analysis and dump them to the given path";

	public static final String LABEL_OVERRIDE_INTERPOLANT_AUTOMATON =
			"Override the interpolant automaton setting of the refinement strategy";
	private static final boolean DEF_OVERRIDE_INTERPOLANT_AUTOMATON = false;

	public static final String LABEL_ASSERT_CODEBLOCKS_HEURISTIC_SCORING_METHOD =
			"Assert CodeBlocks Term Scoring Heuristic";
	private static final ScoringMethod DEF_ASSERT_CODEBLOCKS_HEURISTIC_SCORING_METHOD =
			AssertCodeBlockOrder.DEF_SCORING_METHOD;
	private static final String DESC_ASSERT_CODEBLOCKS_HEURISTIC_SCORING_METHOD =
			"if Assert CodeBlocks is set to SMT_FEATURE_HEURISTIC, each term in a trace is scored. This setting defines which scoring method is used to score traces";

	public static final String LABEL_ASSERT_CODEBLOCKS_HEURISTIC_PARTITIONING_STRATEGY =
			"Assert CodeBlocks Term Scoring Heuristic Partitioning Strategy";
	private static final SmtFeatureHeuristicPartitioningType DEF_ASSERT_CODEBLOCKS_HEURISTIC_PARTITIONING_STRATEGY =
			AssertCodeBlockOrder.DEF_PARTITIONING_STRATEGY;
	private static final String DESC_ASSERT_CODEBLOCKS_HEURISTIC_PARTITIONING_STRATEGY =
			"if Assert CodeBlocks is set to SMT_FEATURE_HEURISTIC, this setting defines which partitioning strategy is used.";

	public static final String LABEL_ACCELINTERPOL_LOOPACCELERATION_TECHNIQUE =
			"Loop acceleration method that is used by accelerated interpolation";
	private static final LoopAccelerators DEF_LOOPACCELERATION_TECHNIQUE = LoopAccelerators.FAST_UPR;
	private static final String DESC_ACCELINTERPOL_LOOPACCELERATION_TECHNIQUE = "Set the loop acceleration technique.";

	public static final String LABEL_ASSERT_CODEBLOCKS_HEURISTIC_NUM_PARTITIONS =
			"Assert CodeBlocks Term Scoring Heuristic number of partitions";
	private static final Integer DEF_ASSERT_CODEBLOCKS_HEURISTIC_NUM_PARTITIONS =
			AssertCodeBlockOrder.DEF_NUM_PARTITIONS;
	private static final String DESC_ASSERT_CODEBLOCKS_HEURISTIC_NUM_PARTITIONS =
			"If Assert CodeBlocks is set to SMT_FEATURE_HEURISTIC and partitioning strategy is FIXED_NUM_PARTITIONS, this setting defines the amount of partitions.";

	public static final String LABEL_ASSERT_CODEBLOCKS_HEURISTIC_SCORE_THRESHOLD =
			"Assert CodeBlocks Term Scoring Heuristic Score Threshold";
	private static final Double DEF_ASSERT_CODEBLOCKS_HEURISTIC_SCORE_THRESHOLD =
			AssertCodeBlockOrder.DEF_SCORE_THRESHOLD;
	private static final String DESC_ASSERT_CODEBLOCKS_HEURISTIC_SCORE_THRESHOLD =
			"If Assert CodeBlocks is set to SMT_FEATURE_HEURISTIC and partitioning strategy is THRESHOLD, two partitions are created, one partition contains all terms >= threshold  and one all terms < threshold";

	/**
	 * Constructor.
	 */
	public TraceAbstractionPreferenceInitializer() {
		super(Activator.PLUGIN_ID, "Automizer (Trace Abstraction)");
	}

	@Override
	protected BaseUltimatePreferenceItem[] initDefaultPreferences() {
		return new BaseUltimatePreferenceItem[] {
				new UltimatePreferenceItem<>(LABEL_INTERPROCEDURAL, DEF_INTERPROCEDURAL, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_STOP_AFTER_FIRST_VIOLATION, DEF_STOP_AFTER_FIRST_VIOLATION,
						DESC_STOP_AFTER_FIRST_VIOLATION, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_CEGAR_RESTART_BEHAVIOUR, DEF_CEGAR_RESTART_BEHAVIOUR,
						DESC_CEGAR_RESTART_BEHAVIOUR, PreferenceType.Combo, CegarRestartBehaviour.values()),
				new UltimatePreferenceItem<>(LABEL_ERROR_AUTOMATON_MODE, DEF_ERROR_AUTOMATON_MODE,
						DESC_ERROR_AUTOMATON_MODE, PreferenceType.Combo, ErrorAutomatonType.values()),

				new UltimatePreferenceItem<>(LABEL_READ_INITIAL_PROOF_ASSERTIONS_FROM_FILE,
						DEF_READ_INITIAL_PROOF_ASSERTIONS_FROM_FILE, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_FLOYD_HOARE_AUTOMATA_REUSE, DEF_FLOYD_HOARE_AUTOMATA_REUSE,
						DESC_FLOYD_HOARE_AUTOMATA_REUSE, PreferenceType.Combo, FloydHoareAutomataReuse.values()),
				new UltimatePreferenceItem<>(LABEL_FLOYD_HOARE_AUTOMATA_REUSE_ENHANCEMENT,
						DEF_FLOYD_HOARE_AUTOMATA_REUSE_ENHANCEMENT, DESC_FLOYD_HOARE_AUTOMATA_REUSE_ENHANCEMENT,
						PreferenceType.Combo, FloydHoareAutomataReuseEnhancement.values()),

				new UltimatePreferenceItemGroup("User Limits",
						new UltimatePreferenceItem<>(LABEL_USERLIMIT_ITERATIONS, DEF_USERLIMIT_ITERATIONS,
								DESC_USERLIMIT_ITERATIONS, PreferenceType.Integer,
								new IUltimatePreferenceItemValidator.IntegerValidator(0, 1_000_000)),
						new UltimatePreferenceItem<>(LABEL_USERLIMIT_TIME, DEF_USERLIMIT_TIME, DESC_USERLIMIT_TIME,
								PreferenceType.Integer, IUltimatePreferenceItemValidator.ONLY_POSITIVE),
						new UltimatePreferenceItem<>(LABEL_USERLIMIT_PATH_PROGRAM, DEF_USERLIMIT_PATH_PROGRAM,
								DESC_USERLIMIT_PATH_PROGRAM, PreferenceType.Integer,
								IUltimatePreferenceItemValidator.ONLY_POSITIVE),
						new UltimatePreferenceItem<>(LABEL_USERLIMIT_TRACE_HISTOGRAM, DEF_USERLIMIT_TRACE_HISTOGRAM,
								DESC_USERLIMIT_TRACE_HISTOGRAM, PreferenceType.Integer,
								IUltimatePreferenceItemValidator.ONLY_POSITIVE)),

				new UltimatePreferenceItem<>(LABEL_COMPUTE_COUNTEREXAMPLE, DEF_COMPUTE_COUNTEREXAMPLE,
						DESC_COMPUTE_COUNTEREXAMPLE, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_COMPUTE_INTERPOLANT_SEQUENCE_STATISTICS,
						DEF_COMPUTE_INTERPOLANT_SEQUENCE_STATISTICS, DESC_COMPUTE_INTERPOLANT_SEQUENCE_STATISTICS,
						PreferenceType.Boolean),

				new UltimatePreferenceItem<>(LABEL_ARTIFACT, Artifact.RCFG, PreferenceType.Combo, Artifact.values()),
				new UltimatePreferenceItem<>(LABEL_WATCHITERATION, DEF_WATCHITERATION, PreferenceType.Integer,
						new IUltimatePreferenceItemValidator.IntegerValidator(0, 1_0000_000)),
				new UltimatePreferenceItem<>(LABEL_HOARE_POSITIONS, DEF_HOARE_POSITIONS, PreferenceType.Combo,
						HoareAnnotationPositions.values()),

				new UltimatePreferenceItem<>(LABEL_USE_PREDICATE_TRIE_BASED_PREDICATE_UNIFIER,
						DEF_USE_PREDICATE_TRIE_BASED_PREDICATE_UNIFIER, DESC_USE_PREDICATE_TRIE_BASED_PREDICATE_UNIFIER,
						PreferenceType.Boolean),

				new UltimatePreferenceItemGroup("Trace Check Solver",
						new UltimatePreferenceItem<>(LABEL_SEPARATE_SOLVER, DEF_SEPARATE_SOLVER,
								PreferenceType.Boolean),
						new UltimatePreferenceItem<>(LABEL_SOLVER, DEF_SOLVER, PreferenceType.Combo,
								SolverMode.values()),
						new UltimatePreferenceItem<>(RcfgPreferenceInitializer.LABEL_FAKE_NON_INCREMENTAL_SCRIPT,
								RcfgPreferenceInitializer.DEF_FAKE_NON_INCREMENTAL_SCRIPT, PreferenceType.Boolean),
						new UltimatePreferenceItem<>(RcfgPreferenceInitializer.LABEL_EXT_SOLVER_COMMAND,
								DEF_EXTERNAL_SOLVER_COMMAND, PreferenceType.String),
						new UltimatePreferenceItem<>(RcfgPreferenceInitializer.LABEL_EXT_SOLVER_LOGIC,
								RcfgPreferenceInitializer.DEF_EXT_SOLVER_LOGIC, PreferenceType.String),
						new UltimatePreferenceItem<>(RcfgPreferenceInitializer.LABEL_DUMP_TO_FILE, Boolean.FALSE,
								PreferenceType.Boolean),
						new UltimatePreferenceItem<>(RcfgPreferenceInitializer.LABEL_DUMP_PATH,
								RcfgPreferenceInitializer.DEF_DUMP_PATH, PreferenceType.Directory),
						new UltimatePreferenceItem<>(RcfgPreferenceInitializer.LABEL_COMPRESS_SMT_DUMP_FILE, false,
								RcfgPreferenceInitializer.DESC_COMPRESS_SMT_DUMP_FILE, PreferenceType.Boolean),
						new UltimatePreferenceItem<>(LABEL_USE_MINIMAL_UNSAT_CORE_ENUMERATION_FOR_SMTINTERPOL,
								DEF_USE_MINIMAL_UNSAT_CORE_ENUMERATION_FOR_SMTINTERPOL,
								DESC_USE_MINIMAL_UNSAT_CORE_ENUMERATION_FOR_SMTINTERPOL, PreferenceType.Boolean),
						new UltimatePreferenceItem<>(LABEL_ADDITIONAL_SMT_OPTIONS, DEF_ADDITIONAL_SMT_OPTIONS,
								PreferenceType.KeyValue)),

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
						AssertCodeBlockOrderType.NOT_INCREMENTALLY, PreferenceType.Combo,
						AssertCodeBlockOrderType.values()),
				new UltimatePreferenceItem<>(LABEL_ASSERT_CODEBLOCKS_HEURISTIC_SCORING_METHOD,
						DEF_ASSERT_CODEBLOCKS_HEURISTIC_SCORING_METHOD, DESC_ASSERT_CODEBLOCKS_HEURISTIC_SCORING_METHOD,
						PreferenceType.Combo, ScoringMethod.values()),
				new UltimatePreferenceItem<>(LABEL_ASSERT_CODEBLOCKS_HEURISTIC_PARTITIONING_STRATEGY,
						DEF_ASSERT_CODEBLOCKS_HEURISTIC_PARTITIONING_STRATEGY,
						DESC_ASSERT_CODEBLOCKS_HEURISTIC_PARTITIONING_STRATEGY, PreferenceType.Combo,
						SmtFeatureHeuristicPartitioningType.values()),
				new UltimatePreferenceItem<>(LABEL_ASSERT_CODEBLOCKS_HEURISTIC_NUM_PARTITIONS,
						DEF_ASSERT_CODEBLOCKS_HEURISTIC_NUM_PARTITIONS, DESC_ASSERT_CODEBLOCKS_HEURISTIC_NUM_PARTITIONS,
						PreferenceType.Integer, new IUltimatePreferenceItemValidator.IntegerValidator(0, 1_0000_000)),
				new UltimatePreferenceItem<>(LABEL_ASSERT_CODEBLOCKS_HEURISTIC_SCORE_THRESHOLD,
						DEF_ASSERT_CODEBLOCKS_HEURISTIC_SCORE_THRESHOLD,
						DESC_ASSERT_CODEBLOCKS_HEURISTIC_SCORE_THRESHOLD, PreferenceType.Double,
						new IUltimatePreferenceItemValidator.DoubleValidator(0.5, 1.0)),
				new UltimatePreferenceItem<>(LABEL_OVERRIDE_INTERPOLANT_AUTOMATON, DEF_OVERRIDE_INTERPOLANT_AUTOMATON,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_INTERPOLANT_AUTOMATON, InterpolantAutomaton.STRAIGHT_LINE,
						PreferenceType.Combo, InterpolantAutomaton.values()),
				new UltimatePreferenceItem<>(LABEL_INTERPOLANT_AUTOMATON_ENHANCEMENT,
						InterpolantAutomatonEnhancement.PREDICATE_ABSTRACTION, PreferenceType.Combo,
						InterpolantAutomatonEnhancement.values()),
				new UltimatePreferenceItem<>(LABEL_HOARE_TRIPLE_CHECKS, HoareTripleChecks.INCREMENTAL,
						PreferenceType.Combo, HoareTripleChecks.values()),

				new UltimatePreferenceItemGroup("Automata Dumping",
						new UltimatePreferenceItem<>(LABEL_DUMPAUTOMATA, DEF_DUMPAUTOMATA, PreferenceType.Boolean),
						new UltimatePreferenceItem<>(LABEL_AUTOMATAFORMAT, DEF_AUTOMATAFORMAT, PreferenceType.Combo,
								Format.values()),
						new UltimatePreferenceItem<>(LABEL_DUMPPATH, DEF_DUMPPATH, PreferenceType.Directory),
						new UltimatePreferenceItem<>(LABEL_DUMP_ONLY_REUSE, DEF_ONLY_REUSE, DESC_DUMP_ONLY_REUSE,
								PreferenceType.Boolean)),

				new UltimatePreferenceItem<>(LABEL_LANGUAGE_OPERATION, LanguageOperation.DIFFERENCE,
						PreferenceType.Combo, LanguageOperation.values()),
				new UltimatePreferenceItem<>(LABEL_DIFFERENCE_SENWA, DEF_DIFFERENCE_SENWA, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_MINIMIZE, Minimization.MINIMIZE_SEVPA, PreferenceType.Combo,
						Minimization.values()),
				new UltimatePreferenceItem<>(LABEL_ABSINT_MODE, DEF_ABSINT_MODE, PreferenceType.Combo,
						AbstractInterpretationMode.values()),
				new UltimatePreferenceItem<>(LABEL_ABSINT_ALWAYS_REFINE, DEF_ABSINT_ALWAYS_REFINE,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_ERROR_TRACE_RELEVANCE_ANALYSIS_MODE,
						DEF_ERROR_TRACE_RELEVANCE_ANALYSIS_MODE, DESC_ERROR_TRACE_RELEVANCE_ANALYSIS_MODE,
						PreferenceType.Combo, RelevanceAnalysisMode.values()),
				new UltimatePreferenceItem<>(LABEL_ERROR_TRACE_ANGELIC_VERIFICATION_ACTIVE,
						DEF_ERROR_TRACE_ANGELIC_VERIFICATION_ACTIVE, DESC_ERROR_TRACE_ANGELIC_VERIFICATION_ACTIVE,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_SIMPLIFICATION_TECHNIQUE, DEF_SIMPLIFICATION_TECHNIQUE,
						PreferenceType.Combo, SimplificationTechnique.values()),
				new UltimatePreferenceItem<>(LABEL_XNF_CONVERSION_TECHNIQUE, DEF_XNF_CONVERSION_TECHNIQUE,
						PreferenceType.Combo, XnfConversionTechnique.values()),
				new UltimatePreferenceItem<>(LABEL_COUNTEREXAMPLE_SEARCH_STRATEGY, DEF_COUNTEREXAMPLE_SEARCH_STRATEGY,
						PreferenceType.Combo, CounterexampleSearchStrategy.values()),
				new UltimatePreferenceItem<>(LABEL_REFINEMENT_STRATEGY, DEF_REFINEMENT_STRATEGY, PreferenceType.Combo,
						RefinementStrategy.values()),
				new UltimatePreferenceItem<>(LABEL_ACIP_REFINEMENT_STRATEGY, DEF_ACIP_REFINEMENT_STRATEGY,
						PreferenceType.Combo, RefinementStrategy.values()),
				new UltimatePreferenceItem<>(LABEL_REFINEMENT_STRATEGY_EXCEPTION_BLACKLIST,
						DEF_REFINEMENT_STRATEGY_EXCEPTION_BLACKLIST, DESC_REFINEMENT_STRATEGY_EXCEPTION_BLACKLIST,
						PreferenceType.Combo, RefinementStrategyExceptionBlacklist.values()),

				new UltimatePreferenceItemGroup("Heuristic Emptiness Check",
						new UltimatePreferenceItem<>(LABEL_HEURISTIC_EMPTINESS_CHECK, DEF_HEURISTIC_EMPTINESS_CHECK,
								DESC_HEURISTIC_EMPTINESS_CHECK, PreferenceType.Boolean),
						new UltimatePreferenceItem<>(LABEL_HEURISTIC_EMPTINESS_CHECK_ASTAR_HEURISTIC,
								DEF_HEURISTIC_EMPTINESS_CHECK_ASTAR_HEURISTIC,
								DESC_HEURISTIC_EMPTINESS_CHECK_ASTAR_HEURISTIC, PreferenceType.Combo,
								AStarHeuristic.values()),
						new UltimatePreferenceItem<>(LABEL_HEURISTIC_EMPTINESS_CHECK_ASTAR_RANDOM_HEURISTIC_SEED,
								DEF_HEURISTIC_EMPTINESS_CHECK_ASTAR_RANDOM_HEURISTIC_SEED,
								DESC_HEURISTIC_EMPTINESS_CHECK_ASTAR_RANDOM_HEURISTIC_SEED, PreferenceType.Integer,
								new IUltimatePreferenceItemValidator.IntegerValidator(0, 1_000_000)),
						new UltimatePreferenceItem<>(LABEL_HEURISTIC_EMPTINESS_CHECK_SCORING_METHOD,
								DEF_HEURISTIC_EMPTINESS_CHECK_SCORING_METHOD,
								DESC_HEURISTIC_EMPTINESS_CHECK_SCORING_METHOD, PreferenceType.Combo,
								ScoringMethod.values())),

				new UltimatePreferenceItem<>(LABEL_ACCELINTERPOL_LOOPACCELERATION_TECHNIQUE,
						DEF_LOOPACCELERATION_TECHNIQUE, DESC_ACCELINTERPOL_LOOPACCELERATION_TECHNIQUE,
						PreferenceType.Combo, LoopAccelerators.values()),
				new UltimatePreferenceItem<>(LABEL_SMT_FEATURE_EXTRACTION, DEF_SMT_FEATURE_EXTRACTION,
						DESC_SMT_FEATURE_EXTRACTION, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_SMT_FEATURE_EXTRACTION_DUMP_PATH,
						DEF_SMT_FEATURE_EXTRACTION_DUMP_PATH, DESC_SMT_FEATURE_EXTRACTION_DUMP_PATH,
						PreferenceType.Directory),

				new UltimatePreferenceItem<>(LABEL_DUMP_PATH_PROGRAM_IF_NOT_PERFECT, false, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_DUMP_PATH_PROGRAM_IF_ANALYZED_TOO_OFTEN, 0, PreferenceType.Integer),
				new UltimatePreferenceItem<>(LABEL_DUMP_PATH_PROGRAM_STOP_MODE, PathProgramDumpStop.AFTER_FIRST_DUMP,
						PreferenceType.Combo, PathProgramDumpStop.values()),
				getConcurrencySettings() };
	}

	public UltimatePreferenceItemContainer getConcurrencySettings() {
		return new UltimatePreferenceItemContainer("Concurrent Programs",
				new UltimatePreferenceItem<>(LABEL_ORDER_OF_ERROR_LOCATIONS, DEF_ORDER_OF_ERROR_LOCATIONS,
						DESC_ORDER_OF_ERROR_LOCATIONS, PreferenceType.Combo, OrderOfErrorLocations.values()),
				new UltimatePreferenceItem<>(LABEL_CONCURRENCY, DEF_CONCURRENCY, PreferenceType.Combo,
						Concurrency.values()),
				new UltimatePreferenceItem<>(LABEL_MCR_REFINEMENT_STRATEGY, DEF_MCR_REFINEMENT_STRATEGY,
						PreferenceType.Combo, RefinementStrategy.values()),
				new UltimatePreferenceItem<>(LABEL_MCR_INTERPOLANT_METHOD, DEF_MCR_INTERPOLANT_METHOD,
						PreferenceType.Combo, McrInterpolantMethod.values()),

				new UltimatePreferenceItemGroup("PetriAutomizer",
						"These settings are only relevant if \"" + LABEL_CONCURRENCY + "\" is set to \""
								+ Concurrency.PETRI_NET + "\".",
						new UltimatePreferenceItem<>(LABEL_CONFIGURATION_ORDER, DEF_CONFIGURATION_ORDER,
								PreferenceType.Combo, EventOrderEnum.values()),
						new UltimatePreferenceItem<>(LABEL_CUTOFF, DEF_CUTOFF, PreferenceType.Boolean),
						new UltimatePreferenceItem<>(LABEL_BACKFOLDING, DEF_BACKFOLDING, PreferenceType.Boolean),
						new UltimatePreferenceItem<>(LABEL_LOOPER_CHECK_PETRI, DEF_LOOPER_CHECK_PETRI,
								PreferenceType.Combo, LooperCheck.values())),

				getPORSettings(), getPetriLbeSettings());
	}

	public UltimatePreferenceItemContainer getPORSettings() {
		return new UltimatePreferenceItemContainer("Partial Order Reduction (GemCutter)",
				new UltimatePreferenceItem<>(LABEL_POR_ONESHOT, DEF_POR_ONESHOT, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_POR_MODE, DEF_POR_MODE, PreferenceType.Combo,
						PartialOrderMode.values()),

				new UltimatePreferenceItem<>(LABEL_POR_DFS_ORDER, DEF_POR_DFS_ORDER, PreferenceType.Combo,
						OrderType.values()),
				new UltimatePreferenceItem<>(LABEL_POR_DFS_RANDOM_SEED, DEF_POR_DFS_RANDOM_SEED,
						PreferenceType.Integer),

				new UltimatePreferenceItem<>(LABEL_POR_NUM_INDEPENDENCE, DEF_POR_NUM_INDEPENDENCE,
						PreferenceType.Integer),
				new UltimatePreferenceItem<>(LABEL_DUMP_INDEPENDENCE_SCRIPT, DEF_DUMP_INDEPENDENCE_SCRIPT,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_INDEPENDENCE_SCRIPT_DUMP_PATH, DEF_INDEPENDENCE_SCRIPT_DUMP_PATH,
						PreferenceType.Directory),

				// TODO introduce a group or similar
				new UltimatePreferenceItem<>(LABEL_CON_COM_CHECKER, DEF_CON_COM_CHECKER, PreferenceType.Combo,
						ConComChecker.values()),
				new UltimatePreferenceItem<>(LABEL_CON_COM_CHECKER_CRITERION, DEF_CON_COM_CHECKER_CRITERION,
						PreferenceType.Combo, ConComCheckerCriterion.values()),
				new UltimatePreferenceItem<>(LABEL_CON_COM_CHECKER_TRACECHECK_MODE, DEF_CON_COM_CHECKER_TRACECHECK_MODE,
						PreferenceType.Combo, ConComCheckerTraceCheckMode.values()),
				new UltimatePreferenceItem<>(LABEL_CON_COM_CHECKER_LIMITED_CHECKS_CRITERION,
						DEF_CON_COM_CHECKER_LIMITED_CHECKS_CRITERION, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_CON_COM_CHECKER_CRITERION_LIMIT, DEF_CON_COM_CHECKER_CRITERION_LIMIT,
						PreferenceType.Integer),
				new UltimatePreferenceItem<>(LABEL_CON_COM_CHECKER_RANDOM_PROB, DEF_CON_COM_CHECKER_RANDOM_PROB,
						PreferenceType.Integer),
				new UltimatePreferenceItem<>(LABEL_CON_COM_CHECKER_RANDOM_SEED, DEF_CON_COM_CHECKER_RANDOM_SEED,
						PreferenceType.Integer),
				new UltimatePreferenceItem<>(LABEL_CON_COM_CHECKER_CONDITION_CRITERION,
						DEF_CON_COM_CHECKER_CONDITION_CRITERION, PreferenceType.Boolean),

				getIndependenceSettings(0),

				getIndependenceSettings(1),

				getIndependenceSettings(2),

				new UltimatePreferenceItemGroup("Stratified Commutativity: Budget Function",
						new UltimatePreferenceItem<>(LABEL_POR_COINFLIP_MODE, DEF_POR_COINFLIP_MODE,
								PreferenceType.Combo, CoinflipMode.values()),
						new UltimatePreferenceItem<>(LABEL_POR_COINFLIP_PROB, DEF_POR_COINFLIP_PROB,
								PreferenceType.Integer, new IUltimatePreferenceItemValidator.IntegerValidator(0, 100)),
						new UltimatePreferenceItem<>(LABEL_POR_COINFLIP_INCREMENT, DEF_POR_COINFLIP_INCREMENT,
								PreferenceType.Integer),
						new UltimatePreferenceItem<>(LABEL_POR_COINFLIP_SEED, DEF_POR_COINFLIP_SEED,
								PreferenceType.Integer)));
	}

	public UltimatePreferenceItemContainer getPetriLbeSettings() {
		return new UltimatePreferenceItemContainer("Petri LBE (Lipton Reduction)",
				new UltimatePreferenceItem<>(LABEL_PETRI_LBE_ONESHOT, DEF_PETRI_LBE_ONESHOT, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_INDEPENDENCE_PLBE, DEF_INDEPENDENCE_PLBE, PreferenceType.Combo,
						IndependenceType.values()),
				new UltimatePreferenceItem<>(LABEL_SEMICOMM_PLBE, DEF_SEMICOMM_PLBE, PreferenceType.Boolean));
	}

	public UltimatePreferenceItemGroup getIndependenceSettings(final int index) {
		final var label =
				getSuffixedLabel("Independence Relation", index) + (index == 0 ? "" : " (Stratified Commutativity)");
		return new UltimatePreferenceItemGroup(label,
				new UltimatePreferenceItem<>(getSuffixedLabel(LABEL_INDEPENDENCE_POR, index),
						IndependenceSettings.DEFAULT_INDEPENDENCE_TYPE, PreferenceType.Combo,
						IndependenceType.values()),
				new UltimatePreferenceItem<>(getSuffixedLabel(LABEL_POR_ABSTRACTION, index),
						IndependenceSettings.DEFAULT_ABSTRACTION_TYPE, PreferenceType.Combo, AbstractionType.values()),
				new UltimatePreferenceItem<>(getSuffixedLabel(LABEL_COND_POR, index),
						IndependenceSettings.DEFAULT_USE_CONDITIONAL, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(getSuffixedLabel(LABEL_SEMICOMM_POR, index),
						IndependenceSettings.DEFAULT_USE_SEMICOMMUTATIVITY, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(getSuffixedLabel(LABEL_INDEPENDENCE_SOLVER_POR, index),
						IndependenceSettings.DEFAULT_SOLVER, PreferenceType.Combo, ExternalSolver.values()),
				new UltimatePreferenceItem<>(getSuffixedLabel(LABEL_INDEPENDENCE_SOLVER_TIMEOUT_POR, index),
						(int) IndependenceSettings.DEFAULT_SOLVER_TIMEOUT, PreferenceType.Integer));
	}

	public static String getSuffixedLabel(final String label, final int index) {
		if (index == 0) {
			return label;
		}
		return label + " #" + (index + 1);
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
		CANONICAL, STRAIGHT_LINE, TOTALINTERPOLATION, TOTALINTERPOLATION2, ABSTRACT_INTERPRETATION, MCR
	}

	/**
	 * Minimization mode.
	 */
	public enum Minimization {
		NONE, MINIMIZE_SEVPA, SHRINK_NWA, DFA_HOPCROFT_ARRAYS, DFA_HOPCROFT_LISTS, NWA_SIZE_BASED_PICKER, NWA_MAX_SAT,
		NWA_MAX_SAT2, NWA_COMBINATOR_PATTERN, NWA_COMBINATOR_EVERY_KTH, RAQ_DIRECT_SIMULATION, RAQ_DIRECT_SIMULATION_B,
		NWA_OVERAPPROXIMATION, NWA_COMBINATOR_MULTI_DEFAULT, NWA_COMBINATOR_MULTI_SIMULATION, DELAYED_SIMULATION,
		FAIR_SIMULATION_WITH_SCC, FAIR_SIMULATION_WITHOUT_SCC, FAIR_DIRECT_SIMULATION, RAQ_DELAYED_SIMULATION,
		RAQ_DELAYED_SIMULATION_B, FULLMULTIPEBBLE_DELAYED_SIMULATION, FULLMULTIPEBBLE_DIRECT_SIMULATION,
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
		 * Strategy that reads the information from the settings. It always uses only one trace check and one
		 * interpolation generator.
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
		 * Integer strategy that tries Craig interpolation with SMTInterpol, SP/WP with Z3 and CVC4 with a high
		 * interpolant threshold.
		 */
		PENGUIN,
		/**
		 * Bitvector strategy that tries SP/WP with CVC4, Z3 and Mathsat with a low interpolant threshold
		 */
		WALRUS,
		/**
		 * Light-weight integer strategy that first tries to obtain craig interpolants with SMTInterpol and then Z3 with
		 * FP.
		 */
		CAMEL,
		/**
		 * Even more light-weight than {@link #CAMEL}. This strategy is exactly like {@link #CAMEL} but does not use any
		 * assertion order modulation.
		 */
		CAMEL_NO_AM,
		/**
		 * Like {@link #CAMEL_NO_AM}, but only uses {@link AssertCodeBlockOrderType#SMT_FEATURE_HEURISTIC} as assertion
		 * order.
		 */
		CAMEL_SMT_AM,
		/**
		 * Like {@link #CAMEL}, but only uses WP.
		 */
		CAMEL_BP_ONLY,
		/**
		 * Like {@link #CAMEL_NO_AM}, but continues as soon as some interpolants are available.
		 */
		LIZARD,
		/**
		 * An integer strategy without assertion order modulation using SMTInterpol with interpolation, Z3 with FP, and
		 * Mathsat with FP. This strategy is used by ReqChecker.
		 */
		BADGER,
		/**
		 * Bitvector strategy that tries SP/WP with CVC4, Z3 and Mathsat with a low interpolant threshold
		 */
		WOLF,
		/**
		 * Bitvector strategy similar to {@link #WOLF}, but no {@link AssertCodeBlockOrder} for Mathsat, and
		 * {@link InterpolationTechnique#FPandBPonlyIfFpWasNotPerfect} for all solvers.
		 */
		BEAR,
		/**
		 * Heavy-weight bitvector strategy that tries SP with CVC4, Z3 and Mathsat with a high interpolant threshold
		 */
		WARTHOG,
		/**
		 * Strategy like {@link #WARTHOG} but without assertion order modulation.
		 */
		WARTHOG_NO_AM,
		/**
		 * Heavy-weight integer strategy that tries craig interpolation with SMTInterpol and Z3 followed by SP/WP with
		 * Z3 with a high interpolant threshold.
		 */
		MAMMOTH,
		/**
		 * Strategy like {@link #MAMMOTH} but without assertion order modulation.
		 */
		MAMMOTH_NO_AM,
		/**
		 * Strategy for benchmarking purposes only: it first uses SMTInterpol with Craig interpolation and disabled
		 * array interpolation, then SMTInterpol with FP.
		 */
		SMTINTERPOL,
		/**
		 * SMTINTERPOL strategy for POR using sleep sets.
		 */
		// TODO Why do we need this?!
		SMTINTERPOLSLEEPSETPOR,
		/**
		 * Strategy that first tries SMTInterpol and then PDR.
		 */
		DACHSHUND,
		/**
		 * Strategy that is exactly like {@link #TAIPAN}, but uses Sifa instead of abstract interpretation.
		 */
		SIFA_TAIPAN,
		/**
		 * Strategy that is exactly like {@link #TOOTHLESS_TAIPAN}, but uses Sifa instead of abstract interpretation.
		 */
		TOOTHLESS_SIFA_TAIPAN,
		/**
		 * Maximal Causality reduction strategy
		 */
		MCR,

		/**
		 * Use accelerated interpolation and some other, nested strategy
		 */
		ACCELERATED_INTERPOLATION,

		/**
		 * Use loop acceleration in combination with the fixed preferences
		 */
		ACCELERATED_TRACE_CHECK
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

	public enum MultiPropertyMode {
		STOP_AFTER_FIRST_VIOLATION, CHECK_EACH_PROPERTY_SEPARATELY, CHECK_ALL_PROPERTIES_REFINE_WITH_VIOLATIONS,
	}

	/**
	 * Relevance analysis mode.
	 *
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	public enum RelevanceAnalysisMode {
		/**
		 * No analysis.
		 */
		NONE,
		/**
		 * Single-trace analysis.
		 */
		SINGLE_TRACE,
		/**
		 * Multi-trace analysis.
		 */
		MULTI_TRACE,
	}

	public enum McrInterpolantMethod {
		WP, SP
	}

	public enum OrderOfErrorLocations {
		INSUFFICIENT_FIRST, PROGRAM_FIRST, TOGETHER
	}

	public enum PathProgramDumpStop {
		NEVER, AFTER_FIRST_DUMP, BEFORE_FIRST_DUPLICATE
	}

	public enum ConComChecker {
		NONE, DFS, IA, BOTH, COUNTEREXAMPLE
	}

	public enum ConComCheckerCriterion {
		DEFAULT, RANDOM, SLEEP_SET, FORWARD, LOOP
	}

	public enum ConComCheckerTraceCheckMode {
		GENERATOR, GENERATOR_WITH_CONTEXT, SYMBOLIC_RELATION
	}
}
