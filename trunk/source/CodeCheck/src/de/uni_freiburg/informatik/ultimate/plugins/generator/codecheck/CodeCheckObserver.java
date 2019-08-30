/*
 * Copyright (C) 2013-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Mostafa Mahmoud Amin
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE CodeCheck plug-in.
 *
 * The ULTIMATE CodeCheck plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CodeCheck plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CodeCheck plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CodeCheck plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CodeCheck plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeMap;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.WitnessInvariant;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.GenericResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.InvariantResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.PositiveResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ResultUtil;
import de.uni_freiburg.informatik.ultimate.core.lib.results.StatisticsResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TimeoutResultAtElement;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovabilityReason;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovableResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithSeverity.Severity;
import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractInterpretationResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgElement;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.DagSizePrinter;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.biesenb.BPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.UnsatCores;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.AbstractInterpreter;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AnnotatedProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AppEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AppHyperEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.ImpRootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.RCFG2AnnotatedRCFG;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.emptinesscheck.IEmptinessCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.emptinesscheck.NWAEmptinessCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.impulse.ImpulseChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.kojak.UltimateChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.CodeCheckPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.CodeCheckPreferenceInitializer.Checker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.CodeCheckPreferenceInitializer.EdgeCheckOptimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.CodeCheckPreferenceInitializer.PredicateUnification;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.CodeCheckPreferenceInitializer.RedirectionStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.CachingHoareTripleCheckerMap;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EfficientHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolantConsolidation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolatingTraceCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolatingTraceCheckCraig;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckSpWp;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckUtils;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class CodeCheckObserver implements IUnmanagedObserver {

	private static final boolean OUTPUT_HOARE_ANNOTATION = true;
	private static final SimplificationTechnique SIMPLIFICATION_TECHNIQUE = SimplificationTechnique.SIMPLIFY_DDA;
	private static final XnfConversionTechnique XNF_CONVERSION_TECHNIQUE =
			XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION;

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	private IPredicateUnifier mPredicateUnifier;

	private IIcfg<IcfgLocation> mOriginalRoot;
	private ImpRootNode mGraphRoot;

	private CodeCheckSettings mGlobalSettings;

	private CfgSmtToolkit mCsToolkit;

	private GraphWriter mGraphWriter;
	private Collection<IcfgLocation> mErrNodesOfAllProc;

	private boolean mLoopForever = true;
	private int mIterationsLimit = -1;
	private PredicateFactory mPredicateFactory;

	CodeCheckObserver(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	/**
	 * Initialize all the required objects in the implementation.
	 *
	 * @param root
	 * @return
	 */
	private boolean initialize(final IIcfg<IcfgLocation> root) {
		if (!root.getCfgSmtToolkit().getConcurrencyInformation().getThreadInstanceMap().isEmpty()) {
			throw new UnsupportedOperationException("Concurrent programs are currently unsupported");
		}

		readPreferencePage();
		mOriginalRoot = root;
		mCsToolkit = mOriginalRoot.getCfgSmtToolkit();
		mPredicateFactory = new PredicateFactory(mServices, mCsToolkit.getManagedScript(), mCsToolkit.getSymbolTable());

		if (mServices.getPreferenceProvider(Activator.PLUGIN_ID)
				.getBoolean(CodeCheckPreferenceInitializer.LABEL_USE_PREDICATE_TRIE_BASED_PREDICATE_UNIFIER)) {
			mPredicateUnifier = new BPredicateUnifier(mServices, mLogger, mCsToolkit.getManagedScript(),
					mPredicateFactory, mOriginalRoot.getCfgSmtToolkit().getSymbolTable());
		} else {
			mPredicateUnifier = new PredicateUnifier(mLogger, mServices, mCsToolkit.getManagedScript(),
					mPredicateFactory, mOriginalRoot.getCfgSmtToolkit().getSymbolTable(), SIMPLIFICATION_TECHNIQUE,
					XNF_CONVERSION_TECHNIQUE);
		}

		final Map<String, Set<IcfgLocation>> proc2errNodes = mOriginalRoot.getProcedureErrorNodes();
		mErrNodesOfAllProc = new ArrayList<>();
		for (final Set<IcfgLocation> errNodeOfProc : proc2errNodes.values()) {
			mErrNodesOfAllProc.addAll(errNodeOfProc);
		}

		mGraphWriter = new GraphWriter(mLogger, mGlobalSettings.getDotGraphPath(), true, true, true);

		// AI Module
		final boolean usePredicatesFromAbstractInterpretation = mGlobalSettings.getUseAbstractInterpretation();
		Map<IcfgLocation, Term> initialPredicates = null;
		if (usePredicatesFromAbstractInterpretation) {

			// Run for 20% of the complete time.
			final IProgressAwareTimer timer = mServices.getProgressMonitorService().getChildTimer(0.2);

			final IAbstractInterpretationResult<?, IcfgEdge, IcfgLocation> result =
					AbstractInterpreter.runFuture(mOriginalRoot, timer, mServices, false, mLogger);

			if (result == null) {
				mLogger.warn(
						"was not able to retrieve initial predicates from abstract interpretation --> wrong toolchain?? (using \"true\")");
			} else {
				initialPredicates = result.getLoc2Term().entrySet().stream()
						.collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue));
			}
		}
		// End AI Module

		final RCFG2AnnotatedRCFG r2ar = new RCFG2AnnotatedRCFG(mCsToolkit, mPredicateFactory, mLogger,
				mPredicateUnifier.getTruePredicate(), initialPredicates);
		mGraphRoot = r2ar.convert(mOriginalRoot);

		removeSummaryEdges();
		mIterationsLimit = mGlobalSettings.getIterations();
		mLoopForever = mIterationsLimit == -1;

		return false;
	}

	private CodeChecker createCodeChecker() {
		final IHoareTripleChecker edgeChecker = createHoareTripleChecker();
		if (mGlobalSettings.getChecker() == Checker.IMPULSE) {
			return new ImpulseChecker(mCsToolkit, mOriginalRoot, mGraphRoot, mGraphWriter, edgeChecker,
					mPredicateUnifier, mLogger, mGlobalSettings);
		}
		return new UltimateChecker(mCsToolkit, mOriginalRoot, mGraphRoot, mGraphWriter, edgeChecker, mPredicateUnifier,
				mLogger, mGlobalSettings);
	}

	private IHoareTripleChecker createHoareTripleChecker() {
		final IHoareTripleChecker smtBasedHoareTripleChecker = new IncrementalHoareTripleChecker(mCsToolkit, false);
		final IHoareTripleChecker protectedHoareTripleChecker =
				new EfficientHoareTripleChecker(smtBasedHoareTripleChecker, mCsToolkit, mPredicateUnifier);
		final IHoareTripleChecker edgeChecker =
				new CachingHoareTripleCheckerMap(mServices, protectedHoareTripleChecker, mPredicateUnifier);
		return edgeChecker;
	}

	private void readPreferencePage() {
		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);

		mGlobalSettings = new CodeCheckSettings();

		final Checker checker = prefs.getEnum(CodeCheckPreferenceInitializer.LABEL_CHECKER, Checker.class);

		mGlobalSettings.setChecker(checker);

		mGlobalSettings.setMemoizeNormalEdgeChecks(
				prefs.getBoolean(CodeCheckPreferenceInitializer.LABEL_MEMOIZENORMALEDGECHECKS,
						CodeCheckPreferenceInitializer.DEF_MEMOIZENORMALEDGECHECKS));
		mGlobalSettings.setMemoizeReturnEdgeChecks(
				prefs.getBoolean(CodeCheckPreferenceInitializer.LABEL_MEMOIZERETURNEDGECHECKS,
						CodeCheckPreferenceInitializer.DEF_MEMOIZERETURNEDGECHECKS));

		mGlobalSettings.setInterpolationMode(
				prefs.getEnum(CodeCheckPreferenceInitializer.LABEL_INTERPOLATIONMODE, InterpolationTechnique.class));

		mGlobalSettings.setUseInterpolantconsolidation(
				prefs.getBoolean(CodeCheckPreferenceInitializer.LABEL_INTERPOLANTCONSOLIDATION,
						CodeCheckPreferenceInitializer.DEF_INTERPOLANTCONSOLIDATION));

		mGlobalSettings.setPredicateUnification(
				prefs.getEnum(CodeCheckPreferenceInitializer.LABEL_PREDICATEUNIFICATION, PredicateUnification.class));

		mGlobalSettings.setEdgeCheckOptimization(
				prefs.getEnum(CodeCheckPreferenceInitializer.LABEL_EDGECHECKOPTIMIZATION, EdgeCheckOptimization.class));

		mGlobalSettings.setIterations(prefs.getInt(CodeCheckPreferenceInitializer.LABEL_ITERATIONS,
				CodeCheckPreferenceInitializer.DEF_ITERATIONS));

		mGlobalSettings.setDotGraphPath(prefs.getString(CodeCheckPreferenceInitializer.LABEL_GRAPHWRITERPATH,
				CodeCheckPreferenceInitializer.DEF_GRAPHWRITERPATH));

		mGlobalSettings.setRedirectionStrategy(
				prefs.getEnum(CodeCheckPreferenceInitializer.LABEL_REDIRECTION, RedirectionStrategy.class));

		mGlobalSettings.setDefaultRedirection(prefs.getBoolean(CodeCheckPreferenceInitializer.LABEL_DEF_RED,
				CodeCheckPreferenceInitializer.DEF_DEF_RED));
		mGlobalSettings.setRemoveFalseNodes(prefs.getBoolean(CodeCheckPreferenceInitializer.LABEL_RmFALSE,
				CodeCheckPreferenceInitializer.DEF_RmFALSE));
		mGlobalSettings.setCheckSatisfiability(prefs.getBoolean(CodeCheckPreferenceInitializer.LABEL_CHK_SAT,
				CodeCheckPreferenceInitializer.DEF_CHK_SAT));

		/*
		 * Settings concerning the solver for trace checks
		 */
		mGlobalSettings.setUseSeparateSolverForTracechecks(
				prefs.getBoolean(CodeCheckPreferenceInitializer.LABEL_USESEPARATETRACECHECKSOLVER,
						CodeCheckPreferenceInitializer.DEF_USESEPARATETRACECHECKSOLVER));

		mGlobalSettings.setUseFallbackForSeparateSolverForTracechecks(
				prefs.getBoolean(CodeCheckPreferenceInitializer.LABEL_USEFALLBACKFORSEPARATETRACECHECKSOLVER,
						CodeCheckPreferenceInitializer.DEF_USEFALLBACKFORSEPARATETRACECHECKSOLVER));

		mGlobalSettings.setChooseSeparateSolverForTracechecks(
				prefs.getEnum(CodeCheckPreferenceInitializer.LABEL_CHOOSESEPARATETRACECHECKSOLVER, SolverMode.class));

		mGlobalSettings.setSeparateSolverForTracechecksCommand(
				prefs.getString(CodeCheckPreferenceInitializer.LABEL_SEPARATETRACECHECKSOLVERCOMMAND,
						CodeCheckPreferenceInitializer.DEF_SEPARATETRACECHECKSOLVERCOMMAND));

		mGlobalSettings.setSeparateSolverForTracechecksTheory(
				prefs.getString(CodeCheckPreferenceInitializer.LABEL_SEPARATETRACECHECKSOLVERTHEORY,
						CodeCheckPreferenceInitializer.DEF_SEPARATETRACECHECKSOLVERTHEORY));

		/*
		 * Settings concerning betim interpolation
		 */
		mGlobalSettings
				.setUseLiveVariables(prefs.getBoolean(CodeCheckPreferenceInitializer.LABEL_LIVE_VARIABLES, true));
		mGlobalSettings
				.setUseUnsatCores(prefs.getEnum(CodeCheckPreferenceInitializer.LABEL_UNSAT_CORES, UnsatCores.class));

		/*
		 * Abstract interpretataion settings
		 */
		mGlobalSettings.setUseAbstractInterpretation(
				prefs.getBoolean(CodeCheckPreferenceInitializer.LABEL_USE_ABSTRACT_INTERPRETATION,
						CodeCheckPreferenceInitializer.DEF_USE_ABSTRACT_INTERPRETATION));

	}

	private void removeSummaryEdges() {
		final Deque<AnnotatedProgramPoint> stack = new ArrayDeque<>();
		final Set<AnnotatedProgramPoint> visited = new HashSet<>();
		visited.add(mGraphRoot);
		stack.add(mGraphRoot);
		while (!stack.isEmpty()) {
			final AnnotatedProgramPoint current = stack.pop();
			for (final AppEdge outEdge : new ArrayList<>(current.getOutgoingEdges())) {
				final AnnotatedProgramPoint successor = outEdge.getTarget();
				if (outEdge.getStatement() instanceof Summary
						&& ((Summary) outEdge.getStatement()).calledProcedureHasImplementation()) {
					outEdge.disconnect();
				}

				if (visited.add(successor)) {
					stack.add(successor);
				}
			}
		}
	}

	@Override
	public boolean process(final IElement root) {
		if (!(root instanceof IIcfg<?>)) {
			return false;
		}
		@SuppressWarnings("unchecked")
		final IIcfg<IcfgLocation> icfg = (IIcfg<IcfgLocation>) root;
		initialize(icfg);

		final ImpRootNode originalGraphCopy = copyGraph(mGraphRoot);

		final ArrayList<AnnotatedProgramPoint> procRootsToCheck = new ArrayList<>();

		// check for Ultimate.start -- assuming that if such a procedure exists,
		// it comes from the c translation
		for (final AnnotatedProgramPoint procRoot : mGraphRoot.getOutgoingNodes()) {
			if (procRoot.getProgramPoint().getProcedure().startsWith("ULTIMATE.start")) {
				procRootsToCheck.add(procRoot);
				break;
			}
		}
		if (procRootsToCheck.isEmpty()) {
			// -> no Ultimate.start present
			procRootsToCheck.addAll(mGraphRoot.getOutgoingNodes());
		}

		boolean allSafe = true;
		boolean verificationInterrupted = false;
		IcfgProgramExecution realErrorProgramExecution = null;

		// benchmark data collector variables
		final CegarLoopStatisticsGenerator benchmarkGenerator = new CegarLoopStatisticsGenerator();
		benchmarkGenerator.start(CegarLoopStatisticsDefinitions.OverallTime.toString());

		int iterationsCount = 0;

		InterpolatingTraceCheck<IIcfgTransition<?>> traceCheck = null;
		final CodeChecker codechecker = createCodeChecker();
		for (final AnnotatedProgramPoint procedureRoot : procRootsToCheck) {
			if (!mServices.getProgressMonitorService().continueProcessing()) {
				verificationInterrupted = true;
				break;
			}

			if (mLogger.isDebugEnabled()) {
				mLogger.debug("Exploring : " + procedureRoot);
			}
			final IEmptinessCheck emptinessCheck = new NWAEmptinessCheck(mServices);

			while (mLoopForever || iterationsCount < mIterationsLimit) {
				iterationsCount++;
				if (!mServices.getProgressMonitorService().continueProcessing()) {
					verificationInterrupted = true;
					break;
				}

				benchmarkGenerator.announceNextIteration();
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(String.format("Iterations = %d%n", iterationsCount));
				}
				final NestedRun<IIcfgTransition<?>, AnnotatedProgramPoint> errorRun =
						emptinessCheck.checkForEmptiness(procedureRoot);

				if (errorRun == null) {
					// TODO: this only works for the case where we have 1 procedure in procRootsToCheck, right??
					mGraphWriter.writeGraphAsImage(procedureRoot, String.format("graph_%s_%s_noEP",
							mGraphWriter.getGraphCounter(), procedureRoot.toString().substring(0, 5)));
					// if an error trace doesn't exist, return safe
					mLogger.warn("This Program is SAFE, Check terminated with " + iterationsCount + " iterations.");
					break;
				}
				mLogger.info("Error Path is FOUND.");
				mGraphWriter.writeGraphAsImage(procedureRoot,
						String.format("graph_%s_%s_foundEP", mGraphWriter.getGraphCounter(),
								procedureRoot.toString().substring(0, 5)),
						errorRun.getStateSequence().toArray(new AnnotatedProgramPoint[] {}));

				ManagedScript mgdScriptTracechecks;
				if (mGlobalSettings.isUseSeparateSolverForTracechecks()) {
					final String filename = mOriginalRoot.getIdentifier() + "_TraceCheck_Iteration" + iterationsCount;
					final SolverMode solverMode = mGlobalSettings.getChooseSeparateSolverForTracechecks();
					final String commandExternalSolver = mGlobalSettings.getSeparateSolverForTracechecksCommand();
					final boolean dumpSmtScriptToFile = false;
					final String pathOfDumpedScript = "";
					final boolean fakeNonIncrementalScript = false;
					final SolverSettings solverSettings = SolverBuilder.constructSolverSettings(filename, solverMode,
							fakeNonIncrementalScript, commandExternalSolver, dumpSmtScriptToFile, pathOfDumpedScript);
					final Script tcSolver = SolverBuilder.buildAndInitializeSolver(mServices,
							mGlobalSettings.getChooseSeparateSolverForTracechecks(), solverSettings, false, false,
							mGlobalSettings.getSeparateSolverForTracechecksTheory(),
							"TraceCheck_Iteration" + iterationsCount);

					mgdScriptTracechecks = new ManagedScript(mServices, tcSolver);
					mOriginalRoot.getCfgSmtToolkit().getSmtFunctionsAndAxioms().transferSymbols(tcSolver);
				} else {
					mgdScriptTracechecks = mCsToolkit.getManagedScript();
				}

				traceCheck = createTraceCheck(errorRun, mgdScriptTracechecks);

				if (mGlobalSettings.isUseSeparateSolverForTracechecks()) {
					mgdScriptTracechecks.getScript().exit();
				}

				if (traceCheck.getToolchainCanceledExpection() != null) {
					throw traceCheck.getToolchainCanceledExpection();
				}

				final LBool isSafe = traceCheck.isCorrect();
				benchmarkGenerator.addTraceCheckData(traceCheck.getTraceCheckBenchmark());

				if (isSafe == LBool.UNSAT) { // trace is infeasible
					IPredicate[] interpolants = null;

					if (mGlobalSettings.isUseInterpolantconsolidation()) {
						try {
							final InterpolantConsolidation<IIcfgTransition<?>> interpConsoli =
									new InterpolantConsolidation<>(mPredicateUnifier.getTruePredicate(),
											mPredicateUnifier.getFalsePredicate(), new TreeMap<Integer, IPredicate>(),
											NestedWord.nestedWord(errorRun.getWord()), mCsToolkit,
											mCsToolkit.getModifiableGlobalsTable(), mServices, mLogger,
											mPredicateFactory, mPredicateUnifier, traceCheck, null);
							// Add benchmark data of interpolant consolidation
							// mCegarLoopBenchmark.addInterpolationConsolidationData(interpConsoli.getInterpolantConsolidationBenchmarks());
							// mInterpolantGenerator = interpConsoli;
							interpolants = interpConsoli.getInterpolants();
						} catch (final AutomataOperationCanceledException e) {
							// Timeout
							mLogger.error("Timeout during automata operation: ", e);
						}
					} else {
						interpolants = traceCheck.getInterpolants();
					}
					codechecker.codeCheck(errorRun, interpolants, procedureRoot);
					benchmarkGenerator.addEdgeCheckerData(codechecker.mEdgeChecker.getEdgeCheckerBenchmark());

				} else if (isSafe == LBool.SAT) { // trace is feasible
					mLogger.warn("This program is UNSAFE, Check terminated with " + iterationsCount + " iterations.");
					allSafe = false;
					if (traceCheck.providesRcfgProgramExecution()) {
						realErrorProgramExecution = traceCheck.getRcfgProgramExecution();
					} else {
						realErrorProgramExecution =
								TraceCheckUtils.computeSomeIcfgProgramExecutionWithoutValues(errorRun.getWord());
					}

					break;
				} else {
					assert isSafe == LBool.UNKNOWN;
					throw new UnsupportedOperationException("Solver said unknown");
				}
			}
			// we need a fresh copy for each iteration because..??
			mGraphRoot = copyGraph(originalGraphCopy);

			if (!allSafe) {
				break;
			}
		}

		Result overallResult = Result.UNKNOWN;
		if (!verificationInterrupted) {
			if (allSafe) {
				overallResult = Result.SAFE;
			} else {
				overallResult = Result.UNSAFE;
			}
		} else {
			reportTimeoutResult(mErrNodesOfAllProc);
		}

		// benchmark stuff
		benchmarkGenerator.setResult(overallResult);
		benchmarkGenerator.stop(CegarLoopStatisticsDefinitions.OverallTime.toString());
		benchmarkGenerator.addPredicateUnifierData(mPredicateUnifier.getPredicateUnifierBenchmark());
		final CodeCheckBenchmarks ccb = new CodeCheckBenchmarks(mOriginalRoot);
		ccb.aggregateBenchmarkData(benchmarkGenerator);
		reportBenchmark(ccb);

		if (overallResult == Result.SAFE) {
			reportPositiveResults(mErrNodesOfAllProc);

			if (OUTPUT_HOARE_ANNOTATION) {
				createInvariantResults(procRootsToCheck, icfg, icfg.getCfgSmtToolkit(),
						mServices.getBacktranslationService());
			}
		} else if (overallResult == Result.UNSAFE) {
			reportCounterexampleResult(realErrorProgramExecution);
		} else {
			final String shortDescription = "Unable to decide if program is safe!";
			final String longDescription = "Unable to decide if program is safe!";
			final GenericResult result =
					new GenericResult(Activator.PLUGIN_NAME, shortDescription, longDescription, Severity.INFO);
			mServices.getResultService().reportResult(Activator.PLUGIN_ID, result);
		}

		return false;
	}

	private void createInvariantResults(final List<AnnotatedProgramPoint> procRootsToCheck,
			final IIcfg<IcfgLocation> icfg, final CfgSmtToolkit csToolkit,
			final IBacktranslationService backTranslatorService) {
		final Term trueterm = csToolkit.getManagedScript().getScript().term("true");

		final Set<IcfgLocation> locsForLoopLocations = new HashSet<>();

		locsForLoopLocations.addAll(IcfgUtils.getPotentialCycleProgramPoints(icfg));
		locsForLoopLocations.addAll(icfg.getLoopLocations());
		// find all locations that have outgoing edges which are annotated with LoopEntry, i.e., all loop candidates

		for (final AnnotatedProgramPoint pr : procRootsToCheck) {
			final Map<IcfgLocation, Term> ha = computeHoareAnnotation(pr);
			for (final Entry<IcfgLocation, Term> kvp : ha.entrySet()) {
				final IcfgLocation locNode = kvp.getKey();
				if (!locsForLoopLocations.contains(locNode)) {
					// only compute loop invariants
					continue;
				}

				final Term invariant = kvp.getValue();
				if (invariant == null) {
					continue;
				}
				mLogger.info("Invariant with dag size " + new DagSizePrinter(invariant));

				final InvariantResult<IIcfgElement, Term> invResult =
						new InvariantResult<>(Activator.PLUGIN_NAME, locNode, backTranslatorService, invariant);
				reportResult(invResult);

				if (trueterm.equals(invariant)) {
					continue;
				}
				final String invStr = backTranslatorService.translateExpressionToString(invariant, Term.class);
				new WitnessInvariant(invStr).annotate(locNode);

			}
		}
	}

	private InterpolatingTraceCheck<IIcfgTransition<?>> createTraceCheck(
			final NestedRun<IIcfgTransition<?>, AnnotatedProgramPoint> errorRun,
			final ManagedScript mgdScriptTracechecks) {
		switch (mGlobalSettings.getInterpolationMode()) {
		case Craig_TreeInterpolation:
		case Craig_NestedInterpolation:
			try {
				final InterpolatingTraceCheck<IIcfgTransition<?>> tc = new InterpolatingTraceCheckCraig<>(
						mPredicateUnifier.getTruePredicate(), mPredicateUnifier.getFalsePredicate(),
						new TreeMap<Integer, IPredicate>(), errorRun.getWord(),
						TraceCheckUtils.getSequenceOfProgramPoints(NestedWord.nestedWord(errorRun.getWord())),
						mServices, mCsToolkit, mgdScriptTracechecks, mPredicateFactory, mPredicateUnifier,
						AssertCodeBlockOrder.NOT_INCREMENTALLY, true, true, mGlobalSettings.getInterpolationMode(),
						true, XNF_CONVERSION_TECHNIQUE, SIMPLIFICATION_TECHNIQUE, false);
				if (tc.getInterpolantComputationStatus().wasComputationSuccesful()) {
					return tc;
				}
			} catch (final Exception e) {
				mLogger.error("First Tracecheck threw exception " + e.getMessage());
				if (!mGlobalSettings.isUseFallbackForSeparateSolverForTracechecks()) {
					throw e;
				}
			}
			/*
			 * The fallback traceCheck is always the normal solver (i.e. the csToolkit that was set in RCFGBuilder
			 * settings with forward predicates betim interpolation.
			 *
			 * The fallback interpolation mode is hardcoded for now
			 */
			return new TraceCheckSpWp<>(mPredicateUnifier.getTruePredicate(), mPredicateUnifier.getFalsePredicate(),
					new TreeMap<Integer, IPredicate>(), errorRun.getWord(), mCsToolkit,
					AssertCodeBlockOrder.NOT_INCREMENTALLY, UnsatCores.CONJUNCT_LEVEL, true, mServices, true,
					mPredicateFactory, mPredicateUnifier, InterpolationTechnique.ForwardPredicates,
					mCsToolkit.getManagedScript(), XNF_CONVERSION_TECHNIQUE, SIMPLIFICATION_TECHNIQUE,
					TraceCheckUtils.getSequenceOfProgramPoints(NestedWord.nestedWord(errorRun.getWord())), true);
		case ForwardPredicates:
		case BackwardPredicates:
		case FPandBP:
		case FPandBPonlyIfFpWasNotPerfect:
			// return LBool.UNSAT if trace is infeasible
			try {
				return new TraceCheckSpWp<>(mPredicateUnifier.getTruePredicate(), mPredicateUnifier.getFalsePredicate(),
						new TreeMap<Integer, IPredicate>(), errorRun.getWord(), mCsToolkit,
						AssertCodeBlockOrder.NOT_INCREMENTALLY, mGlobalSettings.getUseUnsatCores(),
						mGlobalSettings.isUseLiveVariables(), mServices, true, mPredicateFactory, mPredicateUnifier,
						mGlobalSettings.getInterpolationMode(), mgdScriptTracechecks, XNF_CONVERSION_TECHNIQUE,
						SIMPLIFICATION_TECHNIQUE,
						TraceCheckUtils.getSequenceOfProgramPoints(NestedWord.nestedWord(errorRun.getWord())), true);
			} catch (final Exception e) {
				if (!mGlobalSettings.isUseFallbackForSeparateSolverForTracechecks()) {
					throw e;
				}

				return new TraceCheckSpWp<>(mPredicateUnifier.getTruePredicate(), mPredicateUnifier.getFalsePredicate(),
						new TreeMap<Integer, IPredicate>(), errorRun.getWord(), mCsToolkit,
						AssertCodeBlockOrder.NOT_INCREMENTALLY, UnsatCores.CONJUNCT_LEVEL, true, mServices, true,
						mPredicateFactory, mPredicateUnifier, mGlobalSettings.getInterpolationMode(),
						mCsToolkit.getManagedScript(), XNF_CONVERSION_TECHNIQUE, SIMPLIFICATION_TECHNIQUE,
						TraceCheckUtils.getSequenceOfProgramPoints(NestedWord.nestedWord(errorRun.getWord())), true);
			}
		default:
			throw new UnsupportedOperationException(
					"Unsupported interpolation mode: " + mGlobalSettings.getInterpolationMode());
		}
	}

	private Map<IcfgLocation, Term> computeHoareAnnotation(final AnnotatedProgramPoint pr) {
		final Map<IcfgLocation, Term> pp2HoareAnnotation = new HashMap<>();
		final Map<IcfgLocation, Set<AnnotatedProgramPoint>> pp2app = computeProgramPointToAnnotatedProgramPoints(pr);

		for (final Entry<IcfgLocation, Set<AnnotatedProgramPoint>> kvp : pp2app.entrySet()) {
			final List<Term> terms =
					kvp.getValue().stream().map(a -> a.getPredicate().getFormula()).collect(Collectors.toList());
			final Term orTerm =
					SmtUtils.orWithExtendedLocalSimplification(mCsToolkit.getManagedScript().getScript(), terms);
			final Term simplifiedOrTerm = SmtUtils.simplify(mCsToolkit.getManagedScript(), orTerm, mServices,
					SimplificationTechnique.SIMPLIFY_DDA);
			pp2HoareAnnotation.put(kvp.getKey(), simplifiedOrTerm);
		}
		return pp2HoareAnnotation;
	}

	/**
	 * fill up the map programPointToAnnotatedProgramPoints with the reachable part of the CFG
	 *
	 * @param annotatedProgramPoint
	 * @param programPointToAnnotatedProgramPoints
	 */
	private static Map<IcfgLocation, Set<AnnotatedProgramPoint>>
			computeProgramPointToAnnotatedProgramPoints(final AnnotatedProgramPoint entry) {
		final Set<AnnotatedProgramPoint> visited = new HashSet<>();
		final Deque<AnnotatedProgramPoint> queue = new ArrayDeque<>();
		final Map<IcfgLocation, Set<AnnotatedProgramPoint>> rtr = new HashMap<>();
		queue.push(entry);

		while (!queue.isEmpty()) {
			final AnnotatedProgramPoint current = queue.pop();

			Set<AnnotatedProgramPoint> apps = rtr.get(current.getProgramPoint());
			if (apps == null) {
				apps = new HashSet<>();
				rtr.put(current.getProgramPoint(), apps);
			}
			apps.add(current);

			for (final AppEdge outEdge : current.getOutgoingEdges()) {
				if (!visited.contains(outEdge.getTarget())) {
					queue.push(outEdge.getTarget());
					visited.add(outEdge.getTarget());
				}
			}
		}
		return rtr;
	}

	/**
	 * Given a graph root, copy all the nodes and the corresponding connections.
	 *
	 * @param root
	 * @return
	 */
	public ImpRootNode copyGraph(final ImpRootNode root) {
		final HashMap<AnnotatedProgramPoint, AnnotatedProgramPoint> copy = new HashMap<>();
		// FIXME: 2016-11-05 Matthias: I cannot solve this, passing null.
		final ImpRootNode newRoot = new ImpRootNode();
		copy.put(root, newRoot);
		final Deque<AnnotatedProgramPoint> stack = new ArrayDeque<>();
		for (final AnnotatedProgramPoint child : root.getOutgoingNodes()) {
			stack.add(child);
		}
		while (!stack.isEmpty()) {
			final AnnotatedProgramPoint current = stack.pop();
			if (copy.containsKey(current)) {
				continue;
			}
			copy.put(current, new AnnotatedProgramPoint(current));
			final List<AnnotatedProgramPoint> nextNodes = current.getOutgoingNodes();
			for (final AnnotatedProgramPoint nextNode : nextNodes) {
				if (!copy.containsKey(nextNode)) {
					stack.add(nextNode);
				}
			}
		}
		for (final Entry<AnnotatedProgramPoint, AnnotatedProgramPoint> entry : copy.entrySet()) {
			final AnnotatedProgramPoint oldNode = entry.getKey();
			final AnnotatedProgramPoint newNode = entry.getValue();
			for (final AppEdge outEdge : oldNode.getOutgoingEdges()) {
				if (outEdge instanceof AppHyperEdge) {
					final AppHyperEdge outHypEdge = (AppHyperEdge) outEdge;
					final AnnotatedProgramPoint hier = copy.get(outHypEdge.getHier());
					if (hier != null) {
						newNode.connectOutgoingReturn(hier, (IIcfgReturnTransition<?, ?>) outHypEdge.getStatement(),
								copy.get(outHypEdge.getTarget()));
					}
				} else {
					newNode.connectOutgoing(outEdge.getStatement(), copy.get(outEdge.getTarget()));
				}
			}
		}
		return newRoot;
	}

	private <T> void reportBenchmark(final ICsvProviderProvider<T> benchmark) {
		final String shortDescription = "Ultimate CodeCheck benchmark data";
		final StatisticsResult<T> res = new StatisticsResult<>(Activator.PLUGIN_NAME, shortDescription, benchmark);
		reportResult(res);
	}

	private void reportPositiveResults(final Collection<IcfgLocation> errorLocs) {
		if (!errorLocs.isEmpty()) {
			for (final IcfgLocation errorLoc : errorLocs) {
				final PositiveResult<IIcfgElement> pResult =
						new PositiveResult<>(Activator.PLUGIN_NAME, errorLoc, mServices.getBacktranslationService());
				reportResult(pResult);
			}
		}
		final AllSpecificationsHoldResult result =
				AllSpecificationsHoldResult.createAllSpecificationsHoldResult(Activator.PLUGIN_NAME, errorLocs.size());

		reportResult(result);
		mLogger.info(result.getShortDescription() + " " + result.getLongDescription());
	}

	private void reportCounterexampleResult(final IcfgProgramExecution pe) {
		final List<UnprovabilityReason> upreasons = UnprovabilityReason.getUnprovabilityReasons(pe);
		if (!upreasons.isEmpty()) {
			reportUnproveableResult(pe, upreasons);
			return;
		}
		reportResult(new CounterExampleResult<>(getErrorPP(pe), Activator.PLUGIN_NAME,
				mServices.getBacktranslationService(), pe));
	}

	private void reportUnproveableResult(final IcfgProgramExecution pe,
			final List<UnprovabilityReason> unproabilityReasons) {
		final IcfgLocation errorPP = getErrorPP(pe);
		reportResult(new UnprovableResult<>(Activator.PLUGIN_NAME, errorPP, mServices.getBacktranslationService(), pe,
				unproabilityReasons));
	}

	public IcfgLocation getErrorPP(final IcfgProgramExecution rcfgProgramExecution) {
		final int lastPosition = rcfgProgramExecution.getLength() - 1;
		final IIcfgTransition<?> last = rcfgProgramExecution.getTraceElement(lastPosition).getTraceElement();
		final IcfgLocation errorPP = last.getTarget();
		return errorPP;
	}

	private void reportTimeoutResult(final Collection<IcfgLocation> errorLocs) {
		for (final IcfgLocation errorIpp : errorLocs) {
			final ILocation origin = ILocation.getAnnotation(errorIpp);
			String timeOutMessage =
					"Unable to prove that " + ResultUtil.getCheckedSpecification(errorIpp).getPositiveMessage();
			timeOutMessage += " (line " + origin.getStartLine() + ")";
			final TimeoutResultAtElement<IIcfgElement> timeOutRes = new TimeoutResultAtElement<>(errorIpp,
					Activator.PLUGIN_NAME, mServices.getBacktranslationService(), timeOutMessage);
			reportResult(timeOutRes);
		}
	}

	private void reportResult(final IResult res) {
		mServices.getResultService().reportResult(Activator.PLUGIN_ID, res);
	}

	public ImpRootNode getRoot() {
		return mGraphRoot;
	}

	@Override
	public void finish() {
		// not needed
	}

	@Override
	public void init(final ModelType modelType, final int currentModelIndex, final int numberOfModels) {
		// not needed
	}

	@Override
	public boolean performedChanges() {
		return false;
	}
}
