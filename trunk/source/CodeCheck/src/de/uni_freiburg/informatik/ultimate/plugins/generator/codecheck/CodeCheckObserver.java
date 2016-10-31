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
import java.util.Stack;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.BenchmarkResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.GenericResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.PositiveResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ResultUtil;
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
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.Settings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AnnotatedProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AppEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AppHyperEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.ImpRootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.RCFG2AnnotatedRCFG;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.CodeCheckPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.CodeCheckPreferenceInitializer.Checker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.CodeCheckPreferenceInitializer.EdgeCheckOptimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.CodeCheckPreferenceInitializer.PredicateUnification;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.CodeCheckPreferenceInitializer.RedirectionStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.emptinesscheck.IEmptinessCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.emptinesscheck.NWAEmptinessCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.impulse.ImpulseChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.kojak.UltimateChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RcfgElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.UnsatCores;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.InterpolantConsolidation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.InterpolatingTraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.InterpolatingTraceCheckerCraig;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerSpWp;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.IsContained;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap4;

/**
 * 
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class CodeCheckObserver implements IUnmanagedObserver {

	private static final boolean DEBUG = false;
	private static final boolean OUTPUT_HOARE_ANNOTATION = false;

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final IToolchainStorage mToolchainStorage;
	private final SimplificationTechnique mSimplificationTechnique = SimplificationTechnique.SIMPLIFY_DDA;
	private final XnfConversionTechnique mXnfConversionTechnique =
			XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION;

	private PredicateUnifier mPredicateUnifier;

	private CodeChecker mCodeChecker;

	private RootNode mOriginalRoot;
	private ImpRootNode mGraphRoot;

	private SmtManager mSmtManager;

	private IHoareTripleChecker mEdgeChecker;

	private GraphWriter mGraphWriter;

	private NestedMap3<IPredicate, CodeBlock, IPredicate, IsContained> mSatTriples;
	private NestedMap3<IPredicate, CodeBlock, IPredicate, IsContained> mUnsatTriples;
	private NestedMap4<IPredicate, IPredicate, CodeBlock, IPredicate, IsContained> mSatQuadruples;
	private NestedMap4<IPredicate, IPredicate, CodeBlock, IPredicate, IsContained> mUnsatQuadruples;

	private Collection<ProgramPoint> mErrNodesOfAllProc;

	private boolean mLoopForever = true;
	private int mIterationsLimit = -1;

	CodeCheckObserver(final IUltimateServiceProvider services, final IToolchainStorage toolchainStorage) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mToolchainStorage = toolchainStorage;
	}

	/**
	 * Initialize all the required objects in the implementation.
	 * 
	 * @param root
	 * @return
	 */
	private boolean initialize(final IElement root) {
		readPreferencePage();

		mOriginalRoot = (RootNode) root;
		final RootAnnot rootAnnot = mOriginalRoot.getRootAnnot();

		mSmtManager = new SmtManager(rootAnnot.getBoogie2SMT(), rootAnnot.getModGlobVarManager(), mServices,
				rootAnnot.getManagedScript(), mSimplificationTechnique, mXnfConversionTechnique);

		mPredicateUnifier =
				new PredicateUnifier(mServices, mSmtManager.getManagedScript(), 
						mSmtManager.getPredicateFactory(), mOriginalRoot.getRootAnnot().getBoogie2SMT().getBoogie2SmtSymbolTable(), 
						mSimplificationTechnique, mXnfConversionTechnique);

		mEdgeChecker =
				new MonolithicHoareTripleChecker(mSmtManager.getManagedScript(), mSmtManager.getModifiableGlobals());

		final Map<String, Collection<ProgramPoint>> proc2errNodes = rootAnnot.getErrorNodes();
		mErrNodesOfAllProc = new ArrayList<ProgramPoint>();
		for (final Collection<ProgramPoint> errNodeOfProc : proc2errNodes.values()) {
			mErrNodesOfAllProc.addAll(errNodeOfProc);
		}

		if (GlobalSettings._instance._memoizeNormalEdgeChecks) {
			mSatTriples = new NestedMap3<IPredicate, CodeBlock, IPredicate, IsContained>();
			mUnsatTriples = new NestedMap3<IPredicate, CodeBlock, IPredicate, IsContained>();
		}
		if (GlobalSettings._instance._memoizeReturnEdgeChecks) {
			mSatQuadruples = new NestedMap4<IPredicate, IPredicate, CodeBlock, IPredicate, IsContained>();
			mUnsatQuadruples = new NestedMap4<IPredicate, IPredicate, CodeBlock, IPredicate, IsContained>();
		}
		mGraphWriter = new GraphWriter(GlobalSettings._instance._dotGraphPath, true, true, true, false,
				mSmtManager.getScript());

		// DD: removed dependency to AIMK2, will be replaced by AIv2 soon
		// boolean usePredicatesFromAbstractInterpretation = true; // TODO make a Pref
		final Map<RCFGNode, Term> initialPredicates = null;
		// if (usePredicatesFromAbstractInterpretation) {
		// AbstractInterpretationPredicates annot = AbstractInterpretationPredicates.getAnnotation(moriginalRoot);
		// if (annot != null) {
		// initialPredicates = annot.getPredicates();
		// } else {
		// mLogger.warn(
		// "was not able to retrieve initial predicates from abstract interpretation --> wrong toolchain?? (using
		// \"true\")");
		// initialPredicates = null;
		// }
		// }
		// end dependency removal
		final RCFG2AnnotatedRCFG r2ar =
				new RCFG2AnnotatedRCFG(mSmtManager, mLogger, mPredicateUnifier.getTruePredicate(), initialPredicates);
		mGraphRoot = r2ar.convert(mServices, mOriginalRoot);

		mGraphWriter.writeGraphAsImage(mGraphRoot,
				String.format("graph_%s_originalAfterConversion", mGraphWriter._graphCounter));

		removeSummaryEdges();

		mGraphWriter.writeGraphAsImage(mGraphRoot,
				String.format("graph_%s_originalSummaryEdgesRemoved", mGraphWriter._graphCounter));

		if (GlobalSettings._instance.checker == Checker.IMPULSE) {
			mCodeChecker = new ImpulseChecker(root, mSmtManager, mOriginalRoot, mGraphRoot, mGraphWriter, mEdgeChecker,
					mPredicateUnifier, mLogger);
		} else {
			mCodeChecker = new UltimateChecker(root, mSmtManager, mOriginalRoot, mGraphRoot, mGraphWriter, mEdgeChecker,
					mPredicateUnifier, mLogger);
		}
		mIterationsLimit = GlobalSettings._instance._iterations;
		mLoopForever = (mIterationsLimit == -1);

		return false;
	}

	private void readPreferencePage() {
		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);

		GlobalSettings.init();

		GlobalSettings._instance.checker = prefs.getEnum(CodeCheckPreferenceInitializer.LABEL_CHECKER, Checker.class);

		GlobalSettings._instance._memoizeNormalEdgeChecks =
				prefs.getBoolean(CodeCheckPreferenceInitializer.LABEL_MEMOIZENORMALEDGECHECKS,
						CodeCheckPreferenceInitializer.DEF_MEMOIZENORMALEDGECHECKS);
		GlobalSettings._instance._memoizeReturnEdgeChecks =
				prefs.getBoolean(CodeCheckPreferenceInitializer.LABEL_MEMOIZERETURNEDGECHECKS,
						CodeCheckPreferenceInitializer.DEF_MEMOIZERETURNEDGECHECKS);

		// GlobalSettings._instance._solverAndInterpolator = prefs
		// .getEnum(CodeCheckPreferenceInitializer.LABEL_SOLVERANDINTERPOLATOR, SolverAndInterpolator.class);

		GlobalSettings._instance._interpolationMode =
				prefs.getEnum(CodeCheckPreferenceInitializer.LABEL_INTERPOLATIONMODE, InterpolationTechnique.class);

		GlobalSettings._instance.useInterpolantconsolidation =
				prefs.getBoolean(CodeCheckPreferenceInitializer.LABEL_INTERPOLANTCONSOLIDATION,
						CodeCheckPreferenceInitializer.DEF_INTERPOLANTCONSOLIDATION);

		GlobalSettings._instance._predicateUnification =
				prefs.getEnum(CodeCheckPreferenceInitializer.LABEL_PREDICATEUNIFICATION, PredicateUnification.class);

		GlobalSettings._instance._edgeCheckOptimization =
				prefs.getEnum(CodeCheckPreferenceInitializer.LABEL_EDGECHECKOPTIMIZATION, EdgeCheckOptimization.class);

		GlobalSettings._instance._iterations = prefs.getInt(CodeCheckPreferenceInitializer.LABEL_ITERATIONS,
				CodeCheckPreferenceInitializer.DEF_ITERATIONS);

		GlobalSettings._instance._dotGraphPath = prefs.getString(CodeCheckPreferenceInitializer.LABEL_GRAPHWRITERPATH,
				CodeCheckPreferenceInitializer.DEF_GRAPHWRITERPATH);

		GlobalSettings._instance.redirectionStrategy =
				prefs.getEnum(CodeCheckPreferenceInitializer.LABEL_REDIRECTION, RedirectionStrategy.class);

		GlobalSettings._instance.defaultRedirection = prefs.getBoolean(CodeCheckPreferenceInitializer.LABEL_DEF_RED,
				CodeCheckPreferenceInitializer.DEF_DEF_RED);
		GlobalSettings._instance.removeFalseNodes = prefs.getBoolean(CodeCheckPreferenceInitializer.LABEL_RmFALSE,
				CodeCheckPreferenceInitializer.DEF_RmFALSE);
		GlobalSettings._instance.checkSatisfiability = prefs.getBoolean(CodeCheckPreferenceInitializer.LABEL_CHK_SAT,
				CodeCheckPreferenceInitializer.DEF_CHK_SAT);

		/*
		 * Settings concerning the solver for trace checks
		 */
		GlobalSettings._instance.useSeparateSolverForTracechecks =
				prefs.getBoolean(CodeCheckPreferenceInitializer.LABEL_USESEPARATETRACECHECKSOLVER,
						CodeCheckPreferenceInitializer.DEF_USESEPARATETRACECHECKSOLVER);

		GlobalSettings._instance.useFallbackForSeparateSolverForTracechecks =
				prefs.getBoolean(CodeCheckPreferenceInitializer.LABEL_USEFALLBACKFORSEPARATETRACECHECKSOLVER,
						CodeCheckPreferenceInitializer.DEF_USEFALLBACKFORSEPARATETRACECHECKSOLVER);

		GlobalSettings._instance.chooseSeparateSolverForTracechecks =
				prefs.getEnum(CodeCheckPreferenceInitializer.LABEL_CHOOSESEPARATETRACECHECKSOLVER, SolverMode.class);

		GlobalSettings._instance.separateSolverForTracechecksCommand =
				prefs.getString(CodeCheckPreferenceInitializer.LABEL_SEPARATETRACECHECKSOLVERCOMMAND,
						CodeCheckPreferenceInitializer.DEF_SEPARATETRACECHECKSOLVERCOMMAND);

		GlobalSettings._instance.separateSolverForTracechecksTheory =
				prefs.getString(CodeCheckPreferenceInitializer.LABEL_SEPARATETRACECHECKSOLVERTHEORY,
						CodeCheckPreferenceInitializer.DEF_SEPARATETRACECHECKSOLVERTHEORY);

		/*
		 * Settings concerning betim interpolation
		 */
		GlobalSettings._instance.useLiveVariables =
				prefs.getBoolean(CodeCheckPreferenceInitializer.LABEL_LIVE_VARIABLES, true);
		GlobalSettings._instance.useUnsatCores =
				prefs.getEnum(CodeCheckPreferenceInitializer.LABEL_UNSAT_CORES, UnsatCores.class);

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
		initialize(root);

		mGraphWriter.writeGraphAsImage(mGraphRoot, String.format("graph_%s_original", mGraphWriter._graphCounter));

		final ImpRootNode originalGraphCopy = copyGraph(mGraphRoot);

		mGraphWriter.writeGraphAsImage(originalGraphCopy,
				String.format("graph_%s_originalCopied", mGraphWriter._graphCounter));

		final ArrayList<AnnotatedProgramPoint> procRootsToCheck = new ArrayList<AnnotatedProgramPoint>();

		// check for Ultimate.start -- assuming that if such a procedure exists,
		// it comes from the c translation
		for (final AnnotatedProgramPoint procRoot : mGraphRoot.getOutgoingNodes()) {
			if (procRoot.getProgramPoint().getProcedure().startsWith("ULTIMATE.start")) {
				procRootsToCheck.add(procRoot);
				break;
			}
		}
		if (procRootsToCheck.isEmpty()) { // -> no Ultimate.start present
			procRootsToCheck.addAll(mGraphRoot.getOutgoingNodes());
		}

		Result overallResult = Result.UNKNOWN;
		boolean allSafe = true;
		boolean verificationInterrupted = false;
		RcfgProgramExecution realErrorProgramExecution = null;

		// benchmark data collector variables
		final CegarLoopStatisticsGenerator benchmarkGenerator = new CegarLoopStatisticsGenerator();
		benchmarkGenerator.start(CegarLoopStatisticsDefinitions.OverallTime.toString());

		int iterationsCount = 0;

		InterpolatingTraceChecker traceChecker = null;

		for (final AnnotatedProgramPoint procedureRoot : procRootsToCheck) {
			if (!mServices.getProgressMonitorService().continueProcessing()) {
				verificationInterrupted = true;
				break;
			}

			mLogger.debug("Exploring : " + procedureRoot);

			final IEmptinessCheck emptinessCheck = new NWAEmptinessCheck(mServices);

			if (DEBUG) {
				mCodeChecker.debug();
			}
			while (mLoopForever || iterationsCount++ < mIterationsLimit) {
				if (!mServices.getProgressMonitorService().continueProcessing()) {
					verificationInterrupted = true;
					break;
				}

				benchmarkGenerator.announceNextIteration();

				mLogger.debug(String.format("Iterations = %d%n", iterationsCount));
				final NestedRun<CodeBlock, AnnotatedProgramPoint> errorRun =
						emptinessCheck.checkForEmptiness(procedureRoot);

				if (errorRun == null) {
					// TODO: this only works for the case where we have 1 procedure in procRootsToCheck, right??
					mGraphWriter.writeGraphAsImage(procedureRoot, String.format("graph_%s_%s_noEP",
							mGraphWriter._graphCounter, procedureRoot.toString().substring(0, 5)));
					// if an error trace doesn't exist, return safe
					mLogger.warn("This Program is SAFE, Check terminated with " + iterationsCount + " iterations.");
					break;
				} else {
					mLogger.info("Error Path is FOUND.");
					mGraphWriter.writeGraphAsImage(procedureRoot,
							String.format("graph_%s_%s_foundEP", mGraphWriter._graphCounter,
									procedureRoot.toString().substring(0, 5)),
							errorRun.getStateSequence().toArray(new AnnotatedProgramPoint[] {}));

					if (GlobalSettings._instance._predicateUnification == PredicateUnification.PER_ITERATION) {
						mPredicateUnifier = new PredicateUnifier(mServices, mSmtManager.getManagedScript(), 
								mSmtManager.getPredicateFactory(), 
								mOriginalRoot.getRootAnnot().getBoogie2SMT().getBoogie2SmtSymbolTable(), 
								mSimplificationTechnique,
								mXnfConversionTechnique);
					}

					SmtManager smtManagerTracechecks;
					// if (noArrayOrNIRAsofar && GlobalSettings._instance.useSeparateSolverForTracechecks) {
					if (GlobalSettings._instance.useSeparateSolverForTracechecks) {
						final String filename = mOriginalRoot.getFilename() + "_TraceCheck_Iteration" + iterationsCount;
						final SolverMode solverMode = GlobalSettings._instance.chooseSeparateSolverForTracechecks;
						final String commandExternalSolver =
								GlobalSettings._instance.separateSolverForTracechecksCommand;
						final boolean dumpSmtScriptToFile = false;
						final String pathOfDumpedScript = "";
						final boolean  fakeNonIncrementalScript = false;
						final Settings solverSettings = SolverBuilder.constructSolverSettings(
								filename, solverMode, fakeNonIncrementalScript,
								commandExternalSolver, dumpSmtScriptToFile, pathOfDumpedScript);
						final Script tcSolver = SolverBuilder.buildAndInitializeSolver(mServices, mToolchainStorage,
								GlobalSettings._instance.chooseSeparateSolverForTracechecks, solverSettings, false,
								false, GlobalSettings._instance.separateSolverForTracechecksTheory,
								"TraceCheck_Iteration" + iterationsCount);

						smtManagerTracechecks = new SmtManager(mOriginalRoot.getRootAnnot().getBoogie2SMT(), mOriginalRoot.getRootAnnot().getModGlobVarManager(),
								mServices, mOriginalRoot.getRootAnnot().getManagedScript(), mSimplificationTechnique,
								mXnfConversionTechnique);
						final TermTransferrer tt = new TermTransferrer(tcSolver);
						for (final Term axiom : mOriginalRoot.getRootAnnot().getBoogie2SMT().getAxioms()) {
							tcSolver.assertTerm(tt.transform(axiom));
						}
					} else {
						smtManagerTracechecks = mSmtManager;
					}

					traceChecker = createTraceChecker(errorRun, smtManagerTracechecks);

					if (GlobalSettings._instance.useSeparateSolverForTracechecks) {
						smtManagerTracechecks.getScript().exit();
					}

					if (traceChecker.getToolchainCancelledExpection() != null) {
						throw traceChecker.getToolchainCancelledExpection();
					}

					final LBool isSafe = traceChecker.isCorrect();
					benchmarkGenerator.addTraceCheckerData(traceChecker.getTraceCheckerBenchmark());

					if (isSafe == LBool.UNSAT) { // trace is infeasible
						IPredicate[] interpolants = null;

						if (GlobalSettings._instance.useInterpolantconsolidation) {
							try {

								final InterpolantConsolidation interpConsoli = new InterpolantConsolidation(
										mPredicateUnifier.getTruePredicate(), mPredicateUnifier.getFalsePredicate(),
										new TreeMap<Integer, IPredicate>(), NestedWord.nestedWord(errorRun.getWord()),
										mSmtManager, mOriginalRoot.getRootAnnot().getModGlobVarManager(), mServices,
										mLogger, mPredicateUnifier, traceChecker, null// mtaPrefs
								);
								// Add benchmark data of interpolant consolidation
								// mCegarLoopBenchmark.addInterpolationConsolidationData(interpConsoli.getInterpolantConsolidationBenchmarks());
								// mInterpolantGenerator = interpConsoli;
								interpolants = interpConsoli.getInterpolants();
							} catch (final AutomataOperationCanceledException e) {
								// Timeout
								mLogger.error("Timeout during automata operation: ", e);
							}
						} else {
							interpolants = traceChecker.getInterpolants();
						}

						if (GlobalSettings._instance._memoizeNormalEdgeChecks
								&& GlobalSettings._instance._memoizeReturnEdgeChecks) {
							mCodeChecker.codeCheck(errorRun, interpolants, procedureRoot, mSatTriples, mUnsatTriples,
									mSatQuadruples, mUnsatQuadruples);
						} else if (GlobalSettings._instance._memoizeNormalEdgeChecks
								&& !GlobalSettings._instance._memoizeReturnEdgeChecks) {
							mCodeChecker.codeCheck(errorRun, interpolants, procedureRoot, mSatTriples, mUnsatTriples);
						} else {
							mCodeChecker.codeCheck(errorRun, interpolants, procedureRoot);
						}

						benchmarkGenerator.addEdgeCheckerData(mCodeChecker._edgeChecker.getEdgeCheckerBenchmark());

					} else { // trace is feasible
						mLogger.warn(
								"This program is UNSAFE, Check terminated with " + iterationsCount + " iterations.");
						allSafe = false;
						realErrorProgramExecution = traceChecker.getRcfgProgramExecution();

						if (DEBUG) {
							mCodeChecker.debug();
						}
						break;
					}
				}
				if (DEBUG) {
					mCodeChecker.debug();
				}
			}
			// we need a fresh copy for each iteration because..??
			mGraphRoot = copyGraph(originalGraphCopy);
			mCodeChecker.mgraphRoot = mGraphRoot;

			if (!allSafe) {
				break;
			}
		}

		if (DEBUG) {
			mCodeChecker.debug();
		}

		if (!verificationInterrupted) {
			if (allSafe) {
				overallResult = Result.CORRECT;
			} else {
				overallResult = Result.INCORRECT;
			}
		} else {
			reportTimeoutResult(mErrNodesOfAllProc);
		}

		mLogger.debug("MemoizationHitsSat: " + mCodeChecker.memoizationHitsSat);
		mLogger.debug("MemoizationHitsUnsat: " + mCodeChecker.memoizationHitsUnsat);
		mLogger.debug("MemoizationReturnHitsSat: " + mCodeChecker.memoizationReturnHitsSat);
		mLogger.debug("MemoizationReturnHitsUnsat: " + mCodeChecker.memoizationReturnHitsUnsat);

		// benchmark stuff
		benchmarkGenerator.setResult(overallResult);
		benchmarkGenerator.stop(CegarLoopStatisticsDefinitions.OverallTime.toString());

		final CodeCheckBenchmarks ccb = new CodeCheckBenchmarks(mOriginalRoot.getRootAnnot());
		ccb.aggregateBenchmarkData(benchmarkGenerator);

		reportBenchmark(ccb);

		if (overallResult == Result.CORRECT) {
			reportPositiveResults(mErrNodesOfAllProc);

			if (OUTPUT_HOARE_ANNOTATION) {
				for (final AnnotatedProgramPoint pr : procRootsToCheck) {
					mLogger.info("Hoare annotation for entrypoint " + pr.getProgramPoint().getProcedure());
					final HashMap<ProgramPoint, Term> ha = computeHoareAnnotation(pr);
					for (final Entry<ProgramPoint, Term> kvp : ha.entrySet()) {
						mLogger.info("At program point  " + prettyPrintProgramPoint(kvp.getKey())
								+ "  the Hoare annotation is:  " + kvp.getValue());
					}
				}
			}
		} else if (overallResult == Result.INCORRECT) {
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

	private InterpolatingTraceChecker createTraceChecker(final NestedRun<CodeBlock, AnnotatedProgramPoint> errorRun,
			final SmtManager smtManagerTracechecks) {
		switch (GlobalSettings._instance._interpolationMode) {
		case Craig_TreeInterpolation:
		case Craig_NestedInterpolation:
			try {
				return new InterpolatingTraceCheckerCraig(mPredicateUnifier.getTruePredicate(),
						mPredicateUnifier.getFalsePredicate(), new TreeMap<Integer, IPredicate>(), errorRun.getWord(),
						mSmtManager.getManagedScript(), mOriginalRoot.getRootAnnot().getModGlobVarManager(),
						AssertCodeBlockOrder.NOT_INCREMENTALLY, mServices, true, mPredicateUnifier,
						GlobalSettings._instance._interpolationMode, smtManagerTracechecks.getManagedScript(), true,
						mXnfConversionTechnique, mSimplificationTechnique, mOriginalRoot.getRootAnnot().getBoogie2SMT().getBoogie2SmtSymbolTable());
			} catch (final Exception e) {
				if (!GlobalSettings._instance.useFallbackForSeparateSolverForTracechecks) {
					throw e;
				}
				/*
				 * The fallback tracechecker is always the normal solver (i.e. the smtManager that was set in
				 * RCFGBuilder settings with forward predicates betim interpolation.
				 * 
				 * The fallback interpolation mode is hardcoded for now
				 */
				return new TraceCheckerSpWp(mPredicateUnifier.getTruePredicate(), mPredicateUnifier.getFalsePredicate(),
						new TreeMap<Integer, IPredicate>(), errorRun.getWord(), mSmtManager.getManagedScript(),
						mOriginalRoot.getRootAnnot().getModGlobVarManager(), AssertCodeBlockOrder.NOT_INCREMENTALLY,
						UnsatCores.CONJUNCT_LEVEL, true, mServices, true, mPredicateUnifier,
						InterpolationTechnique.ForwardPredicates, mSmtManager.getManagedScript(), mXnfConversionTechnique,
						mSimplificationTechnique, mOriginalRoot.getRootAnnot().getBoogie2SMT().getBoogie2SmtSymbolTable());
			}
		case ForwardPredicates:
		case BackwardPredicates:
		case FPandBP:
			// return LBool.UNSAT if trace is infeasible
			try {
				return new TraceCheckerSpWp(mPredicateUnifier.getTruePredicate(), mPredicateUnifier.getFalsePredicate(),
						new TreeMap<Integer, IPredicate>(), errorRun.getWord(), mSmtManager.getManagedScript(),
						mOriginalRoot.getRootAnnot().getModGlobVarManager(), AssertCodeBlockOrder.NOT_INCREMENTALLY,
						GlobalSettings._instance.useUnsatCores, GlobalSettings._instance.useLiveVariables, mServices,
						true, mPredicateUnifier, GlobalSettings._instance._interpolationMode, smtManagerTracechecks.getManagedScript(),
						mXnfConversionTechnique, mSimplificationTechnique, mOriginalRoot.getRootAnnot().getBoogie2SMT().getBoogie2SmtSymbolTable());
			} catch (final Exception e) {
				if (!GlobalSettings._instance.useFallbackForSeparateSolverForTracechecks) {
					throw e;
				}

				return new TraceCheckerSpWp(mPredicateUnifier.getTruePredicate(), mPredicateUnifier.getFalsePredicate(),
						new TreeMap<Integer, IPredicate>(), errorRun.getWord(), mSmtManager.getManagedScript(),
						mOriginalRoot.getRootAnnot().getModGlobVarManager(), AssertCodeBlockOrder.NOT_INCREMENTALLY,
						UnsatCores.CONJUNCT_LEVEL, true, mServices, true, mPredicateUnifier,
						GlobalSettings._instance._interpolationMode, mSmtManager.getManagedScript(), mXnfConversionTechnique,
						mSimplificationTechnique, mOriginalRoot.getRootAnnot().getBoogie2SMT().getBoogie2SmtSymbolTable());
			}
		default:
			throw new UnsupportedOperationException(
					"Unsupported interpolation mode: " + GlobalSettings._instance._interpolationMode);
		}
	}

	private static String prettyPrintProgramPoint(final ProgramPoint pp) {
		final int startLine = pp.getPayload().getLocation().getStartLine();
		final int endLine = pp.getPayload().getLocation().getStartLine();
		final StringBuilder sb = new StringBuilder();
		sb.append(pp);
		if (startLine == endLine) {
			sb.append("(line " + startLine + ")");
		} else {
			sb.append("(lines " + startLine + " " + endLine + ")");
		}
		return sb.toString();
	}

	private HashMap<ProgramPoint, Term> computeHoareAnnotation(final AnnotatedProgramPoint pr) {
		final HashMap<ProgramPoint, HashSet<AnnotatedProgramPoint>> programPointToAnnotatedProgramPoints =
				new HashMap<>();

		final HashMap<ProgramPoint, Term> programPointToHoareAnnotation = new HashMap<>();

		computeProgramPointToAnnotatedProgramPoints(pr, programPointToAnnotatedProgramPoints);

		for (final Entry<ProgramPoint, HashSet<AnnotatedProgramPoint>> kvp : programPointToAnnotatedProgramPoints
				.entrySet()) {
			IPredicate annot = mSmtManager.getPredicateFactory().newPredicate(mSmtManager.getScript().term("false"));

			for (final AnnotatedProgramPoint app : kvp.getValue()) {
				final Term tvp = mSmtManager.getPredicateFactory().or(false, annot, app.getPredicate());
				annot = mSmtManager.getPredicateFactory().newSPredicate(kvp.getKey(), tvp);
			}
			// programPointToHoareAnnotation.put(kvp.getKey(), annot.getClosedFormula());
			programPointToHoareAnnotation.put(kvp.getKey(), annot.getFormula());
		}
		return programPointToHoareAnnotation;
	}

	/**
	 * fill up the map programPointToAnnotatedProgramPoints with the reachable part of the CFG
	 * 
	 * @param annotatedProgramPoint
	 * @param programPointToAnnotatedProgramPoints
	 */
	private void computeProgramPointToAnnotatedProgramPoints(final AnnotatedProgramPoint entry,
			final HashMap<ProgramPoint, HashSet<AnnotatedProgramPoint>> programPointToAnnotatedProgramPoints) {

		final HashSet<AnnotatedProgramPoint> visited = new HashSet<>();

		final ArrayDeque<AnnotatedProgramPoint> queue = new ArrayDeque<>();

		queue.push(entry);

		while (!queue.isEmpty()) {
			final AnnotatedProgramPoint current = queue.pop();

			HashSet<AnnotatedProgramPoint> apps = programPointToAnnotatedProgramPoints.get(current.getProgramPoint());
			if (apps == null) {
				apps = new HashSet<AnnotatedProgramPoint>();
				programPointToAnnotatedProgramPoints.put(current.getProgramPoint(), apps);
			}
			apps.add(current);

			for (final AppEdge outEdge : current.getOutgoingEdges()) {
				if (!visited.contains(outEdge.getTarget())) {
					queue.push(outEdge.getTarget());
					visited.add(outEdge.getTarget());
				}
			}
		}
	}

	/**
	 * Given a graph root, copy all the nodes and the corresponding connections.
	 * 
	 * @param root
	 * @return
	 */
	public ImpRootNode copyGraph(final ImpRootNode root) {
		final HashMap<AnnotatedProgramPoint, AnnotatedProgramPoint> copy =
				new HashMap<AnnotatedProgramPoint, AnnotatedProgramPoint>();
		final ImpRootNode newRoot = new ImpRootNode(root.getRootAnnot());
		copy.put(root, newRoot);
		final Stack<AnnotatedProgramPoint> stack = new Stack<AnnotatedProgramPoint>();
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
						newNode.connectOutgoingReturn(hier, (Return) outHypEdge.getStatement(),
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
		final BenchmarkResult<T> res = new BenchmarkResult<T>(Activator.PLUGIN_NAME, shortDescription, benchmark);
		// s_Logger.warn(res.getLongDescription());

		reportResult(res);
	}

	private void reportPositiveResults(final Collection<ProgramPoint> errorLocs) {
		final String longDescription;
		if (errorLocs.isEmpty()) {
			longDescription = "We were not able to verify any"
					+ " specifiation because the program does not contain any specification.";
		} else {
			longDescription = errorLocs.size() + " specifications checked. All of them hold";
			for (final ProgramPoint errorLoc : errorLocs) {
				final PositiveResult<RcfgElement> pResult = new PositiveResult<RcfgElement>(Activator.PLUGIN_NAME,
						errorLoc, mServices.getBacktranslationService());
				reportResult(pResult);
			}
		}
		final AllSpecificationsHoldResult result =
				new AllSpecificationsHoldResult(Activator.PLUGIN_NAME, longDescription);
		reportResult(result);
		mLogger.info(result.getShortDescription() + " " + result.getLongDescription());
	}

	private void reportCounterexampleResult(final RcfgProgramExecution pe) {
		if (!pe.getOverapproximations().isEmpty()) {
			reportUnproveableResult(pe, pe.getUnprovabilityReasons());
			return;
		}

		reportResult(new CounterExampleResult<RcfgElement, RCFGEdge, Term>(getErrorPP(pe), Activator.PLUGIN_NAME,
				mServices.getBacktranslationService(), pe));
	}

	private void reportUnproveableResult(final RcfgProgramExecution pe,
			final List<UnprovabilityReason> unproabilityReasons) {
		final ProgramPoint errorPP = getErrorPP(pe);
		final UnprovableResult<RcfgElement, RCFGEdge, Term> uknRes =
				new UnprovableResult<RcfgElement, RCFGEdge, Term>(Activator.PLUGIN_NAME, errorPP,
						mServices.getBacktranslationService(), pe, unproabilityReasons);
		reportResult(uknRes);
	}

	public ProgramPoint getErrorPP(final RcfgProgramExecution rcfgProgramExecution) {
		final int lastPosition = rcfgProgramExecution.getLength() - 1;
		final RCFGEdge last = rcfgProgramExecution.getTraceElement(lastPosition).getTraceElement();
		final ProgramPoint errorPP = (ProgramPoint) last.getTarget();
		return errorPP;
	}

	private void reportTimeoutResult(final Collection<ProgramPoint> errorLocs) {
		for (final ProgramPoint errorIpp : errorLocs) {
			final ProgramPoint errorLoc = errorIpp;
			final ILocation origin = errorLoc.getBoogieASTNode().getLocation().getOrigin();
			String timeOutMessage =
					"Unable to prove that " + ResultUtil.getCheckedSpecification(errorLoc).getPositiveMessage();
			timeOutMessage += " (line " + origin.getStartLine() + ")";
			final TimeoutResultAtElement<RcfgElement> timeOutRes = new TimeoutResultAtElement<RcfgElement>(errorLoc,
					Activator.PLUGIN_NAME, mServices.getBacktranslationService(), timeOutMessage);
			reportResult(timeOutRes);
		}
	}

	private void reportResult(final IResult res) {
		mServices.getResultService().reportResult(Activator.PLUGIN_ID, res);
	}

	public ImpRootNode getRoot() {
		return mCodeChecker.mgraphRoot;
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

	private enum Result {
		CORRECT, TIMEOUT, MAXEDITERATIONS, UNKNOWN, INCORRECT
	}
}
