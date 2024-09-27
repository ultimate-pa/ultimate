/*
 * Copyright (C) 2013-2022 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2011-2022 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2022 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Scanner;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.EpsilonNestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaBasis;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Intersect;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveDeadEnds;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.TaskCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.TaskCanceledException.UserDefinedLimit;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerCache;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtParserUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.SubtaskIterationIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult.BasicRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.proofs.floydhoare.NwaFloydHoareValidityCheck;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.cfg2automaton.Cfg2Automaton;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.PathProgram;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.PathProgram.PathProgramConstructionResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.IcfgAngelicProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.errorlocalization.FlowSensitiveFaultLocalizer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.errorlocalization.TraceAberrantChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.AbstractInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.DeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.NondeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.Artifact;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.FloydHoareAutomataReuse;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RelevanceAnalysisMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.StrategyFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TaCheckAndRefinementPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine.ITARefinementStrategy;
import de.uni_freiburg.informatik.ultimate.util.HistogramOfIterable;
import de.uni_freiburg.informatik.ultimate.util.Lazy;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 * Subclass of AbstractCegarLoop which provides all algorithms for checking safety (not termination).
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 *
 * @param <A>
 *            The type of abstraction refined by the CEGAR loop
 */
public abstract class BasicCegarLoop<L extends IIcfgTransition<?>, A extends IAutomaton<L, IPredicate>>
		extends AbstractCegarLoop<L, A> {

	private static final boolean NON_EA_INDUCTIVITY_CHECK = false;

	protected final PredicateFactoryRefinement mStateFactoryForRefinement;
	protected final PredicateFactoryForInterpolantAutomata mPredicateFactoryInterpolantAutomata;
	protected final PredicateFactoryResultChecking mPredicateFactoryResultChecking;

	protected final RelevanceAnalysisMode mFaultLocalizationMode;
	private final boolean mFaultLocalizationAngelic;
	private final StrategyFactory<L> mStrategyFactory;
	private final PathProgramDumpController<L> mPathProgramDumpController;
	private final boolean mStoreFloydHoareAutomata;
	private final Set<Pair<AbstractInterpolantAutomaton<L>, IPredicateUnifier>> mFloydHoareAutomata =
			new LinkedHashSet<>();

	protected boolean mFallbackToFpIfInterprocedural = false;
	protected IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> mRefinementResult;

	private boolean mFirstReuseDump = true;

	public BasicCegarLoop(final DebugIdentifier name, final A initialAbstraction, final IIcfg<?> rootNode,
			final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory, final TAPreferences taPrefs,
			final Set<? extends IcfgLocation> errorLocs, final boolean computeProof,
			final IUltimateServiceProvider services, final Class<L> transitionClazz,
			final PredicateFactoryRefinement stateFactoryForRefinement) {
		super(services, name, initialAbstraction, rootNode, csToolkit, predicateFactory, taPrefs, errorLocs);
		mPathProgramDumpController = new PathProgramDumpController<>(getServices(), mPref, mIcfg);

		InterpolationTechnique interpolation = taPrefs.interpolation();
		if (mFallbackToFpIfInterprocedural && rootNode.getProcedureEntryNodes().size() > 1
				&& interpolation == InterpolationTechnique.FPandBP) {
			mLogger.info("fallback from FPandBP to FP because CFG is interprocedural");
			interpolation = InterpolationTechnique.ForwardPredicates;
		}

		mStoreFloydHoareAutomata = taPrefs.getFloydHoareAutomataReuse() != FloydHoareAutomataReuse.NONE;
		mStateFactoryForRefinement = stateFactoryForRefinement;
		mPredicateFactoryInterpolantAutomata = new PredicateFactoryForInterpolantAutomata(mCsToolkit.getManagedScript(),
				mPredicateFactory, computeProof);

		mPredicateFactoryResultChecking = new PredicateFactoryResultChecking(mPredicateFactory);

		mCegarLoopBenchmark = new CegarLoopStatisticsGenerator();
		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.OverallTime.toString());

		final IPreferenceProvider prefs = getServices().getPreferenceProvider(Activator.PLUGIN_ID);
		mFaultLocalizationMode =
				prefs.getEnum(TraceAbstractionPreferenceInitializer.LABEL_ERROR_TRACE_RELEVANCE_ANALYSIS_MODE,
						RelevanceAnalysisMode.class);
		mFaultLocalizationAngelic =
				prefs.getBoolean(TraceAbstractionPreferenceInitializer.LABEL_ERROR_TRACE_ANGELIC_VERIFICATION_ACTIVE);

		final TaCheckAndRefinementPreferences<L> taCheckAndRefinementPrefs =
				new TaCheckAndRefinementPreferences<>(getServices(), mPref, interpolation, mSimplificationTechnique,
						mXnfConversionTechnique, mCsToolkit, mPredicateFactory, mIcfg);
		mStrategyFactory = new StrategyFactory<>(mLogger, mPref, taCheckAndRefinementPrefs, mIcfg, mPredicateFactory,
				mPredicateFactoryInterpolantAutomata, transitionClazz);

		if (mPref.dumpOnlyReuseAutomata()) {
			// Construct an empty file. We need this empty file in cases where
			// the CFG does not have error location and no automaton is dumped.
			mLogger.info("Dumping reuse automata for " + mTaskIdentifier.toString());
			final String filename = mTaskIdentifier + "-reuse";
			final String fullPath = mPref.dumpPath() + File.separator + filename + "."
					+ mPrintAutomataLabeling.getFormat().getFileEnding();
			final File file = new File(fullPath);
			try {
				final FileWriter fw = new FileWriter(file, false);
				fw.close();
			} catch (final IOException e) {
				if (mLogger.isErrorEnabled()) {
					mLogger.error("Creating FileWriter did not work.", e);
				}
			}
		}

	}

	@Override
	protected void initialize() throws AutomataLibraryException {
		if (mPref.readInitialProof()) {
			readInitialProof();
		}
	}

	/**
	 * Reads a sequence of SMT assertions from a file (line by line), creates a refinement result from them and refines
	 * the initial abstraction with this result.
	 */
	protected final void readInitialProof() throws AutomataLibraryException {
		final String filename = ILocation.getAnnotation(mIcfg).getFileName() + ".proof.smt2";
		final Path path = Paths.get(filename).toAbsolutePath();
		if (Files.notExists(path)) {
			mLogger.warn("Could not find file with proof assertions: %s", path.toString());
			return;
		}

		mLogger.warn("First iteration: Refining with proof given in %s", path.toString());

		// Read a sequence of predicates from the file
		final List<IPredicate> predicates = new ArrayList<>();
		try (final Scanner myReader = new Scanner(path, StandardCharsets.UTF_8)) {
			while (myReader.hasNextLine()) {
				final String data = myReader.nextLine();
				if (data.isBlank() || data.stripLeading().startsWith("#")) {
					// skip blank lines and comments
					continue;
				}
				final Term term = SmtParserUtils.parseWithVariables(data, mServices, mCsToolkit);
				final IPredicate pred = mPredicateFactory.newPredicate(term);
				predicates.add(pred);
			}
		} catch (final IOException e) {
			throw new IllegalStateException(e);
		}

		final IPredicateUnifier unifier = new PredicateUnifier(mLogger, mServices, mCsToolkit.getManagedScript(),
				mPredicateFactory, mCsToolkit.getSymbolTable(), mSimplificationTechnique, mXnfConversionTechnique,
				predicates.toArray(IPredicate[]::new));

		final VpAlphabet<L> alphabet;
		if (mAbstraction instanceof INwaBasis<?, ?>) {
			alphabet = ((INwaBasis<L, ?>) mAbstraction).getVpAlphabet();
		} else {
			alphabet = new VpAlphabet<>(mAbstraction.getAlphabet());
		}

		// Create an automaton from the predicates.
		// The automaton has no edges, only states; it is only useful in combination with some enhancement.
		final NestedWordAutomaton<L, IPredicate> nwa =
				new NestedWordAutomaton<>(new AutomataLibraryServices(mServices), alphabet, mStateFactoryForRefinement);
		final IPredicate truePred = unifier.getTruePredicate();
		nwa.addState(true, false, truePred);
		final IPredicate falsePred = unifier.getFalsePredicate();
		nwa.addState(false, true, falsePred);
		for (final IPredicate pred : predicates) {
			nwa.addState(false, false, pred);
		}

		// Write the refinement result and interpolant automaton to the class fields, and call #refineAbstraction.
		mRefinementResult = new BasicRefinementEngineResult<>(LBool.UNSAT, nwa, null, false,
				List.of(new QualifiedTracePredicates(new TracePredicates(truePred, falsePred, predicates), getClass(),
						false)),
				new Lazy<>(() -> new MonolithicHoareTripleChecker(mCsToolkit)), new Lazy<>(() -> unifier));
		mInterpolAutomaton = mRefinementResult.getInfeasibilityProof();
		refineAbstraction();
	}

	@Override
	protected Pair<LBool, IProgramExecution<L, Term>> isCounterexampleFeasible()
			throws AutomataOperationCanceledException {

		IStatisticsDataProvider refinementEngineStats = null;
		final ITARefinementStrategy<L> strategy = mStrategyFactory.constructStrategy(getServices(), mCounterexample,
				mAbstraction, new SubtaskIterationIdentifier(mTaskIdentifier, getIteration()),
				mPredicateFactoryInterpolantAutomata, getPreconditionProvider(), getPostconditionProvider());
		try {
			if (mPref.hasLimitPathProgramCount() && mPref.getLimitPathProgramCount() < mStrategyFactory
					.getPathProgramCache().getPathProgramCount(mCounterexample)) {
				final String taskDescription = "bailout by path program count limit in iteration " + getIteration();
				throw new TaskCanceledException(UserDefinedLimit.PATH_PROGRAM_ATTEMPTS, getClass(), taskDescription);
			}

			final TraceAbstractionRefinementEngine<L> refinementEngine =
					new TraceAbstractionRefinementEngine<>(getServices(), mLogger, strategy);
			mRefinementResult = refinementEngine.getResult();
			refinementEngineStats = refinementEngine.getRefinementEngineStatistics();

		} catch (final ToolchainCanceledException tce) {
			final int traceHistogramMax = new HistogramOfIterable<>(mCounterexample.getWord()).getMax();
			final String taskDescription = "analyzing trace of length " + mCounterexample.getLength()
					+ " with TraceHistMax " + traceHistogramMax;
			tce.addRunningTaskInfo(new RunningTaskInfo(getClass(), taskDescription));

			mRefinementResult = new TimeoutRefinementEngineResult(new Lazy<>(() -> null),
					new Lazy<>(() -> strategy.getPredicateUnifier(null)));
			throw tce;
		}

		final LBool feasibility = mRefinementResult.getCounterexampleFeasibility();
		IProgramExecution<L, Term> rcfgProgramExecution = null;
		if (feasibility != LBool.SAT) {
			// dump path program if necessary
			mPathProgramDumpController.reportPathProgram(mCounterexample, mRefinementResult.somePerfectSequenceFound(),
					getIteration());
		}
		if (feasibility != LBool.UNSAT) {
			mLogger.info("Counterexample %s feasible", feasibility == LBool.SAT ? "is" : "might be");
			if (mRefinementResult.providesIcfgProgramExecution()) {
				rcfgProgramExecution = mRefinementResult.getIcfgProgramExecution();
			} else {
				rcfgProgramExecution =
						TraceCheckUtils.computeSomeIcfgProgramExecutionWithoutValues(mCounterexample.getWord());
			}

			if (mFaultLocalizationMode != RelevanceAnalysisMode.NONE && feasibility == LBool.SAT) {
				final INestedWordAutomaton<L, IPredicate> cfg = Cfg2Automaton.constructAutomatonWithSPredicates(
						getServices(), super.mIcfg, mStateFactoryForRefinement, super.mErrorLocs,
						mPref.interprocedural(), mPredicateFactory);
				final FlowSensitiveFaultLocalizer<L> fl = new FlowSensitiveFaultLocalizer<>(
						(NestedRun<L, IPredicate>) mCounterexample, cfg, getServices(), mCsToolkit, mPredicateFactory,
						mCsToolkit.getModifiableGlobalsTable(), mRefinementResult.getPredicateUnifier(),
						mFaultLocalizationMode, mSimplificationTechnique, mXnfConversionTechnique,
						mIcfg.getCfgSmtToolkit().getSymbolTable(), (IIcfg<IcfgLocation>) mIcfg);
				
				if (!(rcfgProgramExecution instanceof IcfgProgramExecution)) {
					throw new UnsupportedOperationException("Program execution is not " + IcfgProgramExecution.class);
				}
				rcfgProgramExecution = ((IcfgProgramExecution<L>) rcfgProgramExecution)
						.addRelevanceInformation(fl.getRelevanceInformation());

				if (mFaultLocalizationAngelic) {
					rcfgProgramExecution =
							new IcfgAngelicProgramExecution<>(rcfgProgramExecution, fl.getAngelicStatus());
				}
			}
			// TODO setting
			if (true && feasibility == LBool.SAT) {
				final TraceAberrantChecker<L> tac = new TraceAberrantChecker<>(
						(NestedRun<L, IPredicate>) mCounterexample, getServices(), mCsToolkit, mPredicateFactory,
						mCsToolkit.getModifiableGlobalsTable(), mRefinementResult.getPredicateUnifier(),
						mFaultLocalizationMode, mSimplificationTechnique, mXnfConversionTechnique,
						mIcfg.getCfgSmtToolkit().getSymbolTable(), (IIcfg<IcfgLocation>) mIcfg);
				if (!(rcfgProgramExecution instanceof IcfgProgramExecution)) {
					throw new UnsupportedOperationException("Program execution is not " + IcfgProgramExecution.class);
				}
				rcfgProgramExecution = ((IcfgProgramExecution<L>) rcfgProgramExecution)
						.addRelevanceInformation(tac.getAberranceInformation());
				
			}
		}

		if (refinementEngineStats != null) {
			mCegarLoopBenchmark.addRefinementEngineStatistics(refinementEngineStats);
		}
		return new Pair<>(feasibility, rcfgProgramExecution);
	}

	@Override
	protected void constructInterpolantAutomaton() throws AutomataOperationCanceledException {
		mInterpolAutomaton = mRefinementResult.getInfeasibilityProof();

		if (mPref.dumpAutomata()) {
			final String filename =
					new SubtaskIterationIdentifier(mTaskIdentifier, getIteration()) + "_RawFloydHoareAutomaton";
			super.writeAutomatonToFile(mInterpolAutomaton, filename);
		}

		assert isInterpolantAutomatonOfSingleStateType(mInterpolAutomaton);
		if (NON_EA_INDUCTIVITY_CHECK) {
			final boolean inductive = checkInterpolantAutomatonInductivity(mInterpolAutomaton);
			if (!inductive) {
				throw new AssertionError("not inductive");
			}
		}

		assert accepts(getServices(), mInterpolAutomaton, mCounterexample.getWord(),
				false) : "Interpolant automaton broken!: " + mCounterexample.getWord() + " not accepted";

		// FIXME (Dominik 2020-12-19): The assertion below is problematic, because it has side-effects!
		// In particular, NwaFloydHoareValidityCheck calls IncrementalHoareTripleChecker, which in the method
		// unAssertCodeBlock unlocks a ManagedScript. If assertions are disabled, this remains locked. This leads to
		// exceptions if other callers try to lock it. With assertions enabled, the line below causes the ManagedScript
		// to be unlocked and no exceptions occur.
		assert checkInterpolantAutomatonInductivity(mInterpolAutomaton);
	}

	protected static boolean
			isInterpolantAutomatonOfSingleStateType(final INestedWordAutomaton<?, IPredicate> automaton) {
		Class<? extends IPredicate> typeofState = null;
		for (final IPredicate state : automaton.getStates()) {
			if (typeofState == null) {
				typeofState = state.getClass();
			}
			if (state.getClass() != typeofState) {
				return false;
			}
		}
		return true;
	}

	@Override
	protected void finish() {
		final List<Integer> sortedHistogram = mStrategyFactory.getPathProgramCache().computeSortedHistrogram();
		mLogger.info("Path program histogram: " + sortedHistogram);
		final int max = HistogramOfIterable.getMaxOfVisualizationArray(sortedHistogram);
		mCegarLoopBenchmark.reportPathProgramHistogramMaximum(max);
		mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.OverallTime.toString());

	}

	protected final IHoareTripleChecker getHoareTripleChecker() {
		final IHoareTripleChecker refinementHtc = mRefinementResult.getHoareTripleChecker();
		if (refinementHtc != null) {
			return refinementHtc;
		}
		// Use all edges of the interpolant automaton that is already constructed as an
		// initial cache for the Hoare triple checker.
		final HoareTripleCheckerCache initialCache =
				TraceAbstractionUtils.extractHoareTriplesfromAutomaton(mRefinementResult.getInfeasibilityProof());
		return HoareTripleCheckerUtils.constructEfficientHoareTripleCheckerWithCaching(getServices(),
				mPref.getHoareTripleChecks(), mCsToolkit, mRefinementResult.getPredicateUnifier(), initialCache);
	}

	protected INwaOutgoingLetterAndTransitionProvider<L, IPredicate> enhanceInterpolantAutomaton(
			final InterpolantAutomatonEnhancement enhanceMode, final IPredicateUnifier predicateUnifier,
			final IHoareTripleChecker htc, final NestedWordAutomaton<L, IPredicate> interpolantAutomaton) {
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahend;
		if (enhanceMode == InterpolantAutomatonEnhancement.NONE) {
			subtrahend = interpolantAutomaton;
		} else {
			final AbstractInterpolantAutomaton<L> ia = constructInterpolantAutomatonForOnDemandEnhancement(
					interpolantAutomaton, predicateUnifier, htc, enhanceMode);
			subtrahend = ia;
			if (mStoreFloydHoareAutomata) {
				mFloydHoareAutomata.add(new Pair<>(ia, predicateUnifier));
			}
		}
		return subtrahend;
	}

	/**
	 *
	 * @return true iff all traces of the path program defined by the counterexample of this iteration were subtracted
	 *         from the abstraction
	 */
	private boolean checkPathProgramRemoval()
			throws AutomataLibraryException, AutomataOperationCanceledException, AssertionError {
		final boolean pathProgramShouldHaveBeenRemoved = mRefinementResult.somePerfectSequenceFound()
				&& mPref.interpolantAutomatonEnhancement() != InterpolantAutomatonEnhancement.NONE;
		if (!pathProgramShouldHaveBeenRemoved) {
			return true;
		}
		final Set<L> counterexampleLetters = mCounterexample.getWord().asSet();
		final PathProgramConstructionResult ppcr =
				PathProgram.constructPathProgram("PathprogramSubtractedCheckIteration" + getIteration(), mIcfg,
						counterexampleLetters, Collections.emptySet());
		final Map<IIcfgTransition<?>, IIcfgTransition<?>> oldTransition2NewTransition =
				ppcr.getOldTransition2NewTransition();
		final Map<IIcfgTransition<?>, IIcfgTransition<?>> newTransition2OldTransition =
				DataStructureUtils.constructReverseMapping(oldTransition2NewTransition);
		final Map<IcfgLocation, IcfgLocation> oldLocation2NewLocation = ppcr.getLocationMapping();
		final PathProgram pp = ppcr.getPathProgram();
		final IcfgLocation errorLoc =
				((ISLPredicate) mCounterexample.getStateSequence().get(mCounterexample.getStateSequence().size() - 1))
						.getProgramPoint();
		final VpAlphabet<L> newVpAlphabet = Cfg2Automaton.extractVpAlphabet(mIcfg, !mPref.interprocedural());
		final VpAlphabet<L> oldVpAlphabet = new VpAlphabet<>(newVpAlphabet, (Map<L, L>) newTransition2OldTransition);
		final INestedWordAutomaton<L, IPredicate> pathProgramAutomaton =
				Cfg2Automaton.constructAutomatonWithDebugPredicates(getServices(), pp, mPredicateFactoryResultChecking,
						Collections.singleton(oldLocation2NewLocation.get(errorLoc)), mPref.interprocedural(),
						newVpAlphabet, newTransition2OldTransition);
		assert pathProgramAutomaton.getFinalStates().size() == 1 : "incorrect accepting states";
		final INestedWordAutomaton<L, IPredicate> intersection =
				new Intersect<>(new AutomataLibraryServices(getServices()), mPredicateFactoryResultChecking,
						(INwaOutgoingLetterAndTransitionProvider<L, IPredicate>) mAbstraction, pathProgramAutomaton)
								.getResult();
		return new IsEmpty<>(new AutomataLibraryServices(getServices()), intersection).getResult();
	}

	protected void dumpOrAppendAutomatonForReuseIfEnabled(
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> automaton,
			final IPredicateUnifier predicateUnifier) {
		if (mPref.dumpOnlyReuseAutomata()) {

			mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.DumpTime);
			mLogger.info("Dumping reuse automata for " + mTaskIdentifier.toString() + " " + automaton.getClass());
			final String filename = mTaskIdentifier + "-reuse";
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> printedAutomaton;
			final AutomataLibraryServices services = new AutomataLibraryServices(getServices());
			final boolean addPredicateImplicationInformation = true;
			if (addPredicateImplicationInformation) {
				final HashRelation<IPredicate, IPredicate> outgoingEpsilonTransitions =
						predicateUnifier.getCoverageRelation().getCopyOfImplicationRelation();
				INestedWordAutomaton<L, IPredicate> backingNestedWordAutomaton;
				try {
					backingNestedWordAutomaton = new RemoveDeadEnds<>(services, automaton).getResult();
					if (backingNestedWordAutomaton.getStates().isEmpty()) {
						mLogger.warn("Automaton with emtpy language -- ommited dump");
						mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.DumpTime);
						return;
					}
				} catch (final AutomataOperationCanceledException e) {
					throw new AssertionError(e);
				}
				printedAutomaton =
						new EpsilonNestedWordAutomaton<>(backingNestedWordAutomaton, outgoingEpsilonTransitions);
			} else {
				printedAutomaton = automaton;
			}
			new AutomatonDefinitionPrinter<String, String>(services, "nwa" + getIteration(),
					mPref.dumpPath() + File.separator + filename, mPrintAutomataLabeling, "", !mFirstReuseDump,
					printedAutomaton);
			mFirstReuseDump = false;
			mLogger.info("Finished dumping");
			mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.DumpTime);
		}
	}

	protected void checkEnhancement(
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> inputInterpolantAutomaton,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> interpolantAutomaton)
			throws AutomataLibraryException, AssertionError, AutomataOperationCanceledException {
		if (!new Accepts<>(new AutomataLibraryServices(getServices()), interpolantAutomaton,
				(NestedWord<L>) mCounterexample.getWord(), true, false).getResult()) {

			final boolean isOriginalBroken = !new Accepts<>(new AutomataLibraryServices(getServices()),
					inputInterpolantAutomaton, (NestedWord<L>) mCounterexample.getWord(), true, false).getResult();
			try {
				debugLogBrokenInterpolantAutomaton(inputInterpolantAutomaton, interpolantAutomaton, mCounterexample);
			} catch (final Error e) {
				// suppress any exception, throw assertion error instead
			}
			throw new AssertionError("enhanced interpolant automaton in iteration " + getIteration()
					+ " broken: counterexample of length " + mCounterexample.getLength() + " not accepted"
					+ (isOriginalBroken ? " (original was already broken)" : " (original is ok)"));
		}
		assert isInterpolantAutomatonOfSingleStateType(
				new RemoveUnreachable<>(new AutomataLibraryServices(getServices()), interpolantAutomaton).getResult());
		assert checkInterpolantAutomatonInductivity(
				new RemoveUnreachable<>(new AutomataLibraryServices(getServices()), interpolantAutomaton).getResult());
	}

	private void debugLogBrokenInterpolantAutomaton(
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> interpolantAutomaton,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> enhancedInterpolantAutomaton,
			final IRun<L, ?> counterexample) {
		mLogger.fatal("--");
		mLogger.fatal("enhanced interpolant automaton broken: counterexample not accepted");
		mLogger.fatal("word:");
		for (final L letter : counterexample.getWord()) {
			mLogger.fatal(letter);
		}
		mLogger.fatal("original automaton:");
		mLogger.fatal(interpolantAutomaton);
		mLogger.fatal("enhanced automaton:");
		mLogger.fatal(enhancedInterpolantAutomaton);
		mLogger.fatal("--");
	}

	protected AbstractInterpolantAutomaton<L> constructInterpolantAutomatonForOnDemandEnhancement(
			final NestedWordAutomaton<L, IPredicate> inputInterpolantAutomaton,
			final IPredicateUnifier predicateUnifier, final IHoareTripleChecker htc,
			final InterpolantAutomatonEnhancement enhanceMode) {
		final AbstractInterpolantAutomaton<L> result;
		switch (enhanceMode) {
		case NONE:
			throw new IllegalArgumentException("In setting NONE we will not do any enhancement");
		case PREDICATE_ABSTRACTION:
		case PREDICATE_ABSTRACTION_CONSERVATIVE:
		case PREDICATE_ABSTRACTION_CANNIBALIZE:
			result = constructInterpolantAutomatonForOnDemandEnhancementPredicateAbstraction(inputInterpolantAutomaton,
					predicateUnifier, htc, enhanceMode);
			break;
		case EAGER:
		case NO_SECOND_CHANCE:
		case EAGER_CONSERVATIVE:
			result = constructInterpolantAutomatonForOnDemandEnhancementEager(inputInterpolantAutomaton,
					predicateUnifier, htc, enhanceMode);
			break;
		default:
			throw new UnsupportedOperationException("unknown " + enhanceMode);
		}
		return result;
	}

	private NondeterministicInterpolantAutomaton<L> constructInterpolantAutomatonForOnDemandEnhancementEager(
			final NestedWordAutomaton<L, IPredicate> inputInterpolantAutomaton,
			final IPredicateUnifier predicateUnifier, final IHoareTripleChecker htc,
			final InterpolantAutomatonEnhancement enhanceMode) {
		final boolean conservativeSuccessorCandidateSelection =
				enhanceMode == InterpolantAutomatonEnhancement.EAGER_CONSERVATIVE;
		final boolean secondChance = enhanceMode != InterpolantAutomatonEnhancement.NO_SECOND_CHANCE;
		return new NondeterministicInterpolantAutomaton<>(getServices(), mCsToolkit, htc, inputInterpolantAutomaton,
				predicateUnifier, conservativeSuccessorCandidateSelection, secondChance);
	}

	private DeterministicInterpolantAutomaton<L>
			constructInterpolantAutomatonForOnDemandEnhancementPredicateAbstraction(
					final NestedWordAutomaton<L, IPredicate> inputInterpolantAutomaton,
					final IPredicateUnifier predicateUnifier, final IHoareTripleChecker htc,
					final InterpolantAutomatonEnhancement enhanceMode) {
		final boolean conservativeSuccessorCandidateSelection =
				enhanceMode == InterpolantAutomatonEnhancement.PREDICATE_ABSTRACTION_CONSERVATIVE;
		final boolean cannibalize = enhanceMode == InterpolantAutomatonEnhancement.PREDICATE_ABSTRACTION_CANNIBALIZE;
		return new DeterministicInterpolantAutomaton<>(getServices(), mCsToolkit, htc, inputInterpolantAutomaton,
				predicateUnifier, conservativeSuccessorCandidateSelection, cannibalize);
	}

	@Override
	public IElement getArtifact() {
		if (mPref.artifact() == Artifact.ABSTRACTION || mPref.artifact() == Artifact.INTERPOLANT_AUTOMATON
				|| mPref.artifact() == Artifact.NEG_INTERPOLANT_AUTOMATON) {

			if (mArtifactAutomaton == null) {
				mLogger.warn("Preferred Artifact not available," + " visualizing the RCFG instead");
				return mIcfg;
			}
			try {
				return mArtifactAutomaton.transformToUltimateModel(new AutomataLibraryServices(getServices()));
			} catch (final AutomataOperationCanceledException e) {
				return null;
			}
		}
		if (mPref.artifact() == Artifact.RCFG) {
			return mIcfg;
		}
		throw new IllegalArgumentException();
	}

	protected boolean accepts(final IUltimateServiceProvider services,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> nia, final Word<L> word,
			final boolean checkAlsoForAcceptanceOfSomePrefix) throws AutomataOperationCanceledException {
		try {
			return new Accepts<>(new AutomataLibraryServices(services), nia, NestedWord.nestedWord(word),
					checkAlsoForAcceptanceOfSomePrefix, false).getResult();
		} catch (final AutomataOperationCanceledException e) {
			throw e;
		} catch (final AutomataLibraryException e) {
			throw new AssertionError(e);
		}
	}

	@Override
	public Set<Pair<AbstractInterpolantAutomaton<L>, IPredicateUnifier>> getFloydHoareAutomata() {
		if (mStoreFloydHoareAutomata) {
			return mFloydHoareAutomata;
		}
		throw new IllegalStateException("Floyd-Hoare automata have not been stored");
	}

	protected boolean checkInterpolantAutomatonInductivity(final INestedWordAutomaton<L, IPredicate> automaton) {
		return NwaFloydHoareValidityCheck.forInterpolantAutomaton(mServices, mCsToolkit.getManagedScript(),
				new IncrementalHoareTripleChecker(mCsToolkit, false), mRefinementResult.getPredicateUnifier(),
				automaton, true).getResult();
	}

	public IPreconditionProvider getPreconditionProvider() {
		return IPreconditionProvider.constructDefaultPreconditionProvider();
	}

	public IPostconditionProvider getPostconditionProvider() {
		return IPostconditionProvider.constructDefaultPostconditionProvider();
	}

	private class TimeoutRefinementEngineResult
			extends BasicRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> {

		public TimeoutRefinementEngineResult(final Lazy<IHoareTripleChecker> htc,
				final Lazy<IPredicateUnifier> predicateUnifier) {
			super(LBool.UNKNOWN, null, null, false, Collections.emptyList(), htc, predicateUnifier);
		}

	}
}
