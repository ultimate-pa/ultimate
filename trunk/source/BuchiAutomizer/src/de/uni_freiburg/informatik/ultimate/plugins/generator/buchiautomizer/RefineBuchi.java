/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BuchiAutomizer plug-in.
 * 
 * The ULTIMATE BuchiAutomizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BuchiAutomizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BuchiAutomizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BuchiAutomizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BuchiAutomizer plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter.Format;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiAccepts;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiComplementFKV;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiDifferenceFKV;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiDifferenceNCSB;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiIntersect;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.MultiOptimizationLevelRankingGenerator.FkvOptimization;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsDeterministic;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsSemiDeterministic;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.PreferenceInitializer.BuchiComplementationConstruction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.PreferenceInitializer.BuchiInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.NondeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.InductivityCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.UnsatCores;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.InterpolatingTraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.InterpolatingTraceCheckerCraig;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerSpWp;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerUtils;
import de.uni_freiburg.informatik.ultimate.util.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.util.ToolchainCanceledException;

public class RefineBuchi {

	protected final ILogger mLogger;
	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;

	/**
	 * Intermediate layer to encapsulate communication with SMT solvers.
	 */
	private final CfgSmtToolkit mCsToolkit;
	private final PredicateFactory mPredicateFactory;
	
	private final BoogieIcfgContainer mICfgContainer;

	private final boolean mDumpAutomata;
	private final boolean mDifference;
	private final PredicateFactoryForInterpolantAutomata mStateFactoryInterpolAutom;
	private final PredicateFactoryRefinement mStateFactoryForRefinement;
	private final boolean mUseDoubleDeckers;
	private final String mDumpPath;
	private final Format mFormat;
	private final InterpolationTechnique mInterpolation;
	private BackwardCoveringInformation mBci;
	/**
	 * Interpolant automaton of this iteration.
	 */
	protected INestedWordAutomatonSimple<CodeBlock, IPredicate> mInterpolAutomatonUsedInRefinement;

	private final IUltimateServiceProvider mServices;

	public RefineBuchi(final BoogieIcfgContainer icfgContainer, final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory, final boolean dumpAutomata, final boolean difference,
			final PredicateFactoryForInterpolantAutomata stateFactoryInterpolAutom, final PredicateFactoryRefinement stateFactoryForRefinement,
			final boolean useDoubleDeckers, final String dumpPath, final Format format, final InterpolationTechnique interpolation, final IUltimateServiceProvider services,
			final ILogger logger, final SimplificationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique) {
		super();
		mServices = services;
		mLogger = logger;
		mICfgContainer = icfgContainer;
		mCsToolkit = csToolkit;
		mPredicateFactory = predicateFactory;
		mDumpAutomata = dumpAutomata;
		mDifference = difference;
		mStateFactoryInterpolAutom = stateFactoryInterpolAutom;
		mStateFactoryForRefinement = stateFactoryForRefinement;
		mUseDoubleDeckers = useDoubleDeckers;
		mDumpPath = dumpPath;
		mFormat = format;
		mInterpolation = interpolation;
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
	}

	class RefinementSetting {
		private final BuchiInterpolantAutomaton mInterpolantAutomaton;
		private final boolean mBouncerStem;
		private final boolean mBouncerLoop;
		private final boolean mScroogeNondeterminismStem;
		private final boolean mScroogeNondeterminismLoop;
		private final boolean mCannibalizeLoop;

		public RefinementSetting(final BuchiInterpolantAutomaton interpolantAutomaton, final boolean bouncerStem, final boolean bouncerLoop,
				final boolean scroogeNondeterminismStem, final boolean scroogeNondeterminismLoop, final boolean cannibalizeLoop) {
			super();
			mInterpolantAutomaton = interpolantAutomaton;
			mBouncerStem = bouncerStem;
			mBouncerLoop = bouncerLoop;
			mScroogeNondeterminismStem = scroogeNondeterminismStem;
			mScroogeNondeterminismLoop = scroogeNondeterminismLoop;
			mCannibalizeLoop = cannibalizeLoop;
		}

		public BuchiInterpolantAutomaton getInterpolantAutomaton() {
			return mInterpolantAutomaton;
		}

		public boolean isBouncerStem() {
			return mBouncerStem;
		}

		public boolean isBouncerLoop() {
			return mBouncerLoop;
		}

		public boolean isScroogeNondeterminismStem() {
			return mScroogeNondeterminismStem;
		}

		public boolean isScroogeNondeterminismLoop() {
			return mScroogeNondeterminismLoop;
		}

		public boolean cannibalizeLoop() {
			return mCannibalizeLoop;
		}
		
		public boolean isAlwaysSemiDeterministic() {
			return !isScroogeNondeterminismLoop();
		}
		
		@Override
		public String toString() {
			return "RefinementSetting [mInterpolantAutomaton="
					+ mInterpolantAutomaton + ", mBouncerStem="
					+ mBouncerStem + ", mBouncerLoop=" + mBouncerLoop
					+ ", mScroogeNondeterminismStem="
					+ mScroogeNondeterminismStem
					+ ", mScroogeNondeterminismLoop="
					+ mScroogeNondeterminismLoop + ", mCannibalizeLoop="
					+ mCannibalizeLoop + "]";
		}


	}

	public INestedWordAutomatonSimple<CodeBlock, IPredicate> getInterpolAutomatonUsedInRefinement() {
		return mInterpolAutomatonUsedInRefinement;
	}

	public BackwardCoveringInformation getBci() {
		return mBci;
	}

	INestedWordAutomaton<CodeBlock, IPredicate> refineBuchi(
			final INestedWordAutomatonSimple<CodeBlock, IPredicate> abstraction,
			final NestedLassoRun<CodeBlock, IPredicate> mCounterexample, final int mIteration, final RefinementSetting setting,
			final BinaryStatePredicateManager bspm, final BuchiModGlobalVarManager buchiModGlobalVarManager,
			final InterpolationTechnique interpolation, final BuchiCegarLoopBenchmarkGenerator benchmarkGenerator,
			final BuchiComplementationConstruction complementationConstruction)
			throws AutomataLibraryException {
		final NestedWord<CodeBlock> stem = mCounterexample.getStem().getWord();
		// if (emptyStem(mCounterexample)) {
		// stem = mCounterexample.getLoop().getWord();
		// } else {
		// stem = mCounterexample.getStem().getWord();
		// }
		final NestedWord<CodeBlock> loop = mCounterexample.getLoop().getWord();

		assert !bspm.getStemPrecondition().getFormula().toString().equals("false");
		assert !bspm.getHondaPredicate().getFormula().toString().equals("false");
		assert !bspm.getRankEqAndSi().getFormula().toString().equals("false");
		final PredicateUnifier pu = new PredicateUnifier(mServices, mCsToolkit.getManagedScript(), mPredicateFactory, 
				mICfgContainer.getBoogie2SMT().getBoogie2SmtSymbolTable(), mSimplificationTechnique, mXnfConversionTechnique, bspm.getStemPrecondition(),
				bspm.getHondaPredicate(), bspm.getRankEqAndSi(), bspm.getStemPostcondition());
		IPredicate[] stemInterpolants;
		InterpolatingTraceChecker traceChecker;
		if (BuchiCegarLoop.emptyStem(mCounterexample)) {
			stemInterpolants = null;
		} else {

			traceChecker = constructTraceChecker(bspm.getStemPrecondition(), bspm.getStemPostcondition(), stem,
					mCsToolkit, buchiModGlobalVarManager, pu, mInterpolation);
			final LBool stemCheck = traceChecker.isCorrect();
			if (stemCheck == LBool.UNSAT) {
				stemInterpolants = traceChecker.getInterpolants();
			} else {
				throw new AssertionError("incorrect predicates - stem");
			}
		}

		traceChecker = constructTraceChecker(bspm.getRankEqAndSi(), bspm.getHondaPredicate(), loop, mCsToolkit,
				buchiModGlobalVarManager, pu, mInterpolation);
		final LBool loopCheck = traceChecker.isCorrect();
		IPredicate[] loopInterpolants;
		if (loopCheck == LBool.UNSAT) {
			loopInterpolants = traceChecker.getInterpolants();
		} else {
			throw new AssertionError("incorrect predicates - loop");
		}
		mBci = TraceCheckerUtils.computeCoverageCapability(mServices, traceChecker, mLogger);

		NestedWordAutomaton<CodeBlock, IPredicate> mInterpolAutomaton = constructBuchiInterpolantAutomaton(
				bspm.getStemPrecondition(), stem, stemInterpolants, bspm.getHondaPredicate(), loop, loopInterpolants,
				abstraction);
		if (mDumpAutomata) {
			
			final String filename = mICfgContainer.getFilename() + "_" + "InterpolantAutomatonBuchi" + mIteration;
			final String message = setting.toString();
			BuchiCegarLoop.writeAutomatonToFile(mServices, mInterpolAutomaton, mDumpPath, filename, mFormat, message);
		}

//		BuchiHoareTripleChecker bhtc = new BuchiHoareTripleChecker(new MonolithicHoareTripleChecker(mCsToolkit));
		final BuchiHoareTripleChecker bhtc = new BuchiHoareTripleChecker(new IncrementalHoareTripleChecker(mCsToolkit));
		bhtc.putDecreaseEqualPair(bspm.getHondaPredicate(), bspm.getRankEqAndSi());
		assert (new InductivityCheck(mServices, mInterpolAutomaton, false, true, bhtc)).getResult();
		assert (new BuchiAccepts<CodeBlock, IPredicate>(new AutomataLibraryServices(mServices), mInterpolAutomaton, mCounterexample.getNestedLassoWord()))
				.getResult();
		switch (setting.getInterpolantAutomaton()) {
		case LassoAutomaton:
			mInterpolAutomatonUsedInRefinement = mInterpolAutomaton;
			break;
		case EagerNondeterminism:
			if (!mInterpolAutomaton.getStates().contains(pu.getTruePredicate())) {
				mInterpolAutomaton.addState(false, false, pu.getTruePredicate());
			}
			if (!mInterpolAutomaton.getStates().contains(pu.getFalsePredicate())) {
				mInterpolAutomaton.addState(false, true, pu.getFalsePredicate());
			}
			mInterpolAutomatonUsedInRefinement = new NondeterministicInterpolantAutomaton(mServices, mCsToolkit,
					bhtc, abstraction, mInterpolAutomaton, pu, mLogger, false, true);
			break;
		case ScroogeNondeterminism:
		case Deterministic:
			Set<IPredicate> stemInterpolantsForRefinement;
			if (BuchiCegarLoop.emptyStem(mCounterexample)) {
				stemInterpolantsForRefinement = Collections.emptySet();
			} else {
				if (setting.cannibalizeLoop()) {
					stemInterpolantsForRefinement = pu.cannibalizeAll(false, stemInterpolants);
				} else {
					stemInterpolantsForRefinement = new HashSet<IPredicate>(Arrays.asList(stemInterpolants));
				}
			}
			Set<IPredicate> loopInterpolantsForRefinement;
			if (setting.cannibalizeLoop()) {
				try {
					loopInterpolantsForRefinement = pu.cannibalizeAll(false, loopInterpolants);
					loopInterpolantsForRefinement.addAll(pu.cannibalize(false, bspm.getRankEqAndSi().getFormula()));

					final LoopCannibalizer lc = new LoopCannibalizer(mCounterexample, loopInterpolantsForRefinement, bspm, pu,
							mCsToolkit, buchiModGlobalVarManager, interpolation, 
							mICfgContainer.getBoogie2SMT().getBoogie2SmtSymbolTable(),
							mServices, mSimplificationTechnique, mXnfConversionTechnique);
					loopInterpolantsForRefinement = lc.getResult();
				} catch (final ToolchainCanceledException tce) {
					final String taskDescription = "loop cannibalization";
					tce.addRunningTaskInfo(new RunningTaskInfo(getClass(), taskDescription));
					throw tce;
				}
			} else {
				loopInterpolantsForRefinement = new HashSet<IPredicate>(Arrays.asList(loopInterpolants));
				loopInterpolantsForRefinement.add(bspm.getRankEqAndSi());
			}

			mInterpolAutomatonUsedInRefinement = new BuchiInterpolantAutomatonBouncer(mCsToolkit, mPredicateFactory, bspm, bhtc,
					BuchiCegarLoop.emptyStem(mCounterexample), stemInterpolantsForRefinement,
					loopInterpolantsForRefinement, BuchiCegarLoop.emptyStem(mCounterexample) ? null
							: stem.getSymbol(stem.length() - 1), loop.getSymbol(loop.length() - 1), abstraction,
					setting.isScroogeNondeterminismStem(), setting.isScroogeNondeterminismLoop(),
					setting.isBouncerStem(), setting.isBouncerLoop(), mStateFactoryInterpolAutom, pu, pu,
					pu.getFalsePredicate(), mServices, mSimplificationTechnique, mXnfConversionTechnique,
					mICfgContainer.getBoogie2SMT().getBoogie2SmtSymbolTable());
			break;
		default:
			throw new UnsupportedOperationException("unknown automaton");
		}
		final IStateDeterminizer<CodeBlock, IPredicate> stateDeterminizer = new PowersetDeterminizer<CodeBlock, IPredicate>(
				mInterpolAutomatonUsedInRefinement, mUseDoubleDeckers, mStateFactoryInterpolAutom);
		INestedWordAutomaton<CodeBlock, IPredicate> newAbstraction;
		if (mDifference) {
			if (complementationConstruction == BuchiComplementationConstruction.Ncsb) {
				if (setting.isAlwaysSemiDeterministic()) {
					newAbstraction = nsbcDifference(abstraction, setting, benchmarkGenerator);
				} else {
					final FkvOptimization optimization = FkvOptimization.ELASTIC;
					newAbstraction = rankBasedOptimization(abstraction, setting, benchmarkGenerator, stateDeterminizer,
							optimization);
				}
			} else {
				final FkvOptimization optimization;
				switch (complementationConstruction) {
				case Elastic:
					optimization = FkvOptimization.ELASTIC;
					break;
				case Ncsb:
					throw new AssertionError("should be handled elsewhere");
				case HeiMat2:
					optimization = FkvOptimization.HEIMAT2;
					break;
				case TightBasic:
					optimization = FkvOptimization.TIGHT_LEVEL_RANKINGS;
					break;
				case TightHighEven:
					optimization = FkvOptimization.HIGH_EVEN;
					break;
				case TightRO:
					optimization = FkvOptimization.SCHEWE;
					break;
				default:
					throw new AssertionError("unknown optimization");
				}
				newAbstraction = rankBasedOptimization(abstraction, setting, benchmarkGenerator, stateDeterminizer,
						optimization);
			}

			// s_Logger.warn("START: minimization test");
			// BuchiComplementFKVNwa<CodeBlock, IPredicate> compl1 =
			// diff.getSndComplemented();
			// INestedWordAutomatonOldApi<CodeBlock, IPredicate> compl = (new
			// RemoveNonLiveStates<CodeBlock, IPredicate>(compl1)).getResult();
			// BuchiClosureNwa<CodeBlock, IPredicate> bc = (new
			// BuchiClosureNwa<CodeBlock, IPredicate>(compl));
			// MinimizeSevpa<CodeBlock, IPredicate> minimizeOp =
			// new MinimizeSevpa<CodeBlock,
			// IPredicate>(bc,null,false,false,mStateFactoryInterpolAutom);
			// s_Logger.warn("END: minimization test");
			// INestedWordAutomatonOldApi<CodeBlock, IPredicate> minimizedOp =
			// minimizeOp.getResult();
			//
			// BuchiIntersect<CodeBlock, IPredicate> newDiff =
			// new BuchiIntersect<CodeBlock, IPredicate>(
			// mAbstraction, minimizedOp, mStateFactoryForRefinement);
			// s_Logger.warn("oldDiff size" +
			// diff.getResult().sizeInformation());
			// s_Logger.warn("newDiff size" +
			// (newDiff.getResult()).sizeInformation());

			
		} else {
			final BuchiComplementFKV<CodeBlock, IPredicate> complNwa = new BuchiComplementFKV<CodeBlock, IPredicate>(
					new AutomataLibraryServices(mServices),
					mInterpolAutomatonUsedInRefinement, stateDeterminizer);
			finishComputation(mInterpolAutomatonUsedInRefinement, setting);
			benchmarkGenerator.reportHighestRank(complNwa.getHighestRank());
			assert (complNwa.checkResult(mStateFactoryInterpolAutom));
			final INestedWordAutomatonSimple<CodeBlock, IPredicate> complement = complNwa.getResult();
			assert !(new BuchiAccepts<CodeBlock, IPredicate>(new AutomataLibraryServices(mServices), complement, mCounterexample.getNestedLassoWord()))
					.getResult();
			final BuchiIntersect<CodeBlock, IPredicate> interNwa = new BuchiIntersect<CodeBlock, IPredicate>(new AutomataLibraryServices(mServices), abstraction,
					complement, mStateFactoryForRefinement);
			assert (interNwa.checkResult(mStateFactoryInterpolAutom));
			newAbstraction = interNwa.getResult();
		}
		// INestedWordAutomatonOldApi<CodeBlock, IPredicate> oldApi = (new
		// RemoveUnreachable<CodeBlock,
		// IPredicate>(mInterpolAutomatonUsedInRefinement)).getResult();
		benchmarkGenerator.addEdgeCheckerData(bhtc.getEdgeCheckerBenchmark());
		mInterpolAutomaton = null;
		final boolean isUseful = isUsefulInterpolantAutomaton(mInterpolAutomatonUsedInRefinement, mCounterexample);
		if (!isUseful) {
			return null;
		}

		// assert (new BuchiAccepts<CodeBlock,
		// IPredicate>(oldApi,mCounterexample.getNestedLassoWord())).getResult()
		// : "interpolant automaton does not accept lasso.";
		// assert !(new BuchiAccepts<CodeBlock,
		// IPredicate>(newAbstraction,mCounterexample.getNestedLassoWord())).getResult()
		// : "no progress";
		if (mDumpAutomata) {
			final String automatonString;
			if (mInterpolAutomatonUsedInRefinement.getCallAlphabet().isEmpty()) {
				automatonString = "interpolBuchiAutomatonUsedInRefinement";
			} else {
				automatonString = "interpolBuchiNestedWordAutomatonUsedInRefinement";
			}
			final String filename = mICfgContainer.getFilename() + "_" + automatonString + mIteration + "after";
			final String message = setting.toString();
			BuchiCegarLoop.writeAutomatonToFile(mServices, mInterpolAutomatonUsedInRefinement, mDumpPath, filename, mFormat, message);
		}
		final boolean tacasDump = false;
		if (tacasDump){
			final String determinicity;
			final boolean isSemiDeterministic = (new IsSemiDeterministic<CodeBlock, IPredicate>(new AutomataLibraryServices(mServices), mInterpolAutomatonUsedInRefinement)).getResult();
			final boolean isDeterministic = (new IsDeterministic<CodeBlock, IPredicate>(new AutomataLibraryServices(mServices), mInterpolAutomatonUsedInRefinement)).getResult();
			if (isDeterministic) {
				determinicity = "deterministic";
				assert isSemiDeterministic : "but semi deterministic";
			} else if (isSemiDeterministic) {
				determinicity = "semideterministic";
			} else {
				determinicity = "nondeterministic";
			}
			final String automatonString;
			if (mInterpolAutomatonUsedInRefinement.getCallAlphabet().isEmpty()) {
				automatonString = "interpolBuchiAutomatonUsedInRefinement";
			} else {
				automatonString = "interpolBuchiNestedWordAutomatonUsedInRefinement";
			}
			final String filename = mICfgContainer.getFilename() + "_" + determinicity + automatonString + mIteration + "after";
			final String message = setting.toString();
			BuchiCegarLoop.writeAutomatonToFile(mServices, mInterpolAutomatonUsedInRefinement, mDumpPath, filename, mFormat, message);

		}
		return newAbstraction;
	}
	
	private INestedWordAutomaton<CodeBlock, IPredicate> nsbcDifference(
			final INestedWordAutomatonSimple<CodeBlock, IPredicate> abstraction, final RefinementSetting setting,
			final BuchiCegarLoopBenchmarkGenerator benchmarkGenerator) throws AutomataLibraryException {
		INestedWordAutomaton<CodeBlock, IPredicate> newAbstraction;
		final BuchiDifferenceNCSB<CodeBlock, IPredicate> diff = new BuchiDifferenceNCSB<CodeBlock, IPredicate>(new AutomataLibraryServices(mServices),
				mStateFactoryForRefinement, abstraction, mInterpolAutomatonUsedInRefinement);
		finishComputation(mInterpolAutomatonUsedInRefinement, setting);
		benchmarkGenerator.reportHighestRank(3);
		assert diff.checkResult(mStateFactoryInterpolAutom);
		newAbstraction = diff.getResult();
		return newAbstraction;
	}

	private INestedWordAutomaton<CodeBlock, IPredicate> rankBasedOptimization(
			final INestedWordAutomatonSimple<CodeBlock, IPredicate> abstraction, final RefinementSetting setting,
			final BuchiCegarLoopBenchmarkGenerator benchmarkGenerator,
			final IStateDeterminizer<CodeBlock, IPredicate> stateDeterminizer, final FkvOptimization optimization)
					throws AutomataLibraryException {
		INestedWordAutomaton<CodeBlock, IPredicate> newAbstraction;
		final BuchiDifferenceFKV<CodeBlock, IPredicate> diff = new BuchiDifferenceFKV<CodeBlock, IPredicate>(new AutomataLibraryServices(mServices),
				mStateFactoryForRefinement, abstraction, mInterpolAutomatonUsedInRefinement, stateDeterminizer,
				optimization,
				Integer.MAX_VALUE);
		finishComputation(mInterpolAutomatonUsedInRefinement, setting);
		benchmarkGenerator.reportHighestRank(diff.getHighestRank());
		assert diff.checkResult(mStateFactoryInterpolAutom);
		newAbstraction = diff.getResult();
		return newAbstraction;
	}

	private InterpolatingTraceChecker constructTraceChecker(final IPredicate precond, final IPredicate postcond,
			final NestedWord<CodeBlock> word, final CfgSmtToolkit csToolkit, final BuchiModGlobalVarManager buchiModGlobalVarManager,
			final PredicateUnifier pu, final InterpolationTechnique interpolation) {
		final InterpolatingTraceChecker itc;
		switch (mInterpolation) {
		case Craig_NestedInterpolation:
		case Craig_TreeInterpolation: {
			itc = new InterpolatingTraceCheckerCraig(precond, postcond, new TreeMap<Integer, IPredicate>(), word,
					mCsToolkit, /*
					 * TODO: When Matthias
					 * introduced this parameter he
					 * set the argument to AssertCodeBlockOrder.NOT_INCREMENTALLY.
					 * Check if you want to set this
					 * to a different value.
					 */AssertCodeBlockOrder.NOT_INCREMENTALLY,
					mServices, false, pu, interpolation, true, mXnfConversionTechnique, 
					 mSimplificationTechnique);
			break;
		}
		case ForwardPredicates:
		case BackwardPredicates:
		case FPandBP: {
			itc = new TraceCheckerSpWp(precond, postcond, new TreeMap<Integer, IPredicate>(),
					word, mCsToolkit, /*
					 * TODO: When Matthias
					 * introduced this parameter he
					 * set the argument to AssertCodeBlockOrder.NOT_INCREMENTALLY.
					 * Check if you want to set this
					 * to a different value.
					 */AssertCodeBlockOrder.NOT_INCREMENTALLY,
					UnsatCores.CONJUNCT_LEVEL,
					 true, mServices, false, pu, interpolation, mCsToolkit.getManagedScript(), mXnfConversionTechnique, 
					 mSimplificationTechnique);
			break;
		}
		default:
			throw new UnsupportedOperationException("unsupported interpolation");
		}
		if (itc.getToolchainCancelledExpection() != null) {
			throw itc.getToolchainCancelledExpection();
		}
		return itc;
	}

	private boolean isUsefulInterpolantAutomaton(
			final INestedWordAutomatonSimple<CodeBlock, IPredicate> interpolAutomatonUsedInRefinement,
			final NestedLassoRun<CodeBlock, IPredicate> counterexample) throws AutomataLibraryException {
		INestedWordAutomatonSimple<CodeBlock, IPredicate> oldApi;
		oldApi = (new RemoveUnreachable<CodeBlock, IPredicate>(new AutomataLibraryServices(mServices), interpolAutomatonUsedInRefinement)).getResult();
		final NestedWord<CodeBlock> stem = counterexample.getStem().getWord();
		final NestedWord<CodeBlock> loop = counterexample.getLoop().getWord();
		final NestedWord<CodeBlock> stemAndLoop = stem.concatenate(loop);
		final NestedLassoWord<CodeBlock> stemExtension = new NestedLassoWord<CodeBlock>(stemAndLoop, loop);
		final NestedWord<CodeBlock> loopAndLoop = loop.concatenate(loop);
		final NestedLassoWord<CodeBlock> loopExtension = new NestedLassoWord<CodeBlock>(stem, loopAndLoop);
		final boolean wordAccepted = (new BuchiAccepts<CodeBlock, IPredicate>(new AutomataLibraryServices(mServices), oldApi, counterexample.getNestedLassoWord()))
				.getResult();
		if (!wordAccepted) {
			mLogger.info("Bad chosen interpolant automaton: word not accepted");
			return false;
		}
		// 2015-01-14 Matthias: word, stemExtension, and loopExtension are only
		// different representations of the same word. The following lines
		// do not make any sense (but might be helpful to reveal a bug.
		final boolean stemExtensionAccepted = (new BuchiAccepts<CodeBlock, IPredicate>(new AutomataLibraryServices(mServices), oldApi, stemExtension)).getResult();
		if (!stemExtensionAccepted) {
			throw new AssertionError("Bad chosen interpolant automaton: stem extension not accepted");
//			mLogger.info("Bad chosen interpolant automaton: stem extension not accepted");
//			return false;
		}
		final boolean loopExtensionAccepted = (new BuchiAccepts<CodeBlock, IPredicate>(new AutomataLibraryServices(mServices), oldApi, loopExtension)).getResult();
		if (!loopExtensionAccepted) {
			throw new AssertionError("Bad chosen interpolant automaton: loop extension not accepted");
//			mLogger.info("Bad chosen interpolant automaton: loop extension not accepted");
//			return false;
		}
		return true;
	}

	private void finishComputation(final INestedWordAutomatonSimple<CodeBlock, IPredicate> interpolantAutomaton,
			final RefinementSetting setting) {
		switch (setting.getInterpolantAutomaton()) {
		case LassoAutomaton:
			// do nothing
			break;
		case EagerNondeterminism:
			((NondeterministicInterpolantAutomaton) interpolantAutomaton).switchToReadonlyMode();
			break;
		case ScroogeNondeterminism:
		case Deterministic:
			((BuchiInterpolantAutomatonBouncer) interpolantAutomaton).switchToReadonlyMode();
			break;
		default:
			throw new UnsupportedOperationException("unknown automaton");
		}
	}

	private NestedWordAutomaton<CodeBlock, IPredicate> constructBuchiInterpolantAutomaton(final IPredicate precondition,
			final NestedWord<CodeBlock> stem, final IPredicate[] stemInterpolants, final IPredicate honda, final NestedWord<CodeBlock> loop,
			final IPredicate[] loopInterpolants, final INestedWordAutomatonSimple<CodeBlock, IPredicate> abstraction) {
		final NestedWordAutomaton<CodeBlock, IPredicate> result = new NestedWordAutomaton<CodeBlock, IPredicate>(
				new AutomataLibraryServices(mServices),
				abstraction.getInternalAlphabet(), abstraction.getCallAlphabet(), abstraction.getReturnAlphabet(),
				abstraction.getStateFactory());
		final boolean emptyStem = stem.length() == 0;
		if (emptyStem) {
			result.addState(true, true, honda);
		} else {
			result.addState(true, false, precondition);
			for (int i = 0; i < stemInterpolants.length; i++) {
				addState(stemInterpolants[i], result);
				addTransition(i, precondition, stemInterpolants, honda, stem, result);
			}
			result.addState(false, true, honda);
			addTransition(stemInterpolants.length, precondition, stemInterpolants, honda, stem, result);
		}
		for (int i = 0; i < loopInterpolants.length; i++) {
			addState(loopInterpolants[i], result);
			addTransition(i, honda, loopInterpolants, honda, loop, result);
		}
		addTransition(loopInterpolants.length, honda, loopInterpolants, honda, loop, result);
		return result;
	}

	private void addState(final IPredicate pred, final NestedWordAutomaton<CodeBlock, IPredicate> nwa) {
		if (!nwa.getStates().contains(pred)) {
			nwa.addState(false, false, pred);
		}
	}

	private void addTransition(final int pos, final IPredicate pre, final IPredicate[] predicates, final IPredicate post,
			final NestedWord<CodeBlock> nw, final NestedWordAutomaton<CodeBlock, IPredicate> nwa) {
		final IPredicate pred = getPredicateAtPosition(pos - 1, pre, predicates, post);
		final IPredicate succ = getPredicateAtPosition(pos, pre, predicates, post);
		final CodeBlock cb = nw.getSymbol(pos);
		if (nw.isInternalPosition(pos)) {
			nwa.addInternalTransition(pred, cb, succ);
		} else if (nw.isCallPosition(pos)) {
			nwa.addCallTransition(pred, cb, succ);
		} else if (nw.isReturnPosition(pos)) {
			assert !nw.isPendingReturn(pos);
			final int k = nw.getCallPosition(pos);
			final IPredicate hier = getPredicateAtPosition(k - 1, pre, predicates, post);
			nwa.addReturnTransition(pred, hier, cb, succ);
		}
	}

	private IPredicate getPredicateAtPosition(final int pos, final IPredicate before, final IPredicate[] predicates, final IPredicate after) {
		assert pos >= -1;
		assert pos <= predicates.length;
		if (pos < 0) {
			return before;
		} else if (pos >= predicates.length) {
			return after;
		} else {
			return predicates[pos];
		}
	}

}
