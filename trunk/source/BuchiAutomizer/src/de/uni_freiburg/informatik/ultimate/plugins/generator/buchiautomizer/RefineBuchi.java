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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IGeneralizedNwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.AbstractBuchiDifference;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.AbstractGeneralizedBuchiDifference;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiAccepts;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiComplementFKV;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiDifferenceFKV;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiDifferenceNCSB;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiDifferenceNCSBLazy;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiDifferenceNCSBLazy2;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiDifferenceNCSBLazy3;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiDifferenceNCSBSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiIntersect;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiToGeneralizedBuchi;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.GeneralizedBuchiDifferenceFKV;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.GeneralizedBuchiDifferenceNCSBAntichain;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.GeneralizedBuchiDifferenceNCSBSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.MultiOptimizationLevelRankingGenerator.FkvOptimization;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsDeterministic;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsSemiDeterministic;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.inclusion.BenchmarkRecord;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.UnsatCores;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.BuchiAutomizerPreferenceInitializer.BuchiComplementationConstruction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.BuchiAutomizerPreferenceInitializer.NcsbImplementation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.NondeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.InductivityCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.HoareTripleChecks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolatingTraceCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolatingTraceCheckCraig;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckSpWp;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckUtils;

public class RefineBuchi<LETTER extends IIcfgTransition<?>> {

	protected final ILogger mLogger;
	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;

	/**
	 * Intermediate layer to encapsulate communication with SMT solvers.
	 */
	private final CfgSmtToolkit mCsToolkit;
	private final PredicateFactory mPredicateFactory;

	private final IIcfg<?> mICfgContainer;

	private final boolean mDumpAutomata;
	private final boolean mDifference;
	private final PredicateFactoryForInterpolantAutomata mStateFactoryInterpolAutom;
	private final PredicateFactoryRefinement mStateFactoryForRefinement;
	private final boolean mUseDoubleDeckers;
	private final String mDumpPath;
	private final Format mFormat;
	private final InterpolationTechnique mInterpolation;
	private BackwardCoveringInformation mBci;
	private final NcsbImplementation mNcsbImplementation;
	/**
	 * Interpolant automaton of this iteration.
	 */
	protected INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> mInterpolAutomatonUsedInRefinement;

	private final IUltimateServiceProvider mServices;

	public RefineBuchi(final IIcfg<?> icfgContainer, final CfgSmtToolkit csToolkit,
			final PredicateFactory predicateFactory, final boolean dumpAutomata, final boolean difference,
			final PredicateFactoryForInterpolantAutomata stateFactoryInterpolAutom,
			final PredicateFactoryRefinement stateFactoryForRefinement, final boolean useDoubleDeckers,
			final String dumpPath, final Format format, final InterpolationTechnique interpolation,
			final IUltimateServiceProvider services, final ILogger logger,
			final SimplificationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique,
			final NcsbImplementation ncsbImplementation) {
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
		mNcsbImplementation = ncsbImplementation;
	}

	public INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> getInterpolAutomatonUsedInRefinement() {
		return mInterpolAutomatonUsedInRefinement;
	}

	public BackwardCoveringInformation getBci() {
		return mBci;
	}

	private int mIteration;

	INestedWordAutomaton<LETTER, IPredicate> refineBuchi(
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> abstraction,
			final NestedLassoRun<LETTER, IPredicate> mCounterexample, final int iteration,
			final BuchiInterpolantAutomatonConstructionStyle setting, final BinaryStatePredicateManager bspm,
			final ModifiableGlobalsTable modifiableGlobalsTable, final InterpolationTechnique interpolation,
			final BuchiCegarLoopBenchmarkGenerator benchmarkGenerator,
			final BuchiComplementationConstruction complementationConstruction) throws AutomataLibraryException {
		mIteration = iteration;
		final NestedWord<LETTER> stem = mCounterexample.getStem().getWord();
		// if (emptyStem(mCounterexample)) {
		// stem = mCounterexample.getLoop().getWord();
		// } else {
		// stem = mCounterexample.getStem().getWord();
		// }
		final NestedWord<LETTER> loop = mCounterexample.getLoop().getWord();

		assert !bspm.getStemPrecondition().getFormula().toString().equals("false");
		assert !bspm.getHondaPredicate().getFormula().toString().equals("false");
		assert !bspm.getRankEqAndSi().getFormula().toString().equals("false");
		final PredicateUnifier pu = new PredicateUnifier(mLogger, mServices, mCsToolkit.getManagedScript(),
				mPredicateFactory, mCsToolkit.getSymbolTable(), mSimplificationTechnique,
				mXnfConversionTechnique, bspm.getStemPrecondition(), bspm.getHondaPredicate(),
				bspm.getRankEqAndSi(), bspm.getStemPostcondition(), bspm.getRankDecreaseAndBound(), bspm.getSiConjunction());
		IPredicate[] stemInterpolants;
		InterpolatingTraceCheck<LETTER> traceCheck;
		if (BuchiCegarLoop.isEmptyStem(mCounterexample)) {
			stemInterpolants = null;
		} else {

			traceCheck = constructTraceCheck(bspm.getStemPrecondition(), bspm.getStemPostcondition(), stem, mCsToolkit,
					pu, mInterpolation);
			final LBool stemCheck = traceCheck.isCorrect();
			if (stemCheck == LBool.UNSAT) {
				stemInterpolants = traceCheck.getInterpolants();
			} else {
				throw new AssertionError("incorrect predicates - stem");
			}
		}

		traceCheck = constructTraceCheck(bspm.getRankEqAndSi(), bspm.getHondaPredicate(), loop, mCsToolkit, pu,
				mInterpolation);
		final LBool loopCheck = traceCheck.isCorrect();
		IPredicate[] loopInterpolants;
		if (loopCheck == LBool.UNSAT) {
			loopInterpolants = traceCheck.getInterpolants();
		} else {
			throw new AssertionError("incorrect predicates - loop");
		}
		mBci = TraceCheckUtils.computeCoverageCapability(mServices, traceCheck, mLogger);

		NestedWordAutomaton<LETTER, IPredicate> mInterpolAutomaton =
				constructBuchiInterpolantAutomaton(bspm.getStemPrecondition(), stem, stemInterpolants,
						bspm.getHondaPredicate(), loop, loopInterpolants, abstraction);
		if (mDumpAutomata) {

			final String filename = mICfgContainer.getIdentifier() + "_" + "InterpolantAutomatonBuchi" + iteration;
			final String message = setting.toString();
			BuchiCegarLoop.writeAutomatonToFile(mServices, mInterpolAutomaton, mDumpPath, filename, mFormat, message);
		}

		// BuchiHoareTripleChecker bhtc = new BuchiHoareTripleChecker(new MonolithicHoareTripleChecker(mCsToolkit));
		final IHoareTripleChecker ehtc = TraceAbstractionUtils.constructEfficientHoareTripleCheckerWithCaching(
				mServices, HoareTripleChecks.INCREMENTAL, mCsToolkit, pu);
		final BuchiHoareTripleChecker bhtc = new BuchiHoareTripleChecker(ehtc);
		bhtc.putDecreaseEqualPair(bspm.getHondaPredicate(), bspm.getRankEqAndSi());
		assert new InductivityCheck<>(mServices, mInterpolAutomaton, false, true, bhtc).getResult();
		assert new BuchiAccepts<>(new AutomataLibraryServices(mServices), mInterpolAutomaton,
				mCounterexample.getNestedLassoWord()).getResult();

		mInterpolAutomatonUsedInRefinement =
				buildBuchiInterpolantAutomatonForOnDemandConstruction(mCounterexample, setting, bspm, interpolation,
						stem, loop, pu, stemInterpolants, loopInterpolants, mInterpolAutomaton, bhtc);
		final IStateDeterminizer<LETTER, IPredicate> stateDeterminizer = new PowersetDeterminizer<>(
				mInterpolAutomatonUsedInRefinement, mUseDoubleDeckers, mStateFactoryInterpolAutom);
		INestedWordAutomaton<LETTER, IPredicate> newAbstraction;
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
			// BuchiComplementFKVNwa<LETTER, IPredicate> compl1 =
			// diff.getSndComplemented();
			// INestedWordAutomatonOldApi<LETTER, IPredicate> compl = (new
			// RemoveNonLiveStates<LETTER, IPredicate>(compl1)).getResult();
			// BuchiClosureNwa<LETTER, IPredicate> bc = (new
			// BuchiClosureNwa<LETTER, IPredicate>(compl));
			// MinimizeSevpa<LETTER, IPredicate> minimizeOp =
			// new MinimizeSevpa<LETTER,
			// IPredicate>(bc,null,false,false,mStateFactoryInterpolAutom);
			// s_Logger.warn("END: minimization test");
			// INestedWordAutomatonOldApi<LETTER, IPredicate> minimizedOp =
			// minimizeOp.getResult();
			//
			// BuchiIntersect<LETTER, IPredicate> newDiff =
			// new BuchiIntersect<LETTER, IPredicate>(
			// mAbstraction, minimizedOp, mStateFactoryForRefinement);
			// s_Logger.warn("oldDiff size" +
			// diff.getResult().sizeInformation());
			// s_Logger.warn("newDiff size" +
			// (newDiff.getResult()).sizeInformation());

		} else {
			final BuchiComplementFKV<LETTER, IPredicate> complNwa =
					new BuchiComplementFKV<>(new AutomataLibraryServices(mServices), mStateFactoryInterpolAutom,
							mInterpolAutomatonUsedInRefinement, stateDeterminizer);
			finishComputation(mInterpolAutomatonUsedInRefinement, setting);
			benchmarkGenerator.reportHighestRank(complNwa.getHighestRank());
			assert complNwa.checkResult(mStateFactoryInterpolAutom);
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> complement = complNwa.getResult();
			assert !new BuchiAccepts<>(new AutomataLibraryServices(mServices), complement,
					mCounterexample.getNestedLassoWord()).getResult();
			final BuchiIntersect<LETTER, IPredicate> interNwa = new BuchiIntersect<>(
					new AutomataLibraryServices(mServices), mStateFactoryForRefinement, abstraction, complement);
			assert interNwa.checkResult(mStateFactoryInterpolAutom);
			newAbstraction = interNwa.getResult();
		}
		// INestedWordAutomatonOldApi<LETTER, IPredicate> oldApi = (new
		// RemoveUnreachable<LETTER,
		// IPredicate>(mInterpolAutomatonUsedInRefinement)).getResult();
		benchmarkGenerator.addEdgeCheckerData(bhtc.getEdgeCheckerBenchmark());
		mInterpolAutomaton = null;
		final boolean isUseful = isUsefulInterpolantAutomaton(mInterpolAutomatonUsedInRefinement, mCounterexample);
		if (!isUseful) {
			return null;
		}

		// assert (new BuchiAccepts<LETTER,
		// IPredicate>(oldApi,mCounterexample.getNestedLassoWord())).getResult()
		// : "interpolant automaton does not accept lasso.";
		// assert !(new BuchiAccepts<LETTER,
		// IPredicate>(newAbstraction,mCounterexample.getNestedLassoWord())).getResult()
		// : "no progress";
		if (mDumpAutomata) {
			final String automatonString;
			if (mInterpolAutomatonUsedInRefinement.getVpAlphabet().getCallAlphabet().isEmpty()) {
				automatonString = "interpolBuchiAutomatonUsedInRefinement";
			} else {
				automatonString = "interpolBuchiNestedWordAutomatonUsedInRefinement";
			}
			final String filename = mICfgContainer.getIdentifier() + "_" + automatonString + iteration + "after";
			final String message = setting.toString();
			BuchiCegarLoop.writeAutomatonToFile(mServices, mInterpolAutomatonUsedInRefinement, mDumpPath, filename,
					mFormat, message);
		}
		final boolean tacasDump = false;
		if (tacasDump) {
			final String determinicity;
			final boolean isSemiDeterministic = new IsSemiDeterministic<>(new AutomataLibraryServices(mServices),
					mInterpolAutomatonUsedInRefinement).getResult();
			final boolean isDeterministic =
					new IsDeterministic<>(new AutomataLibraryServices(mServices), mInterpolAutomatonUsedInRefinement)
							.getResult();
			if (isDeterministic) {
				determinicity = "deterministic";
				assert isSemiDeterministic : "but semi deterministic";
			} else if (isSemiDeterministic) {
				determinicity = "semideterministic";
			} else {
				determinicity = "nondeterministic";
			}
			final String automatonString;
			if (mInterpolAutomatonUsedInRefinement.getVpAlphabet().getCallAlphabet().isEmpty()) {
				automatonString = "interpolBuchiAutomatonUsedInRefinement";
			} else {
				automatonString = "interpolBuchiNestedWordAutomatonUsedInRefinement";
			}
			final String filename =
					mICfgContainer.getIdentifier() + "_" + determinicity + automatonString + iteration + "after";
			final String message = setting.toString();
			BuchiCegarLoop.writeAutomatonToFile(mServices, mInterpolAutomatonUsedInRefinement, mDumpPath, filename,
					mFormat, message);

		}
		return newAbstraction;
	}

	private INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>
			buildBuchiInterpolantAutomatonForOnDemandConstruction(
					final NestedLassoRun<LETTER, IPredicate> mCounterexample,
					final BuchiInterpolantAutomatonConstructionStyle biaConstructionStyle,
					final BinaryStatePredicateManager bspm, final InterpolationTechnique interpolation,
					final NestedWord<LETTER> stem, final NestedWord<LETTER> loop, final PredicateUnifier pu,
					final IPredicate[] stemInterpolants, final IPredicate[] loopInterpolants,
					final NestedWordAutomaton<LETTER, IPredicate> mInterpolAutomaton,
					final BuchiHoareTripleChecker bhtc) {
		INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> buchiInterpolantAutomatonForOnDemandConstruction;
		switch (biaConstructionStyle.getInterpolantAutomaton()) {
		case LassoAutomaton:
			buchiInterpolantAutomatonForOnDemandConstruction = mInterpolAutomaton;
			break;
		case EagerNondeterminism:
			if (!mInterpolAutomaton.getStates().contains(pu.getTruePredicate())) {
				mInterpolAutomaton.addState(false, false, pu.getTruePredicate());
			}
			if (!mInterpolAutomaton.getStates().contains(pu.getFalsePredicate())) {
				mInterpolAutomaton.addState(false, true, pu.getFalsePredicate());
			}
			buchiInterpolantAutomatonForOnDemandConstruction = new NondeterministicInterpolantAutomaton<>(mServices,
					mCsToolkit, bhtc, mInterpolAutomaton, pu, false, true);
			break;
		case ScroogeNondeterminism:
		case Deterministic:
			Set<IPredicate> stemInterpolantsForRefinement;
			if (BuchiCegarLoop.isEmptyStem(mCounterexample)) {
				stemInterpolantsForRefinement = Collections.emptySet();
			} else {
				if (biaConstructionStyle.cannibalizeLoop()) {
					stemInterpolantsForRefinement = pu.cannibalizeAll(false, Arrays.asList(stemInterpolants));
				} else {
					stemInterpolantsForRefinement = new HashSet<>(Arrays.asList(stemInterpolants));
				}
			}
			Set<IPredicate> loopInterpolantsForRefinement;
			if (biaConstructionStyle.cannibalizeLoop()) {
				try {
					loopInterpolantsForRefinement = pu.cannibalizeAll(false, Arrays.asList(loopInterpolants));
					loopInterpolantsForRefinement.addAll(pu.cannibalize(false, bspm.getRankEqAndSi().getFormula()));

					final LoopCannibalizer<LETTER> lc =
							new LoopCannibalizer<>(mCounterexample, loopInterpolantsForRefinement, bspm, pu, mCsToolkit,
									interpolation, mServices, mSimplificationTechnique, mXnfConversionTechnique);
					loopInterpolantsForRefinement = lc.getResult();
				} catch (final ToolchainCanceledException tce) {
					final String taskDescription = "loop cannibalization";
					tce.addRunningTaskInfo(new RunningTaskInfo(getClass(), taskDescription));
					throw tce;
				}
			} else {
				loopInterpolantsForRefinement = new HashSet<>(Arrays.asList(loopInterpolants));
				loopInterpolantsForRefinement.add(bspm.getRankEqAndSi());
			}

			buchiInterpolantAutomatonForOnDemandConstruction = new BuchiInterpolantAutomatonBouncer<>(mCsToolkit,
					mPredicateFactory, bspm, bhtc, BuchiCegarLoop.isEmptyStem(mCounterexample),
					stemInterpolantsForRefinement, loopInterpolantsForRefinement,
					BuchiCegarLoop.isEmptyStem(mCounterexample) ? null : stem.getSymbol(stem.length() - 1),
					loop.getSymbol(loop.length() - 1), biaConstructionStyle.isScroogeNondeterminismStem(),
					biaConstructionStyle.isScroogeNondeterminismLoop(), biaConstructionStyle.isBouncerStem(),
					biaConstructionStyle.isBouncerLoop(), mStateFactoryInterpolAutom, pu, pu, pu.getFalsePredicate(),
					mServices, mInterpolAutomaton);
			break;
		default:
			throw new UnsupportedOperationException("unknown automaton");
		}
		return buchiInterpolantAutomatonForOnDemandConstruction;
	}

	private INestedWordAutomaton<LETTER, IPredicate> nsbcDifference(
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> abstraction,
			final BuchiInterpolantAutomatonConstructionStyle setting,
			final BuchiCegarLoopBenchmarkGenerator benchmarkGenerator) throws AutomataLibraryException {
		INestedWordAutomaton<LETTER, IPredicate> newAbstraction;
		AbstractBuchiDifference<LETTER, IPredicate> diff = null;
		AbstractGeneralizedBuchiDifference<LETTER, IPredicate> gbaDiff = null;
		final IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> gbaAbstraction;
		switch (mNcsbImplementation) {
		case INTSET:
			diff = new BuchiDifferenceNCSBSimple<>(new AutomataLibraryServices(mServices), mStateFactoryForRefinement,
					abstraction, mInterpolAutomatonUsedInRefinement);
			break;
		case INTSET_LAZY:
			diff = new BuchiDifferenceNCSBLazy<>(new AutomataLibraryServices(mServices), mStateFactoryForRefinement,
					abstraction, mInterpolAutomatonUsedInRefinement);
			break;
		case INTSET_GBA:
			if (abstraction.getVpAlphabet().getCallAlphabet().isEmpty()
					&& abstraction.getVpAlphabet().getReturnAlphabet().isEmpty()) {
				if (abstraction instanceof IGeneralizedNwaOutgoingLetterAndTransitionProvider) {
					gbaAbstraction =
							(IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>) abstraction;
				} else {
					gbaAbstraction = new BuchiToGeneralizedBuchi<>(abstraction);
				}
				gbaDiff = new GeneralizedBuchiDifferenceNCSBSimple<>(new AutomataLibraryServices(mServices),
						mStateFactoryForRefinement, gbaAbstraction, mInterpolAutomatonUsedInRefinement, false);
			} else {
				diff = new BuchiDifferenceNCSBLazy3<>(new AutomataLibraryServices(mServices),
						mStateFactoryForRefinement, abstraction, mInterpolAutomatonUsedInRefinement);
			}
			break;
		case INTSET_GBA_LAZY:
			if (abstraction.getVpAlphabet().getCallAlphabet().isEmpty()
					&& abstraction.getVpAlphabet().getReturnAlphabet().isEmpty()) {
				if (abstraction instanceof IGeneralizedNwaOutgoingLetterAndTransitionProvider) {
					gbaAbstraction =
							(IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>) abstraction;
				} else {
					gbaAbstraction = new BuchiToGeneralizedBuchi<>(abstraction);
				}
				gbaDiff = new GeneralizedBuchiDifferenceNCSBSimple<>(new AutomataLibraryServices(mServices),
						mStateFactoryForRefinement, gbaAbstraction, mInterpolAutomatonUsedInRefinement, true);
			} else {
				diff = new BuchiDifferenceNCSBLazy3<>(new AutomataLibraryServices(mServices),
						mStateFactoryForRefinement, abstraction, mInterpolAutomatonUsedInRefinement);
			}

			break;
		case INTSET_GBA_ANTICHAIN:
			if (abstraction.getVpAlphabet().getCallAlphabet().isEmpty()
					&& abstraction.getVpAlphabet().getReturnAlphabet().isEmpty()) {
				if (abstraction instanceof IGeneralizedNwaOutgoingLetterAndTransitionProvider) {
					gbaAbstraction =
							(IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>) abstraction;
				} else {
					gbaAbstraction = new BuchiToGeneralizedBuchi<>(abstraction);
				}
				gbaDiff = new GeneralizedBuchiDifferenceNCSBAntichain<>(new AutomataLibraryServices(mServices),
						mStateFactoryForRefinement, gbaAbstraction, mInterpolAutomatonUsedInRefinement, false);
			} else {
				diff = new BuchiDifferenceNCSBLazy3<>(new AutomataLibraryServices(mServices),
						mStateFactoryForRefinement, abstraction, mInterpolAutomatonUsedInRefinement);
			}
			break;
		case INTSET_GBA_LAZY_ANTICHAIN:
			if (abstraction.getVpAlphabet().getCallAlphabet().isEmpty()
					&& abstraction.getVpAlphabet().getReturnAlphabet().isEmpty()) {
				if (abstraction instanceof IGeneralizedNwaOutgoingLetterAndTransitionProvider) {
					gbaAbstraction =
							(IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>) abstraction;
				} else {
					gbaAbstraction = new BuchiToGeneralizedBuchi<>(abstraction);
				}
				gbaDiff = new GeneralizedBuchiDifferenceNCSBAntichain<>(new AutomataLibraryServices(mServices),
						mStateFactoryForRefinement, gbaAbstraction, mInterpolAutomatonUsedInRefinement, true);
			} else {
				diff = new BuchiDifferenceNCSBLazy3<>(new AutomataLibraryServices(mServices),
						mStateFactoryForRefinement, abstraction, mInterpolAutomatonUsedInRefinement);
			}
			break;
		case INTSET_LAZY2:
			diff = new BuchiDifferenceNCSBLazy2<>(new AutomataLibraryServices(mServices), mStateFactoryForRefinement,
					abstraction, mInterpolAutomatonUsedInRefinement);
			break;
		case INTSET_LAZY3:
			diff = new BuchiDifferenceNCSBLazy3<>(new AutomataLibraryServices(mServices), mStateFactoryForRefinement,
					abstraction, mInterpolAutomatonUsedInRefinement);
			break;
		case ORIGINAL:
			diff = new BuchiDifferenceNCSB<>(new AutomataLibraryServices(mServices), mStateFactoryForRefinement,
					abstraction, mInterpolAutomatonUsedInRefinement);
			break;
		default:
			throw new AssertionError("illegal value");
		}
		finishComputation(mInterpolAutomatonUsedInRefinement, setting);
		benchmarkGenerator.reportHighestRank(3);
		if (gbaDiff == null) {
			assert diff.checkResult(mStateFactoryInterpolAutom);
			newAbstraction = diff.getResult();
			if (BenchmarkRecord.canDump()) {
				BenchmarkRecord.addComplementAutomaton(mIteration, diff.getSndComplemented().size(), 0);
			}
		} else {
			newAbstraction = gbaDiff.getResult();
			if (BenchmarkRecord.canDump()) {
				BenchmarkRecord.addComplementAutomaton(mIteration, gbaDiff.getSndComplemented().size(), 0);
			}
		}

		return newAbstraction;
	}

	private INestedWordAutomaton<LETTER, IPredicate> rankBasedOptimization(
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> abstraction,
			final BuchiInterpolantAutomatonConstructionStyle setting,
			final BuchiCegarLoopBenchmarkGenerator benchmarkGenerator,
			final IStateDeterminizer<LETTER, IPredicate> stateDeterminizer, final FkvOptimization optimization)
			throws AutomataLibraryException {
		INestedWordAutomaton<LETTER, IPredicate> newAbstraction;
		GeneralizedBuchiDifferenceFKV<LETTER, IPredicate> gbaDiff = null;
		BuchiDifferenceFKV<LETTER, IPredicate> diff = null;
		if (abstraction instanceof IGeneralizedNwaOutgoingLetterAndTransitionProvider) {
			final IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> gbaAbstraction =
					(IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>) abstraction;
			gbaDiff = new GeneralizedBuchiDifferenceFKV<>(new AutomataLibraryServices(mServices),
					mStateFactoryForRefinement, gbaAbstraction, mInterpolAutomatonUsedInRefinement, stateDeterminizer,
					optimization, Integer.MAX_VALUE);
		} else {
			diff = new BuchiDifferenceFKV<>(new AutomataLibraryServices(mServices), mStateFactoryForRefinement,
					abstraction, mInterpolAutomatonUsedInRefinement, stateDeterminizer, optimization,
					Integer.MAX_VALUE);
		}
		finishComputation(mInterpolAutomatonUsedInRefinement, setting);
		if (gbaDiff == null) {
			benchmarkGenerator.reportHighestRank(diff.getHighestRank());
			assert diff.checkResult(mStateFactoryInterpolAutom);
			newAbstraction = diff.getResult();
		} else {
			newAbstraction = gbaDiff.getResult();
		}

		return newAbstraction;
	}

	private InterpolatingTraceCheck<LETTER> constructTraceCheck(final IPredicate precond, final IPredicate postcond,
			final NestedWord<LETTER> word, final CfgSmtToolkit csToolkit, final PredicateUnifier pu,
			final InterpolationTechnique interpolation) {
		final InterpolatingTraceCheck<LETTER> itc;
		switch (mInterpolation) {
		case Craig_NestedInterpolation:
		case Craig_TreeInterpolation: {
			itc = new InterpolatingTraceCheckCraig<>(precond, postcond, new TreeMap<Integer, IPredicate>(), word, null,
					mServices, mCsToolkit, mPredicateFactory, pu, AssertCodeBlockOrder.NOT_INCREMENTALLY, false, false,
					interpolation, true, mXnfConversionTechnique, mSimplificationTechnique);
			break;
		}
		case ForwardPredicates:
		case BackwardPredicates:
		case FPandBP:
		case FPandBPonlyIfFpWasNotPerfect: {
			itc = new TraceCheckSpWp<>(precond, postcond, new TreeMap<Integer, IPredicate>(), word, mCsToolkit,
					AssertCodeBlockOrder.NOT_INCREMENTALLY, UnsatCores.CONJUNCT_LEVEL, true, mServices, false,
					mPredicateFactory, pu, interpolation, mCsToolkit.getManagedScript(), mXnfConversionTechnique,
					mSimplificationTechnique, null, false);
			break;
		}
		default:
			throw new UnsupportedOperationException("unsupported interpolation");
		}
		if (itc.getToolchainCanceledExpection() != null) {
			throw itc.getToolchainCanceledExpection();
		}
		return itc;
	}

	private boolean isUsefulInterpolantAutomaton(
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> interpolAutomatonUsedInRefinement,
			final NestedLassoRun<LETTER, IPredicate> counterexample) throws AutomataLibraryException {
		INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> oldApi;
		oldApi = new RemoveUnreachable<>(new AutomataLibraryServices(mServices), interpolAutomatonUsedInRefinement)
				.getResult();
		final NestedWord<LETTER> stem = counterexample.getStem().getWord();
		final NestedWord<LETTER> loop = counterexample.getLoop().getWord();
		final NestedWord<LETTER> stemAndLoop = stem.concatenate(loop);
		final NestedLassoWord<LETTER> stemExtension = new NestedLassoWord<>(stemAndLoop, loop);
		final NestedWord<LETTER> loopAndLoop = loop.concatenate(loop);
		final NestedLassoWord<LETTER> loopExtension = new NestedLassoWord<>(stem, loopAndLoop);
		final boolean wordAccepted =
				new BuchiAccepts<>(new AutomataLibraryServices(mServices), oldApi, counterexample.getNestedLassoWord())
						.getResult();
		if (!wordAccepted) {
			mLogger.info("Bad chosen interpolant automaton: word not accepted");
			return false;
		}
		// 2015-01-14 Matthias: word, stemExtension, and loopExtension are only
		// different representations of the same word. The following lines
		// do not make any sense (but might be helpful to reveal a bug.
		final boolean stemExtensionAccepted =
				new BuchiAccepts<>(new AutomataLibraryServices(mServices), oldApi, stemExtension).getResult();
		if (!stemExtensionAccepted) {
			throw new AssertionError("Bad chosen interpolant automaton: stem extension not accepted");
			// mLogger.info("Bad chosen interpolant automaton: stem extension not accepted");
			// return false;
		}
		final boolean loopExtensionAccepted =
				new BuchiAccepts<>(new AutomataLibraryServices(mServices), oldApi, loopExtension).getResult();
		if (!loopExtensionAccepted) {
			throw new AssertionError("Bad chosen interpolant automaton: loop extension not accepted");
			// mLogger.info("Bad chosen interpolant automaton: loop extension not accepted");
			// return false;
		}
		return true;
	}

	private void finishComputation(
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> interpolantAutomaton,
			final BuchiInterpolantAutomatonConstructionStyle setting) {
		switch (setting.getInterpolantAutomaton()) {
		case LassoAutomaton:
			// do nothing
			break;
		case EagerNondeterminism:
			((NondeterministicInterpolantAutomaton<?>) interpolantAutomaton).switchToReadonlyMode();
			break;
		case ScroogeNondeterminism:
		case Deterministic:
			((BuchiInterpolantAutomatonBouncer<?>) interpolantAutomaton).switchToReadonlyMode();
			break;
		default:
			throw new UnsupportedOperationException("unknown automaton");
		}
	}

	private NestedWordAutomaton<LETTER, IPredicate> constructBuchiInterpolantAutomaton(final IPredicate precondition,
			final NestedWord<LETTER> stem, final IPredicate[] stemInterpolants, final IPredicate honda,
			final NestedWord<LETTER> loop, final IPredicate[] loopInterpolants,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> abstraction) {
		final NestedWordAutomaton<LETTER, IPredicate> result = new NestedWordAutomaton<>(
				new AutomataLibraryServices(mServices), abstraction.getVpAlphabet(), (IEmptyStackStateFactory<IPredicate>) abstraction.getStateFactory());
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

	private void addState(final IPredicate pred, final NestedWordAutomaton<LETTER, IPredicate> nwa) {
		if (!nwa.getStates().contains(pred)) {
			nwa.addState(false, false, pred);
		}
	}

	private void addTransition(final int pos, final IPredicate pre, final IPredicate[] predicates,
			final IPredicate post, final NestedWord<LETTER> nw, final NestedWordAutomaton<LETTER, IPredicate> nwa) {
		final IPredicate pred = getPredicateAtPosition(pos - 1, pre, predicates, post);
		final IPredicate succ = getPredicateAtPosition(pos, pre, predicates, post);
		final LETTER cb = nw.getSymbol(pos);
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

	private static IPredicate getPredicateAtPosition(final int pos, final IPredicate before,
			final IPredicate[] predicates, final IPredicate after) {
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
