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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerUtils.HoareTripleChecks;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.BuchiAutomizerPreferenceInitializer.BuchiComplementationConstruction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.BuchiAutomizerPreferenceInitializer.NcsbImplementation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.NondeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.InductivityCheck;

public class RefineBuchi<LETTER extends IIcfgTransition<?>> {

	protected final ILogger mLogger;
	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;

	/**
	 * Intermediate layer to encapsulate communication with SMT solvers.
	 */
	private final CfgSmtToolkit mCsToolkit;
	private final PredicateFactory mPredicateFactory;

	private final boolean mDumpAutomata;
	private final boolean mDifference;
	private final PredicateFactoryForInterpolantAutomata mStateFactoryInterpolAutom;
	private final PredicateFactoryRefinement mStateFactoryForRefinement;
	private final boolean mUseDoubleDeckers;
	private final String mDumpPath;
	private final Format mFormat;
	private final NcsbImplementation mNcsbImplementation;
	private final String mIdentifier;

	/**
	 * Interpolant automaton of this iteration.
	 */
	protected INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> mInterpolAutomatonUsedInRefinement;

	private final IUltimateServiceProvider mServices;

	public RefineBuchi(final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory,
			final boolean dumpAutomata, final boolean difference,
			final PredicateFactoryForInterpolantAutomata stateFactoryInterpolAutom,
			final PredicateFactoryRefinement stateFactoryForRefinement, final boolean useDoubleDeckers,
			final String dumpPath, final Format format, final IUltimateServiceProvider services, final ILogger logger,
			final SimplificationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique,
			final NcsbImplementation ncsbImplementation, final String identifier) {
		mServices = services;
		mLogger = logger;
		mCsToolkit = csToolkit;
		mPredicateFactory = predicateFactory;
		mDumpAutomata = dumpAutomata;
		mDifference = difference;
		mStateFactoryInterpolAutom = stateFactoryInterpolAutom;
		mStateFactoryForRefinement = stateFactoryForRefinement;
		mUseDoubleDeckers = useDoubleDeckers;
		mDumpPath = dumpPath;
		mFormat = format;
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
		mNcsbImplementation = ncsbImplementation;
		mIdentifier = identifier;
	}

	public INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> getInterpolAutomatonUsedInRefinement() {
		return mInterpolAutomatonUsedInRefinement;
	}

	private int mIteration;

	public INestedWordAutomaton<LETTER, IPredicate> refineBuchi(
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> abstraction,
			final NestedLassoRun<LETTER, IPredicate> counterexample, final int iteration,
			final BuchiInterpolantAutomatonConstructionStyle setting, final BinaryStatePredicateManager bspm,
			final InterpolationTechnique interpolation, final BuchiCegarLoopBenchmarkGenerator benchmarkGenerator,
			final BuchiComplementationConstruction complementationConstruction, final IPredicate[] stemInterpolants,
			final IPredicate[] loopInterpolants, final PredicateUnifier pu) throws AutomataLibraryException {
		mIteration = iteration;
		final NestedWord<LETTER> stem = counterexample.getStem().getWord();
		final NestedWord<LETTER> loop = counterexample.getLoop().getWord();
		NestedWordAutomaton<LETTER, IPredicate> interpolAutomaton =
				BuchiAutomizerUtils.constructBuchiInterpolantAutomaton(bspm.getStemPrecondition(), stem,
						stemInterpolants, bspm.getHondaPredicate(), loop, loopInterpolants, abstraction.getVpAlphabet(),
						mServices, (IEmptyStackStateFactory<IPredicate>) abstraction.getStateFactory());
		if (mDumpAutomata) {

			final String filename = mIdentifier + "_" + "InterpolantAutomatonBuchi" + iteration;
			final String message = setting.toString();
			BuchiAutomizerUtils.writeAutomatonToFile(mServices, interpolAutomaton, mDumpPath, filename, mFormat,
					message);
		}
		final IHoareTripleChecker ehtc = HoareTripleCheckerUtils.constructEfficientHoareTripleCheckerWithCaching(
				mServices, HoareTripleChecks.INCREMENTAL, mCsToolkit, pu);
		final BuchiHoareTripleChecker bhtc = new BuchiHoareTripleChecker(ehtc);
		bhtc.putDecreaseEqualPair(bspm.getHondaPredicate(), bspm.getRankEqAndSi());
		assert new InductivityCheck<>(mServices, interpolAutomaton, false, true, bhtc).getResult();
		assert new BuchiAccepts<>(new AutomataLibraryServices(mServices), interpolAutomaton,
				counterexample.getNestedLassoWord()).getResult();

		mInterpolAutomatonUsedInRefinement =
				buildBuchiInterpolantAutomatonForOnDemandConstruction(counterexample, setting, bspm, interpolation,
						stem, loop, pu, stemInterpolants, loopInterpolants, interpolAutomaton, bhtc);
		final IStateDeterminizer<LETTER, IPredicate> stateDeterminizer = new PowersetDeterminizer<>(
				mInterpolAutomatonUsedInRefinement, mUseDoubleDeckers, mStateFactoryInterpolAutom);
		INestedWordAutomaton<LETTER, IPredicate> newAbstraction;
		if (mDifference) {
			if (complementationConstruction == BuchiComplementationConstruction.NCSB) {
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
				case ELASTIC:
					optimization = FkvOptimization.ELASTIC;
					break;
				case NCSB:
					throw new AssertionError("should be handled elsewhere");
				case HEIMAT2:
					optimization = FkvOptimization.HEIMAT2;
					break;
				case TIGHT_BASIC:
					optimization = FkvOptimization.TIGHT_LEVEL_RANKINGS;
					break;
				case TIGHT_HIGH_EVEN:
					optimization = FkvOptimization.HIGH_EVEN;
					break;
				case TIGHT_RO:
					optimization = FkvOptimization.SCHEWE;
					break;
				default:
					throw new AssertionError("unknown optimization");
				}
				newAbstraction = rankBasedOptimization(abstraction, setting, benchmarkGenerator, stateDeterminizer,
						optimization);
			}
		} else {
			final BuchiComplementFKV<LETTER, IPredicate> complNwa =
					new BuchiComplementFKV<>(new AutomataLibraryServices(mServices), mStateFactoryInterpolAutom,
							mInterpolAutomatonUsedInRefinement, stateDeterminizer);
			finishComputation(mInterpolAutomatonUsedInRefinement, setting);
			benchmarkGenerator.reportHighestRank(complNwa.getHighestRank());
			assert complNwa.checkResult(mStateFactoryInterpolAutom);
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> complement = complNwa.getResult();
			assert !new BuchiAccepts<>(new AutomataLibraryServices(mServices), complement,
					counterexample.getNestedLassoWord()).getResult();
			final BuchiIntersect<LETTER, IPredicate> interNwa = new BuchiIntersect<>(
					new AutomataLibraryServices(mServices), mStateFactoryForRefinement, abstraction, complement);
			assert interNwa.checkResult(mStateFactoryInterpolAutom);
			newAbstraction = interNwa.getResult();
		}
		benchmarkGenerator.addEdgeCheckerData(bhtc.getStatistics());
		interpolAutomaton = null;
		final boolean isUseful = isUsefulInterpolantAutomaton(mInterpolAutomatonUsedInRefinement, counterexample);
		if (!isUseful) {
			return null;
		}
		if (mDumpAutomata) {
			final String automatonString;
			if (mInterpolAutomatonUsedInRefinement.getVpAlphabet().getCallAlphabet().isEmpty()) {
				automatonString = "interpolBuchiAutomatonUsedInRefinement";
			} else {
				automatonString = "interpolBuchiNestedWordAutomatonUsedInRefinement";
			}
			final String filename = mIdentifier + "_" + automatonString + iteration + "after";
			final String message = setting.toString();
			BuchiAutomizerUtils.writeAutomatonToFile(mServices, mInterpolAutomatonUsedInRefinement, mDumpPath, filename,
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
			final String filename = mIdentifier + "_" + determinicity + automatonString + iteration + "after";
			final String message = setting.toString();
			BuchiAutomizerUtils.writeAutomatonToFile(mServices, mInterpolAutomatonUsedInRefinement, mDumpPath, filename,
					mFormat, message);

		}
		return newAbstraction;
	}

	private INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>
			buildBuchiInterpolantAutomatonForOnDemandConstruction(
					final NestedLassoRun<LETTER, IPredicate> counterexample,
					final BuchiInterpolantAutomatonConstructionStyle biaConstructionStyle,
					final BinaryStatePredicateManager bspm, final InterpolationTechnique interpolation,
					final NestedWord<LETTER> stem, final NestedWord<LETTER> loop, final PredicateUnifier pu,
					final IPredicate[] stemInterpolants, final IPredicate[] loopInterpolants,
					final NestedWordAutomaton<LETTER, IPredicate> interpolAutomaton,
					final BuchiHoareTripleChecker bhtc) {
		switch (biaConstructionStyle.getInterpolantAutomaton()) {
		case LASSO_AUTOMATON:
			return interpolAutomaton;
		case EAGER_NONDETERMINISM:
			if (!interpolAutomaton.getStates().contains(pu.getTruePredicate())) {
				interpolAutomaton.addState(false, false, pu.getTruePredicate());
			}
			if (!interpolAutomaton.getStates().contains(pu.getFalsePredicate())) {
				interpolAutomaton.addState(false, true, pu.getFalsePredicate());
			}
			return new NondeterministicInterpolantAutomaton<>(mServices, mCsToolkit, bhtc, interpolAutomaton, pu, false,
					true);
		case SCROOGE_NONDETERMINISM:
		case DETERMINISTIC:
			Set<IPredicate> stemInterpolantsForRefinement;
			final boolean emptyStem = BuchiAutomizerUtils.isEmptyStem(counterexample.getStem());
			if (emptyStem) {
				stemInterpolantsForRefinement = Collections.emptySet();
			} else if (biaConstructionStyle.cannibalizeLoop()) {
				stemInterpolantsForRefinement = pu.cannibalizeAll(false, Arrays.asList(stemInterpolants));
			} else {
				stemInterpolantsForRefinement = new HashSet<>(Arrays.asList(stemInterpolants));
			}
			Set<IPredicate> loopInterpolantsForRefinement;
			if (biaConstructionStyle.cannibalizeLoop()) {
				try {
					loopInterpolantsForRefinement = pu.cannibalizeAll(false, Arrays.asList(loopInterpolants));
					loopInterpolantsForRefinement.addAll(pu.cannibalize(false, bspm.getRankEqAndSi().getFormula()));

					final LoopCannibalizer<LETTER> lc =
							new LoopCannibalizer<>(counterexample, loopInterpolantsForRefinement, bspm, pu, mCsToolkit,
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

			return new BuchiInterpolantAutomatonBouncer<>(mCsToolkit, mPredicateFactory, bspm, bhtc, emptyStem,
					stemInterpolantsForRefinement, loopInterpolantsForRefinement,
					emptyStem ? null : stem.getSymbol(stem.length() - 1), loop.getSymbol(loop.length() - 1),
					biaConstructionStyle.isScroogeNondeterminismStem(),
					biaConstructionStyle.isScroogeNondeterminismLoop(), biaConstructionStyle.isBouncerStem(),
					biaConstructionStyle.isBouncerLoop(), mStateFactoryInterpolAutom, pu, pu, pu.getFalsePredicate(),
					mServices, interpolAutomaton);
		default:
			throw new UnsupportedOperationException("unknown automaton");
		}
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
			return diff.getResult();
		}
		return gbaDiff.getResult();
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
		}
		final boolean loopExtensionAccepted =
				new BuchiAccepts<>(new AutomataLibraryServices(mServices), oldApi, loopExtension).getResult();
		if (!loopExtensionAccepted) {
			throw new AssertionError("Bad chosen interpolant automaton: loop extension not accepted");
		}
		return true;
	}

	private void finishComputation(
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> interpolantAutomaton,
			final BuchiInterpolantAutomatonConstructionStyle setting) {
		switch (setting.getInterpolantAutomaton()) {
		case LASSO_AUTOMATON:
			// do nothing
			break;
		case EAGER_NONDETERMINISM:
			((NondeterministicInterpolantAutomaton<?>) interpolantAutomaton).switchToReadonlyMode();
			break;
		case SCROOGE_NONDETERMINISM:
		case DETERMINISTIC:
			((BuchiInterpolantAutomatonBouncer<?>) interpolantAutomaton).switchToReadonlyMode();
			break;
		default:
			throw new UnsupportedOperationException("unknown automaton");
		}
	}
}
