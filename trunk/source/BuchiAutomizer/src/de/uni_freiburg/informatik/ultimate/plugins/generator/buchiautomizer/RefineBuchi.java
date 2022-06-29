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

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IGeneralizedNwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.inclusion.BenchmarkRecord;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.BuchiAutomizerPreferenceInitializer.BuchiComplementationConstruction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.BuchiAutomizerPreferenceInitializer.NcsbImplementation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;

public class RefineBuchi<LETTER extends IIcfgTransition<?>> {

	protected final ILogger mLogger;
	private final boolean mDifference;
	private final PredicateFactoryForInterpolantAutomata mStateFactoryInterpolAutom;
	private final PredicateFactoryRefinement mStateFactoryForRefinement;
	private final boolean mUseDoubleDeckers;
	private final NcsbImplementation mNcsbImplementation;

	private final IUltimateServiceProvider mServices;
	private int mIteration;

	public RefineBuchi(final boolean difference, final PredicateFactoryForInterpolantAutomata stateFactoryInterpolAutom,
			final PredicateFactoryRefinement stateFactoryForRefinement, final boolean useDoubleDeckers,
			final IUltimateServiceProvider services, final ILogger logger,
			final NcsbImplementation ncsbImplementation) {
		mServices = services;
		mLogger = logger;
		mDifference = difference;
		mStateFactoryInterpolAutom = stateFactoryInterpolAutom;
		mStateFactoryForRefinement = stateFactoryForRefinement;
		mUseDoubleDeckers = useDoubleDeckers;
		mNcsbImplementation = ncsbImplementation;
	}

	public INestedWordAutomaton<LETTER, IPredicate> refineBuchi(
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> abstraction,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> interpolantAutomaton,
			final NestedLassoRun<LETTER, IPredicate> counterexample, final int iteration,
			final boolean semiDeterministic, final BuchiCegarLoopBenchmarkGenerator benchmarkGenerator,
			final BuchiComplementationConstruction complementationConstruction) throws AutomataLibraryException {
		mIteration = iteration;
		final IStateDeterminizer<LETTER, IPredicate> stateDeterminizer =
				new PowersetDeterminizer<>(interpolantAutomaton, mUseDoubleDeckers, mStateFactoryInterpolAutom);
		if (mDifference) {
			if (complementationConstruction == BuchiComplementationConstruction.NCSB) {
				if (semiDeterministic) {
					return nsbcDifference(abstraction, interpolantAutomaton, benchmarkGenerator);
				}
				final FkvOptimization optimization = FkvOptimization.ELASTIC;
				return rankBasedOptimization(abstraction, interpolantAutomaton, benchmarkGenerator, stateDeterminizer,
						optimization);
			}
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
			return rankBasedOptimization(abstraction, interpolantAutomaton, benchmarkGenerator, stateDeterminizer,
					optimization);
		}

		final BuchiComplementFKV<LETTER, IPredicate> complNwa =
				new BuchiComplementFKV<>(new AutomataLibraryServices(mServices), mStateFactoryInterpolAutom,
						interpolantAutomaton, stateDeterminizer);
		benchmarkGenerator.reportHighestRank(complNwa.getHighestRank());
		assert complNwa.checkResult(mStateFactoryInterpolAutom);
		final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> complement = complNwa.getResult();
		assert !new BuchiAccepts<>(new AutomataLibraryServices(mServices), complement,
				counterexample.getNestedLassoWord()).getResult();
		final BuchiIntersect<LETTER, IPredicate> interNwa = new BuchiIntersect<>(new AutomataLibraryServices(mServices),
				mStateFactoryForRefinement, abstraction, complement);
		assert interNwa.checkResult(mStateFactoryInterpolAutom);
		return interNwa.getResult();
	}

	private INestedWordAutomaton<LETTER, IPredicate> nsbcDifference(
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> abstraction,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> interpolantAutomaton,
			final BuchiCegarLoopBenchmarkGenerator benchmarkGenerator) throws AutomataLibraryException {
		INestedWordAutomaton<LETTER, IPredicate> newAbstraction;
		AbstractBuchiDifference<LETTER, IPredicate> diff = null;
		AbstractGeneralizedBuchiDifference<LETTER, IPredicate> gbaDiff = null;
		final IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> gbaAbstraction;
		switch (mNcsbImplementation) {
		case INTSET:
			diff = new BuchiDifferenceNCSBSimple<>(new AutomataLibraryServices(mServices), mStateFactoryForRefinement,
					abstraction, interpolantAutomaton);
			break;
		case INTSET_LAZY:
			diff = new BuchiDifferenceNCSBLazy<>(new AutomataLibraryServices(mServices), mStateFactoryForRefinement,
					abstraction, interpolantAutomaton);
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
						mStateFactoryForRefinement, gbaAbstraction, interpolantAutomaton, false);
			} else {
				diff = new BuchiDifferenceNCSBLazy3<>(new AutomataLibraryServices(mServices),
						mStateFactoryForRefinement, abstraction, interpolantAutomaton);
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
						mStateFactoryForRefinement, gbaAbstraction, interpolantAutomaton, true);
			} else {
				diff = new BuchiDifferenceNCSBLazy3<>(new AutomataLibraryServices(mServices),
						mStateFactoryForRefinement, abstraction, interpolantAutomaton);
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
						mStateFactoryForRefinement, gbaAbstraction, interpolantAutomaton, false);
			} else {
				diff = new BuchiDifferenceNCSBLazy3<>(new AutomataLibraryServices(mServices),
						mStateFactoryForRefinement, abstraction, interpolantAutomaton);
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
						mStateFactoryForRefinement, gbaAbstraction, interpolantAutomaton, true);
			} else {
				diff = new BuchiDifferenceNCSBLazy3<>(new AutomataLibraryServices(mServices),
						mStateFactoryForRefinement, abstraction, interpolantAutomaton);
			}
			break;
		case INTSET_LAZY2:
			diff = new BuchiDifferenceNCSBLazy2<>(new AutomataLibraryServices(mServices), mStateFactoryForRefinement,
					abstraction, interpolantAutomaton);
			break;
		case INTSET_LAZY3:
			diff = new BuchiDifferenceNCSBLazy3<>(new AutomataLibraryServices(mServices), mStateFactoryForRefinement,
					abstraction, interpolantAutomaton);
			break;
		case ORIGINAL:
			diff = new BuchiDifferenceNCSB<>(new AutomataLibraryServices(mServices), mStateFactoryForRefinement,
					abstraction, interpolantAutomaton);
			break;
		default:
			throw new AssertionError("illegal value");
		}
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
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> interpolantAutomaton,
			final BuchiCegarLoopBenchmarkGenerator benchmarkGenerator,
			final IStateDeterminizer<LETTER, IPredicate> stateDeterminizer, final FkvOptimization optimization)
			throws AutomataLibraryException {
		GeneralizedBuchiDifferenceFKV<LETTER, IPredicate> gbaDiff = null;
		BuchiDifferenceFKV<LETTER, IPredicate> diff = null;
		if (abstraction instanceof IGeneralizedNwaOutgoingLetterAndTransitionProvider) {
			final IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> gbaAbstraction =
					(IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>) abstraction;
			gbaDiff = new GeneralizedBuchiDifferenceFKV<>(new AutomataLibraryServices(mServices),
					mStateFactoryForRefinement, gbaAbstraction, interpolantAutomaton, stateDeterminizer, optimization,
					Integer.MAX_VALUE);
		} else {
			diff = new BuchiDifferenceFKV<>(new AutomataLibraryServices(mServices), mStateFactoryForRefinement,
					abstraction, interpolantAutomaton, stateDeterminizer, optimization, Integer.MAX_VALUE);
		}
		if (gbaDiff == null) {
			benchmarkGenerator.reportHighestRank(diff.getHighestRank());
			assert diff.checkResult(mStateFactoryInterpolAutom);
			return diff.getResult();
		}
		return gbaDiff.getResult();
	}
}
