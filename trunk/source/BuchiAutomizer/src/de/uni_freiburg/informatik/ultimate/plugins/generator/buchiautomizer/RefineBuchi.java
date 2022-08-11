/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2022 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.BuchiAutomizerPreferenceInitializer.BuchiComplementationConstruction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.BuchiAutomizerPreferenceInitializer.NcsbImplementation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;

/**
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 */
public class RefineBuchi<LETTER extends IIcfgTransition<?>> {
	private final boolean mDifference;
	private final PredicateFactoryForInterpolantAutomata mStateFactoryInterpolAutom;
	private final PredicateFactoryRefinement mStateFactoryForRefinement;
	private final boolean mUseDoubleDeckers;
	private final NcsbImplementation mNcsbImplementation;
	private final AutomataLibraryServices mServices;

	public RefineBuchi(final boolean difference, final PredicateFactoryForInterpolantAutomata stateFactoryInterpolAutom,
			final PredicateFactoryRefinement stateFactoryForRefinement, final boolean useDoubleDeckers,
			final AutomataLibraryServices services, final NcsbImplementation ncsbImplementation) {
		mServices = services;
		mDifference = difference;
		mStateFactoryInterpolAutom = stateFactoryInterpolAutom;
		mStateFactoryForRefinement = stateFactoryForRefinement;
		mUseDoubleDeckers = useDoubleDeckers;
		mNcsbImplementation = ncsbImplementation;
	}

	public INestedWordAutomaton<LETTER, IPredicate> refineBuchi(
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> abstraction,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> interpolantAutomaton,
			final boolean semiDeterministic, final BuchiCegarLoopBenchmarkGenerator benchmarkGenerator,
			final BuchiComplementationConstruction complementationConstruction) throws AutomataLibraryException {
		final IStateDeterminizer<LETTER, IPredicate> stateDeterminizer =
				new PowersetDeterminizer<>(interpolantAutomaton, mUseDoubleDeckers, mStateFactoryInterpolAutom);
		if (mDifference) {
			final FkvOptimization optimization;
			switch (complementationConstruction) {
			case ELASTIC:
				optimization = FkvOptimization.ELASTIC;
				break;
			case NCSB:
				if (semiDeterministic) {
					return nsbcDifference(abstraction, interpolantAutomaton, benchmarkGenerator);
				}
				optimization = FkvOptimization.ELASTIC;
				break;
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

		final BuchiComplementFKV<LETTER, IPredicate> complNwa = new BuchiComplementFKV<>(mServices,
				mStateFactoryInterpolAutom, interpolantAutomaton, stateDeterminizer);
		benchmarkGenerator.reportHighestRank(complNwa.getHighestRank());
		assert complNwa.checkResult(mStateFactoryInterpolAutom);
		final BuchiIntersect<LETTER, IPredicate> interNwa =
				new BuchiIntersect<>(mServices, mStateFactoryForRefinement, abstraction, complNwa.getResult());
		assert interNwa.checkResult(mStateFactoryInterpolAutom);
		return interNwa.getResult();
	}

	private INestedWordAutomaton<LETTER, IPredicate> nsbcDifference(
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> abstraction,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> interpolantAutomaton,
			final BuchiCegarLoopBenchmarkGenerator benchmarkGenerator) throws AutomataLibraryException {
		benchmarkGenerator.reportHighestRank(3);
		final boolean noCallAndReturn = abstraction.getVpAlphabet().getCallAlphabet().isEmpty()
				&& abstraction.getVpAlphabet().getReturnAlphabet().isEmpty();
		switch (mNcsbImplementation) {
		case INTSET:
			return new BuchiDifferenceNCSBSimple<>(mServices, mStateFactoryForRefinement, abstraction,
					interpolantAutomaton).getResult();
		case INTSET_LAZY:
			return new BuchiDifferenceNCSBLazy<>(mServices, mStateFactoryForRefinement, abstraction,
					interpolantAutomaton).getResult();
		case INTSET_GBA:
			if (noCallAndReturn) {
				return new GeneralizedBuchiDifferenceNCSBSimple<>(mServices, mStateFactoryForRefinement,
						getGeneralizedBuchiAutomaton(abstraction), interpolantAutomaton, false).getResult();
			}
			return new BuchiDifferenceNCSBLazy3<>(mServices, mStateFactoryForRefinement, abstraction,
					interpolantAutomaton).getResult();
		case INTSET_GBA_LAZY:
			if (noCallAndReturn) {
				return new GeneralizedBuchiDifferenceNCSBSimple<>(mServices, mStateFactoryForRefinement,
						getGeneralizedBuchiAutomaton(abstraction), interpolantAutomaton, true).getResult();
			}
			return new BuchiDifferenceNCSBLazy3<>(mServices, mStateFactoryForRefinement, abstraction,
					interpolantAutomaton).getResult();
		case INTSET_GBA_ANTICHAIN:
			if (noCallAndReturn) {
				return new GeneralizedBuchiDifferenceNCSBAntichain<>(mServices, mStateFactoryForRefinement,
						getGeneralizedBuchiAutomaton(abstraction), interpolantAutomaton, false).getResult();
			}
			return new BuchiDifferenceNCSBLazy3<>(mServices, mStateFactoryForRefinement, abstraction,
					interpolantAutomaton).getResult();
		case INTSET_GBA_LAZY_ANTICHAIN:
			if (noCallAndReturn) {
				return new GeneralizedBuchiDifferenceNCSBAntichain<>(mServices, mStateFactoryForRefinement,
						getGeneralizedBuchiAutomaton(abstraction), interpolantAutomaton, true).getResult();
			}
			return new BuchiDifferenceNCSBLazy3<>(mServices, mStateFactoryForRefinement, abstraction,
					interpolantAutomaton).getResult();
		case INTSET_LAZY2:
			return new BuchiDifferenceNCSBLazy2<>(mServices, mStateFactoryForRefinement, abstraction,
					interpolantAutomaton).getResult();
		case INTSET_LAZY3:
			return new BuchiDifferenceNCSBLazy3<>(mServices, mStateFactoryForRefinement, abstraction,
					interpolantAutomaton).getResult();
		case ORIGINAL:
			return new BuchiDifferenceNCSB<>(mServices, mStateFactoryForRefinement, abstraction, interpolantAutomaton)
					.getResult();
		default:
			throw new AssertionError("illegal value");
		}
	}

	private IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>
			getGeneralizedBuchiAutomaton(final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> automaton) {
		if (automaton instanceof IGeneralizedNwaOutgoingLetterAndTransitionProvider) {
			return (IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>) automaton;
		}
		return new BuchiToGeneralizedBuchi<>(automaton);
	}

	private INestedWordAutomaton<LETTER, IPredicate> rankBasedOptimization(
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> abstraction,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> interpolantAutomaton,
			final BuchiCegarLoopBenchmarkGenerator benchmarkGenerator,
			final IStateDeterminizer<LETTER, IPredicate> stateDeterminizer, final FkvOptimization optimization)
			throws AutomataLibraryException {
		if (abstraction instanceof IGeneralizedNwaOutgoingLetterAndTransitionProvider) {
			return new GeneralizedBuchiDifferenceFKV<>(mServices, mStateFactoryForRefinement,
					(IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>) abstraction,
					interpolantAutomaton, stateDeterminizer, optimization, Integer.MAX_VALUE).getResult();
		}
		final var diff = new BuchiDifferenceFKV<>(mServices, mStateFactoryForRefinement, abstraction,
				interpolantAutomaton, stateDeterminizer, optimization, Integer.MAX_VALUE);
		benchmarkGenerator.reportHighestRank(diff.getHighestRank());
		assert diff.checkResult(mStateFactoryInterpolAutom);
		return diff.getResult();
	}
}
