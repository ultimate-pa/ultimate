/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker plug-in.
 *
 * The ULTIMATE LassoRanker plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LassoRanker plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LassoRanker plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiAccepts;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public final class LassoAutomatonBuilder<LETTER> {

	private final NestedWordAutomaton<LETTER, IPredicate> mResult;
	private final PredicateFactory mPredicateFactory;

	public LassoAutomatonBuilder(final VpAlphabet<LETTER> alphabet,
			final IEmptyStackStateFactory<IPredicate> predicateFactoryRc, final PredicateFactory predicateFactory,
			final NestedWord<LETTER> stem, final NestedWord<LETTER> loop, final IUltimateServiceProvider services)
			throws AutomataOperationCanceledException {
		mPredicateFactory = predicateFactory;
		mResult = new NestedWordAutomaton<>(new AutomataLibraryServices(services), alphabet, predicateFactoryRc);
		final List<IPredicate> stemStates = constructListOfDontCarePredicates(stem.length());
		final List<IPredicate> loopStates = constructListOfDontCarePredicates(loop.length());
		IPredicate initialState;
		if (stem.length() == 0) {
			initialState = loopStates.get(0);
			mResult.addState(true, true, initialState);
		} else {
			initialState = stemStates.get(0);
			mResult.addState(true, false, initialState);
		}
		final IPredicate hondaState = loopStates.get(0);
		if (stem.length() > 0) {
			mResult.addState(false, true, hondaState);
		}
		stemStates.add(hondaState);
		loopStates.add(hondaState);
		addSequenceOfStatesButFirstAndLast(stemStates);
		mResult.addTransitions(stem, stemStates);
		addSequenceOfStatesButFirstAndLast(loopStates);
		mResult.addTransitions(loop, loopStates);
		try {
			assert new BuchiAccepts<>(new AutomataLibraryServices(services), mResult, new NestedLassoWord<>(stem, loop))
					.getResult();
		} catch (final AutomataLibraryException e) {
			throw new AssertionError(e);
		}
	}

	private List<IPredicate> constructListOfDontCarePredicates(final int length) {
		final ArrayList<IPredicate> result = new ArrayList<>(length);
		for (int i = 0; i < length; i++) {
			result.add(mPredicateFactory.newDontCarePredicate(null));
		}
		return result;
	}

	private void addSequenceOfStatesButFirstAndLast(final List<IPredicate> states) {
		for (int i = 1; i < states.size() - 1; i++) {
			mResult.addState(false, false, states.get(i));
		}
	}

	public INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> getResult() {
		return mResult;
	}
}
