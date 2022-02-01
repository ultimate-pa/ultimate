/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.multipebble;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomatonFilteredStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveDeadEnds;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveNonLiveStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.IMinimizationCheckResultStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.IMinimizationStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.util.ISetOfPairs;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * TODO: documentation.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class ReduceNwaDelayedFullMultipebbleSimulation<LETTER, STATE>
		extends ReduceNwaFullMultipebbleSimulation<LETTER, STATE, DelayedFullMultipebbleGameState<STATE>> {

	public ReduceNwaDelayedFullMultipebbleSimulation(final AutomataLibraryServices services,
			final IMinimizationStateFactory<STATE> stateFactory, final IDoubleDeckerAutomaton<LETTER, STATE> operand)
			throws AutomataOperationCanceledException {
		super(services, stateFactory, operand, true);
	}

	@Override
	protected FullMultipebbleStateFactory<STATE, DelayedFullMultipebbleGameState<STATE>>
			constructGameFactory(final ISetOfPairs<STATE, ?> initialPairs) {
		return new DelayedFullMultipebbleStateFactory<>(initialPairs);
	}

	@Override
	protected Pair<IDoubleDeckerAutomaton<LETTER, DelayedFullMultipebbleGameState<STATE>>, Integer> computeSimulation(
			final FullMultipebbleGameAutomaton<LETTER, STATE, DelayedFullMultipebbleGameState<STATE>> gameAutomaton)
			throws AutomataOperationCanceledException {
		final RemoveNonLiveStates<LETTER, DelayedFullMultipebbleGameState<STATE>> rnls =
				new RemoveNonLiveStates<>(mServices, gameAutomaton);
		final int maxGameAutomatonSize = rnls.getInputSize();
		final IDoubleDeckerAutomaton<LETTER, DelayedFullMultipebbleGameState<STATE>> tmp1 = rnls.getResult();
		final Set<DelayedFullMultipebbleGameState<STATE>> goodForSpoiler = new HashSet<>();
		for (final DelayedFullMultipebbleGameState<STATE> state : tmp1.getStates()) {
			if (state.isEmptyOrSomeBitIsTrue()) {
				goodForSpoiler.add(state);
			}
		}
		final NestedWordAutomatonFilteredStates<LETTER, DelayedFullMultipebbleGameState<STATE>> tmp2 =
				new NestedWordAutomatonFilteredStates<>(mServices,
						(NestedWordAutomatonReachableStates<LETTER, DelayedFullMultipebbleGameState<STATE>>) tmp1,
						goodForSpoiler, goodForSpoiler, goodForSpoiler);
		final IDoubleDeckerAutomaton<LETTER, DelayedFullMultipebbleGameState<STATE>> tmp3 =
				new RemoveNonLiveStates<>(mServices, tmp2).getResult();

		final NestedWordAutomatonFilteredStates<LETTER, DelayedFullMultipebbleGameState<STATE>> tmp4 =
				new NestedWordAutomatonFilteredStates<>(mServices,
						(NestedWordAutomatonReachableStates<LETTER, DelayedFullMultipebbleGameState<STATE>>) tmp1,
						tmp1.getStates(), tmp1.getInitialStates(), tmp3.getStates());
		final IDoubleDeckerAutomaton<LETTER, DelayedFullMultipebbleGameState<STATE>> result =
				new RemoveDeadEnds<>(mServices, tmp4).getResult();
		return new Pair<>(result, maxGameAutomatonSize);
	}

	@Override
	protected Pair<Boolean, String> checkResultHelper(final IMinimizationCheckResultStateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		return checkBuchiEquivalence(stateFactory);
	}
}
