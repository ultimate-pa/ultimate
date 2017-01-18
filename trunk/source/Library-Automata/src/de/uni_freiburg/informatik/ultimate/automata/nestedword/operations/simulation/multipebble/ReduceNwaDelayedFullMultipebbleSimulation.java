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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.TestBuchiEquivalence;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveDeadEnds;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveNonLiveStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * TODO: documentation
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class ReduceNwaDelayedFullMultipebbleSimulation<LETTER, STATE> extends ReduceNwaFullMultipebbleSimulation<LETTER, STATE, DelayedFullMultipebbleGameState<STATE>> {
	
	public ReduceNwaDelayedFullMultipebbleSimulation(final AutomataLibraryServices services, final IStateFactory<STATE> stateFactory,
			final IDoubleDeckerAutomaton<LETTER, STATE> operand)
			throws AutomataOperationCanceledException {
		super(services, stateFactory, operand);
	}
		
	@Override
	protected FullMultipebbleStateFactory<STATE, DelayedFullMultipebbleGameState<STATE>> constructGameFactory() {
		return new DelayedFullMultipebbleStateFactory<>();
	}
	
	@Override
	protected IDoubleDeckerAutomaton<LETTER, DelayedFullMultipebbleGameState<STATE>> computeSimulation(
			final FullMultipebbleGameAutomaton<LETTER, STATE, DelayedFullMultipebbleGameState<STATE>> gameAutomaton)
			throws AutomataOperationCanceledException {
		final IDoubleDeckerAutomaton<LETTER, DelayedFullMultipebbleGameState<STATE>> tmp1 = new RemoveNonLiveStates<>(mServices, gameAutomaton).getResult();
		final Set<DelayedFullMultipebbleGameState<STATE>> allBitsAreTrue = new HashSet<>();
		for (final DelayedFullMultipebbleGameState<STATE> state : tmp1.getStates()) {
			if (state.areAllBitsTrue()) {
				allBitsAreTrue.add(state);
			}
		}
		final NestedWordAutomatonFilteredStates<LETTER, DelayedFullMultipebbleGameState<STATE>> tmp2 =
				new NestedWordAutomatonFilteredStates<>(mServices, (NestedWordAutomatonReachableStates<LETTER, DelayedFullMultipebbleGameState<STATE>>) tmp1, allBitsAreTrue, allBitsAreTrue, allBitsAreTrue);
		final IDoubleDeckerAutomaton<LETTER, DelayedFullMultipebbleGameState<STATE>> tmp3 = new RemoveNonLiveStates<>(mServices, tmp2).getResult();
		
		final NestedWordAutomatonFilteredStates<LETTER, DelayedFullMultipebbleGameState<STATE>> tmp4 =
				new NestedWordAutomatonFilteredStates<>(mServices, (NestedWordAutomatonReachableStates<LETTER, DelayedFullMultipebbleGameState<STATE>>) tmp1, tmp1.getStates(), tmp1.getInitialStates(), tmp3.getStates());
		final IDoubleDeckerAutomaton<LETTER, DelayedFullMultipebbleGameState<STATE>> result = new RemoveDeadEnds<>(mServices, tmp4).getResult();
		return result;
	}
	
	
	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		mLogger.info("Start testing correctness of " + operationName());
		final boolean correct = (new TestBuchiEquivalence<LETTER, STATE>(mServices, stateFactory, getOperand(),
				getResult())).getResult();
		mLogger.info("Finished testing correctness of " + operationName());
		return correct;
	}

}


