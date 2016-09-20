/*
 * Copyright (C) 2014-2015 Markus Pomrehn
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.alternating.visualization;

import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.alternating.AlternatingAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.visualization.AutomatonState;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;

/**
 * Converts an {@link AlternatingAutomaton} to an Ultimate model.
 * <p>
 * TODO Christian 2016-09-18: This class is completely broken/useless.
 * 
 * @author Markus Pomrehn
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class AAToUltimateModel<LETTER, STATE> {
	/**
	 * @param operand
	 *            An alternating automaton.
	 * @return Ultimate model
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public IElement getUltimateModelOfAA(final AlternatingAutomaton<LETTER, STATE> operand)
			throws AutomataOperationCanceledException {
		/*
		final AlternatingAutomaton<LETTER, STATE> aa;
		aa = (AlternatingAutomaton<LETTER, STATE>) aaSimple;
		final Map<STATE, AutomatonState> constructed = new HashMap<>();
		final LinkedList<STATE> queue = new LinkedList<>();
		
		// add all initial states to model - all are successors of the graphroot
		for (final STATE state : aa.getInitialStates()) {
			queue.add(state);
			final AutomatonState vsn = new AutomatonState(state,
					nwa.isFinal(state));
			constructed.put(state, vsn);
			new AutomatonTransition((AutomatonState) graphroot,
					Transition.INTERNAL, "", null, vsn);
		}
		
		while (!queue.isEmpty()) {
			final STATE state = queue.removeFirst();
			final AutomatonState vsn = constructed.get(state);
			
			for (final OutgoingInternalTransition<LETTER, STATE> trans : nwa.internalSuccessors(state)) {
				final LETTER symbol = trans.getLetter();
				final STATE succState = trans.getSucc();
				AutomatonState succVSN;
				if (constructed.containsKey(succState)) {
					succVSN = constructed.get(succState);
				} else {
					succVSN = new AutomatonState(succState,
							nwa.isFinal(succState));
					mLogger.debug("Creating Node: " + succVSN.toString());
					constructed.put(succState, succVSN);
					queue.add(succState);
				}
				new AutomatonTransition(vsn, Transition.INTERNAL, symbol, null, succVSN);
			}
			
			for (final OutgoingCallTransition<LETTER, STATE> trans : nwa.callSuccessors(state)) {
				final LETTER symbol = trans.getLetter();
				final STATE succState = trans.getSucc();
				AutomatonState succVSN;
				if (constructed.containsKey(succState)) {
					succVSN = constructed.get(succState);
				} else {
					succVSN = new AutomatonState(succState,
							nwa.isFinal(succState));
					mLogger.debug("Creating Node: " + succVSN.toString());
					constructed.put(succState, succVSN);
					queue.add(succState);
				}
				new AutomatonTransition(vsn, Transition.CALL, symbol, null, succVSN);
			}
			for (final STATE hierPredState : nwa.getStates()) {
				for (final OutgoingReturnTransition<LETTER, STATE> trans : nwa.returnSuccessorsGivenHier(state,
						hierPredState)) {
					final LETTER symbol = trans.getLetter();
					final STATE succState = trans.getSucc();
					AutomatonState succVSN;
					if (constructed.containsKey(succState)) {
						succVSN = constructed.get(succState);
					} else {
						succVSN = new AutomatonState(succState, nwa.isFinal(succState));
						mLogger.debug("Creating Node: " + succVSN.toString());
						constructed.put(succState, succVSN);
						queue.add(succState);
					}
					new AutomatonTransition(vsn, Transition.RETURN, symbol,
							hierPredState.toString(), succVSN);
				}
			}
		}
		*/
		System.out.println("Foo");
		return new AutomatonState("Sucessors of this node are the initial states", false);
	}
}
