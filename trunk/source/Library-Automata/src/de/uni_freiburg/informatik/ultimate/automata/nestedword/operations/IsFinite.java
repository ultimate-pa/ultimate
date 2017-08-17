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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomatonFilteredStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Checks whether the language of a nested word automaton contains only finitely
 * many words.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class IsFinite<LETTER, STATE> extends UnaryNwaOperation<LETTER, STATE, IStateFactory<STATE>> {
	private final boolean mResult;
	private final INestedWordAutomaton<LETTER, STATE> mOperand;

	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            input NWA
	 * @throws AutomataOperationCanceledException 
	 */
	public IsFinite(final AutomataLibraryServices services, final INestedWordAutomaton<LETTER, STATE> operand) throws AutomataOperationCanceledException {
		super(services);
		mOperand = operand;
		mResult = computeIsFinite();
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Language of automaton is a " + (mResult ? "finite" : "infinite") + " set.");
		}
	}

	private boolean computeIsFinite() throws AutomataOperationCanceledException {
		final IDoubleDeckerAutomaton<LETTER, STATE> withoutDeadEnds = new RemoveDeadEnds<>(mServices, mOperand)
				.getResult();
		final NestedWordAutomatonReachableStates<LETTER, STATE> nwars = new NestedWordAutomatonReachableStates<>(
				mServices, withoutDeadEnds);
		final NestedWordAutomatonFilteredStates<LETTER, STATE> allAccepting = new NestedWordAutomatonFilteredStates<>(
				mServices, nwars, nwars.getInitialStates(), nwars.getStates(), nwars.getStates());
		final IDoubleDeckerAutomaton<LETTER, STATE> withoutNonLive = new RemoveNonLiveStates<>(mServices, allAccepting).getResult();
		final boolean isEmpty = new IsEmpty<>(mServices, withoutNonLive).getResult();
		return isEmpty;
	}

	@Override
	protected INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getOperand() {
		return mOperand;
	}

	@Override
	public Boolean getResult() {
		return mResult;
	}
}
