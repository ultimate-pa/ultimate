/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.SummaryReturnTransition;


/**
 * Check if transitions of an automaton are stored consistently. This is slow!
 * Use only for testing on small examples.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * 
 * @param <LETTER> letter type
 * @param <STATE> state type
 */
public class TransitionConsistencyCheck<LETTER, STATE> {
	
	private final IDoubleDeckerAutomaton<LETTER, STATE> mNwa;
	
	/**
	 * @param nwa double decker automaton
	 */
	public TransitionConsistencyCheck(final IDoubleDeckerAutomaton<LETTER, STATE> nwa) {
		mNwa = nwa;
	}
	
	public boolean consistentForAll() {
		boolean result = true;
		for (final STATE state : mNwa.getStates()) {
			result &= consistentForState(state);
		}
		return result;
	}
	
	private boolean consistentForState(final STATE state) {
		boolean result = true;
		for (final OutgoingInternalTransition<LETTER, STATE> t : mNwa.internalSuccessors(state)) {
			result &= internalIn(state, t.getLetter(), t.getSucc());
			assert result;
		}
		for (final IncomingInternalTransition<LETTER, STATE> t : mNwa.internalPredecessors(state)) {
			result &= internalOut(t.getPred(), t.getLetter(), state);
			assert result;
		}
		for (final OutgoingCallTransition<LETTER, STATE> t : mNwa.callSuccessors(state)) {
			result &= callIn(state, t.getLetter(), t.getSucc());
			assert result;
		}
		for (final IncomingCallTransition<LETTER, STATE> t : mNwa.callPredecessors(state)) {
			result &= callOut(t.getPred(), t.getLetter(), state);
			assert result;
		}
		for (final OutgoingReturnTransition<LETTER, STATE> t : mNwa.returnSuccessors(state)) {
			result &= returnIn(state, t.getHierPred(), t.getLetter(), t.getSucc());
			assert result;
			result &= returnSummary(state, t.getHierPred(), t.getLetter(), t.getSucc());
			assert result;
		}
		for (final IncomingReturnTransition<LETTER, STATE> t : mNwa.returnPredecessors(state)) {
			result &= returnOut(t.getLinPred(), t.getHierPred(), t.getLetter(), state);
			assert result;
			result &= returnSummary(t.getLinPred(), t.getHierPred(), t.getLetter(), state);
			assert result;
		}
		for (final LETTER letter : mNwa.getReturnAlphabet()) {
			for (final SummaryReturnTransition<LETTER, STATE> t : mNwa.summarySuccessors(state, letter)) {
				result &= returnIn(t.getLinPred(), state, t.getLetter(), t.getSucc());
				assert result;
				result &= returnOut(t.getLinPred(), state, t.getLetter(), t.getSucc());
				assert result;
			}
		}
		return result;
	}
	
	private boolean internalOut(final STATE state, final LETTER letter, final STATE succ) {
		for (final OutgoingInternalTransition<LETTER, STATE> t : mNwa.internalSuccessors(state)) {
			final boolean contains = letter.equals(t.getLetter())
					&& succ.equals(t.getSucc());
			if (contains) {
				return true;
			}
		}
		return false;
	}
	
	private boolean internalIn(final STATE pred, final LETTER letter, final STATE succ) {
		for (final IncomingInternalTransition<LETTER, STATE> t : mNwa.internalPredecessors(succ)) {
			final boolean contains = pred.equals(t.getPred())
					&& letter.equals(t.getLetter());
			if (contains) {
				return true;
			}
		}
		return false;
	}
	
	private boolean callOut(final STATE state, final LETTER letter, final STATE succ) {
		for (final OutgoingCallTransition<LETTER, STATE> t : mNwa.callSuccessors(state)) {
			final boolean contains = letter.equals(t.getLetter())
					&& succ.equals(t.getSucc());
			if (contains) {
				return true;
			}
		}
		return false;
	}
	
	private boolean callIn(final STATE pred, final LETTER letter, final STATE succ) {
		for (final IncomingCallTransition<LETTER, STATE> t : mNwa.callPredecessors(succ)) {
			final boolean contains = pred.equals(t.getPred())
					&& letter.equals(t.getLetter());
			if (contains) {
				return true;
			}
		}
		return false;
	}
	
	
	private boolean returnOut(final STATE state, final STATE hier,
			final LETTER letter, final STATE succ) {
		for (final OutgoingReturnTransition<LETTER, STATE> t : mNwa.returnSuccessors(state)) {
			final boolean contains = hier.equals(t.getHierPred())
					&& letter.equals(t.getLetter()) && succ.equals(t.getSucc());
			if (contains) {
				return true;
			}
		}
		return false;
	}
	
	private boolean returnIn(final STATE state, final STATE hier,
			final LETTER letter, final STATE succ) {
		for (final IncomingReturnTransition<LETTER, STATE> t : mNwa.returnPredecessors(succ)) {
			final boolean contains = state.equals(t.getLinPred())
					&& hier.equals(t.getHierPred()) && letter.equals(t.getLetter());
			if (contains) {
				return true;
			}
		}
		return false;
	}
	
	private boolean returnSummary(final STATE state, final STATE hier,
			final LETTER letter, final STATE succ) {
		for (final SummaryReturnTransition<LETTER, STATE> t : mNwa.summarySuccessors(hier, letter)) {
			final boolean contains = state.equals(t.getLinPred())
					&& succ.equals(t.getSucc());
			if (contains) {
				return true;
			}
		}
		return false;
	}


}
