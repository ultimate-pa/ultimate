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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.SummaryReturnTransition;


/**
 * Check if transitions of an automaton are stored consistent. This is slow!
 * Use only for testing on small examples.
 * @author heizmann@informatik.uni-freiburg.de
 */
public class TransitionConsitenceCheck<LETTER, STATE> {
	
	INestedWordAutomatonOldApi<LETTER, STATE> mNwa;
	
	public TransitionConsitenceCheck(INestedWordAutomatonOldApi<LETTER, STATE> nwa) {
		mNwa = nwa;
	}
	
	public boolean consistentForAll() {
		boolean result = true;
		for (STATE state : mNwa.getStates()) {
			result &= consistentForState(state);
		}
		return result;
	}
	
	private boolean consistentForState(STATE state) {
		boolean result = true;
		for (OutgoingInternalTransition<LETTER, STATE> t : mNwa.internalSuccessors(state)) {
			result &= internalIn(state, t.getLetter(), t.getSucc());
			assert result;
		}
		for (IncomingInternalTransition<LETTER, STATE> t : mNwa.internalPredecessors(state)) {
			result &= internalOut(t.getPred(), t.getLetter(), state);
			assert result;
		}
		for (OutgoingCallTransition<LETTER, STATE> t : mNwa.callSuccessors(state)) {
			result &= callIn(state, t.getLetter(), t.getSucc());
			assert result;
		}
		for (IncomingCallTransition<LETTER, STATE> t : mNwa.callPredecessors(state)) {
			result &= callOut(t.getPred(), t.getLetter(), state);
			assert result;
		}
		for (OutgoingReturnTransition<LETTER, STATE> t : mNwa.returnSuccessors(state)) {
			result &= returnIn(state, t.getHierPred(), t.getLetter(), t.getSucc());
			assert result;
			result &= returnSummary(state, t.getHierPred(), t.getLetter(), t.getSucc());
			assert result;
		}
		for (IncomingReturnTransition<LETTER, STATE> t : mNwa.returnPredecessors(state)) {
			result &= returnOut(t.getLinPred(), t.getHierPred(), t.getLetter(), state);
			assert result;
			result &= returnSummary(t.getLinPred(), t.getHierPred(), t.getLetter(), state);
			assert result;
		}
		for (LETTER letter : mNwa.getReturnAlphabet()) {
			for (SummaryReturnTransition<LETTER, STATE> t : mNwa.returnSummarySuccessor(letter, state)) {
				result &= returnIn(t.getLinPred(), state, t.getLetter(), t.getSucc());
				assert result;
				result &= returnOut(t.getLinPred(), state, t.getLetter(), t.getSucc());
				assert result;
			}
		}
		return result;
	}
	
	private boolean internalOut(STATE state, LETTER letter, STATE succ) {
		for (OutgoingInternalTransition<LETTER, STATE> t : mNwa.internalSuccessors(state)) {
			boolean contains = letter.equals(t.getLetter()) && succ.equals(t.getSucc());
			if (contains) return true;
		}
		return false;
	}
	
	private boolean internalIn(STATE pred, LETTER letter, STATE succ) {
		for (IncomingInternalTransition<LETTER, STATE> t : mNwa.internalPredecessors(succ)) {
			boolean contains = pred.equals(t.getPred()) && letter.equals(t.getLetter());
			if (contains) return true;
		}
		return false;
	}
	
	private boolean callOut(STATE state, LETTER letter, STATE succ) {
		for (OutgoingCallTransition<LETTER, STATE> t : mNwa.callSuccessors(state)) {
			boolean contains = letter.equals(t.getLetter()) && succ.equals(t.getSucc());
			if (contains) return true;
		}
		return false;
	}
	
	private boolean callIn(STATE pred, LETTER letter, STATE succ) {
		for (IncomingCallTransition<LETTER, STATE> t : mNwa.callPredecessors(succ)) {
			boolean contains = pred.equals(t.getPred()) && letter.equals(t.getLetter());
			if (contains) return true;
		}
		return false;
	}
	
	
	private boolean returnOut(STATE state, STATE hier, LETTER letter, STATE succ) {
		for (OutgoingReturnTransition<LETTER, STATE> t : mNwa.returnSuccessors(state)) {
			boolean contains = hier.equals(t.getHierPred()) && letter.equals(t.getLetter()) && succ.equals(t.getSucc());
			if (contains) return true;
		}
		return false;
	}
	
	private boolean returnIn(STATE state, STATE hier, LETTER letter, STATE succ) {
		for (IncomingReturnTransition<LETTER, STATE> t : mNwa.returnPredecessors(succ)) {
			boolean contains = state.equals(t.getLinPred()) && hier.equals(t.getHierPred()) && letter.equals(t.getLetter());
			if (contains) return true;
		}
		return false;
	}
	
	private boolean returnSummary(STATE state, STATE hier, LETTER letter, STATE succ) {
		for (SummaryReturnTransition<LETTER, STATE> t : mNwa.returnSummarySuccessor(letter, hier)) {
			boolean contains = state.equals(t.getLinPred()) && succ.equals(t.getSucc());
			if (contains) return true;
		}
		return false;
	}


}
