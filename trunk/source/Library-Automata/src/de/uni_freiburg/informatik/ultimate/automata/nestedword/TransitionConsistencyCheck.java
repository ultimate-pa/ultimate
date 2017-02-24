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
 * Check if transitions of an automaton are stored consistently.
 * <p>
 * Consistency here means that an outgoing transition from state <tt>p</tt> to state <tt>q</tt> is also an incoming
 * transition for <tt>q</tt> from <tt>p</tt>.
 * <p>
 * This is slow! Use only for testing on small examples.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class TransitionConsistencyCheck<LETTER, STATE> {
	private final INestedWordAutomaton<LETTER, STATE> mNwa;

	/**
	 * Constructor.
	 * 
	 * @param nwa
	 *            double decker automaton
	 */
	public TransitionConsistencyCheck(final INestedWordAutomaton<LETTER, STATE> nwa) {
		mNwa = nwa;
	}

	/**
	 * @return true iff automaton transitions are stored consistently for all states.
	 */
	public boolean consistentForAll() {
		boolean result = true;
		for (final STATE state : mNwa.getStates()) {
			result = result && consistentForState(state);
		}
		return result;
	}

	/**
	 * TODO Christian 2016-08-27: This could be made much more efficient by
	 * <ol>
	 * <li>storing all transitions in a list/map and removing from it<br>
	 * (the memory overhead should be negligible as it is only for one state);</li>
	 * <li>using the transition methods with a given letter<br>
	 * (this may go against the idea of the class, discuss this).</li>
	 * </ol>
	 * 
	 * @param state
	 *            state
	 * @return true iff all transitions are stored consistently for the given state.
	 */
	@SuppressWarnings("squid:MethodCyclomaticComplexity")
	private boolean consistentForState(final STATE state) {
		boolean result = true;
		for (final OutgoingInternalTransition<LETTER, STATE> trans : mNwa.internalSuccessors(state)) {
			result = result && internalIn(state, trans.getLetter(), trans.getSucc());
			assert result;
		}
		for (final IncomingInternalTransition<LETTER, STATE> trans : mNwa.internalPredecessors(state)) {
			result = result && internalOut(trans.getPred(), trans.getLetter(), state);
			assert result;
		}
		for (final OutgoingCallTransition<LETTER, STATE> trans : mNwa.callSuccessors(state)) {
			result = result && callIn(state, trans.getLetter(), trans.getSucc());
			assert result;
		}
		for (final IncomingCallTransition<LETTER, STATE> trans : mNwa.callPredecessors(state)) {
			result = result && callOut(trans.getPred(), trans.getLetter(), state);
			assert result;
		}
		for (final OutgoingReturnTransition<LETTER, STATE> trans : mNwa.returnSuccessors(state)) {
			result = result && returnIn(state, trans.getHierPred(), trans.getLetter(), trans.getSucc());
			assert result;
			result = result && returnSummary(state, trans.getHierPred(), trans.getLetter(), trans.getSucc());
			assert result;
		}
		for (final IncomingReturnTransition<LETTER, STATE> trans : mNwa.returnPredecessors(state)) {
			result = result && returnOut(trans.getLinPred(), trans.getHierPred(), trans.getLetter(), state);
			assert result;
			result = result && returnSummary(trans.getLinPred(), trans.getHierPred(), trans.getLetter(), state);
			assert result;
		}
		for (final LETTER letter : mNwa.getReturnAlphabet()) {
			for (final SummaryReturnTransition<LETTER, STATE> trans : mNwa.summarySuccessors(state, letter)) {
				result = result && returnIn(trans.getLinPred(), state, trans.getLetter(), trans.getSucc());
				assert result;
				result = result && returnOut(trans.getLinPred(), state, trans.getLetter(), trans.getSucc());
				assert result;
			}
		}
		return result;
	}

	private boolean internalOut(final STATE state, final LETTER letter, final STATE succ) {
		for (final OutgoingInternalTransition<LETTER, STATE> trans : mNwa.internalSuccessors(state)) {
			final boolean contains = letter.equals(trans.getLetter()) && succ.equals(trans.getSucc());
			if (contains) {
				return true;
			}
		}
		return false;
	}

	private boolean internalIn(final STATE pred, final LETTER letter, final STATE succ) {
		for (final IncomingInternalTransition<LETTER, STATE> trans : mNwa.internalPredecessors(succ)) {
			final boolean contains = pred.equals(trans.getPred()) && letter.equals(trans.getLetter());
			if (contains) {
				return true;
			}
		}
		return false;
	}

	private boolean callOut(final STATE state, final LETTER letter, final STATE succ) {
		for (final OutgoingCallTransition<LETTER, STATE> trans : mNwa.callSuccessors(state)) {
			final boolean contains = letter.equals(trans.getLetter()) && succ.equals(trans.getSucc());
			if (contains) {
				return true;
			}
		}
		return false;
	}

	private boolean callIn(final STATE pred, final LETTER letter, final STATE succ) {
		for (final IncomingCallTransition<LETTER, STATE> trans : mNwa.callPredecessors(succ)) {
			final boolean contains = pred.equals(trans.getPred()) && letter.equals(trans.getLetter());
			if (contains) {
				return true;
			}
		}
		return false;
	}

	private boolean returnOut(final STATE state, final STATE hier, final LETTER letter, final STATE succ) {
		for (final OutgoingReturnTransition<LETTER, STATE> trans : mNwa.returnSuccessors(state)) {
			final boolean contains = hier.equals(trans.getHierPred()) && letter.equals(trans.getLetter())
					&& succ.equals(trans.getSucc());
			if (contains) {
				return true;
			}
		}
		return false;
	}

	private boolean returnIn(final STATE state, final STATE hier, final LETTER letter, final STATE succ) {
		for (final IncomingReturnTransition<LETTER, STATE> trans : mNwa.returnPredecessors(succ)) {
			final boolean contains = state.equals(trans.getLinPred()) && hier.equals(trans.getHierPred())
					&& letter.equals(trans.getLetter());
			if (contains) {
				return true;
			}
		}
		return false;
	}

	private boolean returnSummary(final STATE state, final STATE hier, final LETTER letter, final STATE succ) {
		for (final SummaryReturnTransition<LETTER, STATE> trans : mNwa.summarySuccessors(hier, letter)) {
			final boolean contains = state.equals(trans.getLinPred()) && succ.equals(trans.getSucc());
			if (contains) {
				return true;
			}
		}
		return false;
	}
}
