/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.IPredicate;

/**
 * Provides IPredicates for filtering of transitions where the filtering
 * is based on a given set of states. The predicates evaluate to true iff 
 * each state that occurs in the transition is contained in the given set
 * of states.
 * @author Matthias Heizmann
 *
 */
public class StateBasedTransitionFilterPredicateProvider<LETTER, STATE> {
	protected final Set<STATE> m_States;
	private final IPredicate<IncomingInternalTransition<LETTER, STATE>> m_InternalPredecessorsPredicate;
	private final IPredicate<IncomingCallTransition<LETTER, STATE>> m_CallPredecessorPredicate;
	private final IPredicate<OutgoingInternalTransition<LETTER, STATE>> m_InternalSuccessorPredicate;
	private final IPredicate<OutgoingCallTransition<LETTER, STATE>> m_CallSuccessorPredicate;
	private final IPredicate<IncomingReturnTransition<LETTER, STATE>> m_ReturnPredecessorPredicate;
	private final IPredicate<OutgoingReturnTransition<LETTER, STATE>> m_ReturnSuccessorPredicate;
	private final IPredicate<SummaryReturnTransition<LETTER, STATE>> m_ReturnSummaryPredicate;
	
	public StateBasedTransitionFilterPredicateProvider(Set<STATE> states) {
		m_States = states;
		
		m_InternalPredecessorsPredicate = new IPredicate<IncomingInternalTransition<LETTER,STATE>>() {
			@Override
			public boolean evaluate(IncomingInternalTransition<LETTER, STATE> trans) {
				return m_States.contains(trans.getPred());
			}
		};

		m_CallPredecessorPredicate = new IPredicate<IncomingCallTransition<LETTER,STATE>>() {
			@Override
			public boolean evaluate(IncomingCallTransition<LETTER, STATE> trans) {
				return m_States.contains(trans.getPred());
			}
		};

		m_InternalSuccessorPredicate = new IPredicate<OutgoingInternalTransition<LETTER,STATE>>() {
			@Override
			public boolean evaluate(OutgoingInternalTransition<LETTER, STATE> trans) {
				return m_States.contains(trans.getSucc());
			}
		};

		m_CallSuccessorPredicate = new IPredicate<OutgoingCallTransition<LETTER,STATE>>() {
			@Override
			public boolean evaluate(OutgoingCallTransition<LETTER, STATE> trans) {
				return m_States.contains(trans.getSucc());
			}
		};

		m_ReturnPredecessorPredicate = new IPredicate<IncomingReturnTransition<LETTER,STATE>>() {
			@Override
			public boolean evaluate(IncomingReturnTransition<LETTER, STATE> trans) {
				return m_States.contains(trans.getLinPred()) && m_States.contains(trans.getHierPred());
			}
		};
		
		m_ReturnSuccessorPredicate = new IPredicate<OutgoingReturnTransition<LETTER,STATE>>() {
			@Override
			public boolean evaluate(OutgoingReturnTransition<LETTER, STATE> trans) {
				return m_States.contains(trans.getHierPred()) && m_States.contains(trans.getSucc());
			}
		};

		m_ReturnSummaryPredicate = new IPredicate<SummaryReturnTransition<LETTER,STATE>>() {
			@Override
			public boolean evaluate(SummaryReturnTransition<LETTER, STATE> trans) {
				return m_States.contains(trans.getSucc()) && m_States.contains(trans.getLinPred());
			}
		};
	}

	public IPredicate<IncomingInternalTransition<LETTER, STATE>> getInternalPredecessorsPredicate() {
		return m_InternalPredecessorsPredicate;
	}

	public IPredicate<IncomingCallTransition<LETTER, STATE>> getCallPredecessorPredicate() {
		return m_CallPredecessorPredicate;
	}

	public IPredicate<OutgoingInternalTransition<LETTER, STATE>> getInternalSuccessorPredicate() {
		return m_InternalSuccessorPredicate;
	}

	public IPredicate<OutgoingCallTransition<LETTER, STATE>> getCallSuccessorPredicate() {
		return m_CallSuccessorPredicate;
	}

	public IPredicate<IncomingReturnTransition<LETTER, STATE>> getReturnPredecessorPredicate() {
		return m_ReturnPredecessorPredicate;
	}

	public IPredicate<OutgoingReturnTransition<LETTER, STATE>> getReturnSuccessorPredicate() {
		return m_ReturnSuccessorPredicate;
	}

	public IPredicate<SummaryReturnTransition<LETTER, STATE>> getReturnSummaryPredicate() {
		return m_ReturnSummaryPredicate;
	}
	
	

}
