/*
 * Copyright (C) 2009-2014 University of Freiburg
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
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;

/**
 * Totalized automaton of input. Expects that input is deterministic.
 * If a transition is nondeterminisic an empty transition set is returned and
 * m_NondeterminismInInputDetected is set to true.
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <LETTER>
 * @param <STATE>
 */
public class TotalizeNwa<LETTER, STATE> implements INestedWordAutomatonSimple<LETTER, STATE> {
	
	private final INestedWordAutomatonSimple<LETTER, STATE> m_Operand;
	private final StateFactory<STATE> m_StateFactory;
	private final STATE m_SinkState;
	private boolean m_NondeterminismInInputDetected = false;

	public boolean nonDeterminismInInputDetected() {
		return m_NondeterminismInInputDetected;
	}
	
	public TotalizeNwa(INestedWordAutomatonSimple<LETTER, STATE> operand, 
			StateFactory<STATE> sf) {
		m_Operand = operand;
		m_StateFactory = sf;
		m_SinkState = sf.createSinkStateContent();
	}
	
	
	@Override
	public Iterable<STATE> getInitialStates() {
		Iterator<STATE> it = m_Operand.getInitialStates().iterator();
		STATE initial;
		if (it.hasNext()) {
			initial = it.next();
		} else {
			initial = m_SinkState;
		}
		if (it.hasNext()) {
			m_NondeterminismInInputDetected = true;
		}
		HashSet<STATE> result = new HashSet<STATE>(1);
		result.add(initial);
		return result;
		
	}


	@Override
	public Set<LETTER> getInternalAlphabet() {
		return m_Operand.getInternalAlphabet();
	}

	@Override
	public Set<LETTER> getCallAlphabet() {
		return m_Operand.getCallAlphabet();
	}

	@Override
	public Set<LETTER> getReturnAlphabet() {
		return m_Operand.getReturnAlphabet();
	}

	@Override
	public StateFactory<STATE> getStateFactory() {
		return m_StateFactory;
	}
	
	@Override
	public boolean isInitial(STATE state) {
		if (state == m_SinkState) {
			return false;
		} else {
			return m_Operand.isInitial(state);
		}
	}

	@Override
	public boolean isFinal(STATE state) {
		if (state == m_SinkState) {
			return false;
		} else {
			return m_Operand.isFinal(state);
		}
	}



	@Override
	public STATE getEmptyStackState() {
		return m_Operand.getEmptyStackState();
	}

	@Override
	public Set<LETTER> lettersInternal(STATE state) {
		return m_Operand.getInternalAlphabet();
	}

	@Override
	public Set<LETTER> lettersCall(STATE state) {
		return m_Operand.getCallAlphabet();
	}

	@Override
	public Set<LETTER> lettersReturn(STATE state) {
		return m_Operand.getReturnAlphabet();
	}


	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			STATE state, LETTER letter) {
		if (m_NondeterminismInInputDetected) {
			return new HashSet<OutgoingInternalTransition<LETTER, STATE>>(0);
		}
		if (state != m_SinkState) {
			Iterator<OutgoingInternalTransition<LETTER, STATE>> it = 
					m_Operand.internalSuccessors(state, letter).iterator();
			if (it.hasNext()) {
				it.next();
				if (it.hasNext()) {
					m_NondeterminismInInputDetected = true;
					return new HashSet<OutgoingInternalTransition<LETTER, STATE>>(0);
				} else {
					return m_Operand.internalSuccessors(state, letter);
				}
			}
		}
		OutgoingInternalTransition<LETTER, STATE> trans = 
				new OutgoingInternalTransition<LETTER, STATE>(letter, m_SinkState);
		ArrayList<OutgoingInternalTransition<LETTER, STATE>> result = 
				new ArrayList<OutgoingInternalTransition<LETTER, STATE>>(1);
		result.add(trans);
		return result;
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			STATE state) {
		if (m_NondeterminismInInputDetected) {
			return new HashSet<OutgoingInternalTransition<LETTER, STATE>>(0);
		}
		ArrayList<OutgoingInternalTransition<LETTER, STATE>> result = 
				new ArrayList<OutgoingInternalTransition<LETTER, STATE>>();
		for (LETTER letter : getInternalAlphabet()) {
			Iterator<OutgoingInternalTransition<LETTER, STATE>> it = 
					internalSuccessors(state, letter).iterator();
			if (m_NondeterminismInInputDetected) {
				return new HashSet<OutgoingInternalTransition<LETTER, STATE>>(0);
			}
			result.add(it.next());
			assert !it.hasNext();
		}
		return result;
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			STATE state, LETTER letter) {
		if (m_NondeterminismInInputDetected) {
			return new HashSet<OutgoingCallTransition<LETTER, STATE>>(0);
		}
		if (state != m_SinkState) {
			Iterator<OutgoingCallTransition<LETTER, STATE>> it = 
					m_Operand.callSuccessors(state, letter).iterator();
			if (it.hasNext()) {
				it.next();
				if (it.hasNext()) {
					m_NondeterminismInInputDetected = true;
					return new HashSet<OutgoingCallTransition<LETTER, STATE>>(0);
				} else {
					return m_Operand.callSuccessors(state, letter);
				}
			}
		}
		OutgoingCallTransition<LETTER, STATE> trans = 
				new OutgoingCallTransition<LETTER, STATE>(letter, m_SinkState);
		ArrayList<OutgoingCallTransition<LETTER, STATE>> result = 
				new ArrayList<OutgoingCallTransition<LETTER, STATE>>(1);
		result.add(trans);
		return result;
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			STATE state) {
		if (m_NondeterminismInInputDetected) {
			return new HashSet<OutgoingCallTransition<LETTER, STATE>>(0);
		}
		ArrayList<OutgoingCallTransition<LETTER, STATE>> result = 
				new ArrayList<OutgoingCallTransition<LETTER, STATE>>();
		for (LETTER letter : getCallAlphabet()) {
			Iterator<OutgoingCallTransition<LETTER, STATE>> it = 
					callSuccessors(state, letter).iterator();
			if (m_NondeterminismInInputDetected) {
				return new HashSet<OutgoingCallTransition<LETTER, STATE>>(0);
			}
			result.add(it.next());
			assert !it.hasNext();
		}
		return result;
	}



	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSucccessors(
			STATE state, STATE hier, LETTER letter) {
		if (m_NondeterminismInInputDetected) {
			return new HashSet<OutgoingReturnTransition<LETTER, STATE>>(0);
		}
		if (state != m_SinkState) {
			Iterator<OutgoingReturnTransition<LETTER, STATE>> it = 
					m_Operand.returnSucccessors(state, hier, letter).iterator();
			if (it.hasNext()) {
				it.next();
				if (it.hasNext()) {
					m_NondeterminismInInputDetected = true;
					return new HashSet<OutgoingReturnTransition<LETTER, STATE>>(0);
				} else {
					return m_Operand.returnSucccessors(state, hier, letter);
				}
			}
		}
		OutgoingReturnTransition<LETTER, STATE> trans = 
				new OutgoingReturnTransition<LETTER, STATE>(hier, letter, m_SinkState);
		ArrayList<OutgoingReturnTransition<LETTER, STATE>> result = 
				new ArrayList<OutgoingReturnTransition<LETTER, STATE>>(1);
		result.add(trans);
		return result;
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(
			STATE state, STATE hier) {
		if (m_NondeterminismInInputDetected) {
			return new HashSet<OutgoingReturnTransition<LETTER, STATE>>(0);
		}
		ArrayList<OutgoingReturnTransition<LETTER, STATE>> result = 
				new ArrayList<OutgoingReturnTransition<LETTER, STATE>>();
		for (LETTER letter : getReturnAlphabet()) {
			Iterator<OutgoingReturnTransition<LETTER, STATE>> it = 
					returnSucccessors(state, hier, letter).iterator();
			if (m_NondeterminismInInputDetected) {
				return new HashSet<OutgoingReturnTransition<LETTER, STATE>>(0);
			}
			result.add(it.next());
			assert !it.hasNext();
		}
		return result;
	}

	@Override
	public int size() {
		throw new UnsupportedOperationException();
	}

	@Override
	public Set<LETTER> getAlphabet() {
		throw new UnsupportedOperationException();	}

	@Override
	public String sizeInformation() {
		return "size Information not available";
	}


}
