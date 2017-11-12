/*
 * Copyright (C) 2014-2015 Yong Li (liyong@ios.ac.cn)
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.inclusion;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;

import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IGeneralizedNestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoRun;


import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;


/**
 * A generalized nested word automaton with reachable states information.
 * For now, we only support generalized word automata.
 *
 * @author Yong Li (liyong@ios.ac.cn)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public abstract class AbstractGeneralizedAutomatonReachableStates<LETTER, STATE> implements IGeneralizedNestedWordAutomaton<LETTER, STATE>
                                  , IDoubleDeckerAutomaton<LETTER, STATE> {

	
	protected abstract StateContainer<LETTER, STATE> getStateContainer(STATE state);
	
	public abstract Boolean isEmpty();
	
	protected NestedLassoRun<LETTER, STATE> mLasso = null;
	
	public abstract NestedLassoRun<LETTER, STATE> getNestedLassoRun() throws AutomataOperationCanceledException;
	
	protected final Set<LETTER> mEmptyLetterSet = new HashSet<>();
	protected final Set<STATE> mDownStates = new HashSet<>();
	protected final Set<STATE> mInitialStates = new HashSet<>();
	protected final Set<STATE> mFinalStates = new HashSet<>();
	
	protected final AutomataLibraryServices mServices;
	protected final ILogger mLogger;
	
	protected final VpAlphabet<LETTER> mVpAlphabet;
	
	protected int mNumberOfConstructedStates;
	
	public AbstractGeneralizedAutomatonReachableStates(final AutomataLibraryServices services, final VpAlphabet<LETTER> vpAlphabet) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mVpAlphabet = vpAlphabet;
	}
	
	protected void removeStates(STATE state) {
		
	}

	@Override
	public boolean isDoubleDecker(STATE upState, STATE downState) {
		return mDownStates.contains(downState);
	}

	@Override
	public Set<STATE> getDownStates(STATE upState) {
		return Collections.unmodifiableSet(mDownStates);
	}
	
	@Override
	public Set<STATE> getInitialStates() {
		return Collections.unmodifiableSet(mInitialStates);
	}

	@Override
	public Collection<STATE> getFinalStates() {
		return Collections.unmodifiableSet(mFinalStates);
	}
	

	@Override
	public Set<LETTER> getAlphabet() {
		return mVpAlphabet.getInternalAlphabet();
	}
	

	@Override
	public VpAlphabet<LETTER> getVpAlphabet() {
		return mVpAlphabet;
	}
	
	// ---------------------------------------------------------------------
	@Override
	public Set<LETTER> lettersReturn(STATE state) {
		return mEmptyLetterSet;
	}

	@Override
	public Set<LETTER> lettersCallIncoming(STATE state) {
		return mEmptyLetterSet;
	}

	@Override
	public Set<LETTER> lettersReturnIncoming(STATE state) {
		return mEmptyLetterSet;
	}

	@Override
	public Set<LETTER> lettersSummary(STATE state) {
		return mEmptyLetterSet;
	}
	
	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(STATE state, LETTER letter) {
		return () -> new Iterator<OutgoingCallTransition<LETTER, STATE>>() {
			@Override
			public boolean hasNext() {
				return false;
			}

			@Override
			public OutgoingCallTransition<LETTER, STATE> next() {
				return null;
			}
		};
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(STATE state, STATE hier, LETTER letter) {
		return returnSuccessors(state);
	}

	@Override
	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(STATE succ, LETTER letter) {
		return callPredecessors(succ);
	}

	@Override
	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(STATE succ) {
		return () -> new Iterator<IncomingCallTransition<LETTER, STATE>>() {
			@Override
			public boolean hasNext() {
				return false;
			}

			@Override
			public IncomingCallTransition<LETTER, STATE> next() {
				return null;
			}
		};
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(STATE succ, STATE hier, LETTER letter) {
		return returnPredecessors(succ);
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(STATE succ, LETTER letter) {
		return returnPredecessors(succ);
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(STATE succ) {
		return () -> new Iterator<IncomingReturnTransition<LETTER, STATE>>() {
			@Override
			public boolean hasNext() {
				return false;
			}

			@Override
			public IncomingReturnTransition<LETTER, STATE> next() {
				return null;
			}
		};
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(STATE state) {
		return () -> new Iterator<OutgoingReturnTransition<LETTER, STATE>>() {
			@Override
			public boolean hasNext() {
				return false;
			}

			@Override
			public OutgoingReturnTransition<LETTER, STATE> next() {
				return null;
			}
		};
	}

	@Override
	public Iterable<SummaryReturnTransition<LETTER, STATE>> summarySuccessors(STATE hier, LETTER letter) {
		return summarySuccessors(hier);
	}

	@Override
	public Iterable<SummaryReturnTransition<LETTER, STATE>> summarySuccessors(STATE hier) {
		return () -> new Iterator<SummaryReturnTransition<LETTER, STATE>>() {
			@Override
			public boolean hasNext() {
				return false;
			}

			@Override
			public SummaryReturnTransition<LETTER, STATE> next() {
				return null;
			}
		};
	}
	


}
