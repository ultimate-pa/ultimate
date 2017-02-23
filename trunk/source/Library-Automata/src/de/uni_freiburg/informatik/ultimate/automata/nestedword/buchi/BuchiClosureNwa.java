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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi;

import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Represents complement of deterministic and total nested word automaton.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public final class BuchiClosureNwa<LETTER, STATE> implements IDoubleDeckerAutomaton<LETTER, STATE> {
	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;

	private final INestedWordAutomaton<LETTER, STATE> mOperand;
	private final Set<STATE> mAcceptingStates;

	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            operand
	 */
	public BuchiClosureNwa(final AutomataLibraryServices services, final INestedWordAutomaton<LETTER, STATE> operand) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mOperand = operand;
		mAcceptingStates = computeSetOfAcceptingStates();
	}

	/**
	 * Maximizes the set of accepting states.
	 * 
	 * @return maximal set
	 */
	public Set<STATE> computeSetOfAcceptingStates() {
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Accepting states before buchiClosure: " + mOperand.getFinalStates().size());
		}

		final Set<STATE> newFinalStates = new HashSet<>();
		final LinkedHashSet<STATE> worklist = new LinkedHashSet<>();
		newFinalStates.addAll(mOperand.getFinalStates());
		for (final STATE fin : mOperand.getFinalStates()) {
			addAllNonFinalPredecessors(fin, worklist, newFinalStates);
		}
		while (!worklist.isEmpty()) {
			final STATE state = worklist.iterator().next();
			worklist.remove(state);
			assert !newFinalStates.contains(state);
			if (allSuccessorsAccepting(state, newFinalStates)) {
				newFinalStates.add(state);
				addAllNonFinalPredecessors(state, worklist, newFinalStates);
			}
		}
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Accepting states after buchiClosure: " + newFinalStates.size());
		}
		return newFinalStates;
	}

	/**
	 * Add all predecessors of state that are not in the set newFinalStates
	 * to worklist.
	 */
	private void addAllNonFinalPredecessors(final STATE state, final Set<STATE> worklist,
			final Set<STATE> newFinalStates) {
		for (final IncomingInternalTransition<LETTER, STATE> inTrans : mOperand.internalPredecessors(state)) {
			if (!newFinalStates.contains(inTrans.getPred())) {
				worklist.add(inTrans.getPred());
			}
		}
		for (final IncomingCallTransition<LETTER, STATE> inTrans : mOperand.callPredecessors(state)) {
			if (!newFinalStates.contains(inTrans.getPred())) {
				worklist.add(inTrans.getPred());
			}
		}
		for (final IncomingReturnTransition<LETTER, STATE> inTrans : mOperand.returnPredecessors(state)) {
			if (!newFinalStates.contains(inTrans.getLinPred())) {
				worklist.add(inTrans.getLinPred());
			}
		}
	}

	/**
	 * Return true iff all successors of state state is the set newFinalStates.
	 */
	private boolean allSuccessorsAccepting(final STATE state, final Set<STATE> newFinalStates) {
		for (final OutgoingInternalTransition<LETTER, STATE> trans : mOperand.internalSuccessors(state)) {
			final STATE succ = trans.getSucc();
			if (!newFinalStates.contains(succ)) {
				return false;
			}
		}
		for (final OutgoingCallTransition<LETTER, STATE> trans : mOperand.callSuccessors(state)) {
			final STATE succ = trans.getSucc();
			if (!newFinalStates.contains(succ)) {
				return false;
			}
		}
		for (final OutgoingReturnTransition<LETTER, STATE> trans : mOperand.returnSuccessors(state)) {
			final STATE succ = trans.getSucc();
			if (!newFinalStates.contains(succ)) {
				return false;
			}
		}
		return true;
	}

	@Override
	public Set<STATE> getInitialStates() {
		return mOperand.getInitialStates();
	}

	@Override
	public Set<LETTER> getInternalAlphabet() {
		return mOperand.getInternalAlphabet();
	}

	@Override
	public Set<LETTER> getCallAlphabet() {
		return mOperand.getCallAlphabet();
	}

	@Override
	public Set<LETTER> getReturnAlphabet() {
		return mOperand.getReturnAlphabet();
	}

	@Override
	public IStateFactory<STATE> getStateFactory() {
		return mOperand.getStateFactory();
	}

	@Override
	public boolean isInitial(final STATE state) {
		return mOperand.isInitial(state);
	}

	@Override
	public boolean isFinal(final STATE state) {
		return mAcceptingStates.contains(state);
	}

	@Override
	public STATE getEmptyStackState() {
		return mOperand.getEmptyStackState();
	}

	@Override
	public Set<LETTER> lettersInternal(final STATE state) {
		return mOperand.lettersInternal(state);
	}

	@Override
	public Set<LETTER> lettersCall(final STATE state) {
		return mOperand.lettersCall(state);
	}

	@Override
	public Set<LETTER> lettersReturn(final STATE state) {
		return mOperand.lettersReturn(state);
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state,
			final LETTER letter) {
		return mOperand.internalSuccessors(state, letter);
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state) {
		return mOperand.internalSuccessors(state);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state, final LETTER letter) {
		return mOperand.callSuccessors(state, letter);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state) {
		return mOperand.callSuccessors(state);
	}

	@Override
	public int size() {
		return mOperand.size();
	}

	@Override
	public Set<LETTER> getAlphabet() {
		return mOperand.getAlphabet();
	}

	@Override
	public String sizeInformation() {
		return mOperand.sizeInformation();
	}

	@Override
	public Set<STATE> getStates() {
		return mOperand.getStates();
	}

	@Override
	public Iterable<STATE> hierarchicalPredecessorsOutgoing(final STATE state, final LETTER letter) {
		return mOperand.hierarchicalPredecessorsOutgoing(state, letter);
	}

	@Override
	public Collection<STATE> getFinalStates() {
		return mAcceptingStates;
	}

	@Override
	public Iterable<SummaryReturnTransition<LETTER, STATE>> summarySuccessors(final STATE hier, final LETTER letter) {
		return mOperand.summarySuccessors(hier, letter);
	}

	@Override
	public Iterable<SummaryReturnTransition<LETTER, STATE>> summarySuccessors(final STATE hier) {
		return mOperand.summarySuccessors(hier);
	}

	@Override
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(final STATE succ) {
		return mOperand.internalPredecessors(succ);
	}

	@Override
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(final STATE succ,
			final LETTER letter) {
		return mOperand.internalPredecessors(succ, letter);
	}

	@Override
	public Set<LETTER> lettersInternalIncoming(final STATE state) {
		return mOperand.lettersInternalIncoming(state);
	}

	@Override
	public Set<LETTER> lettersCallIncoming(final STATE state) {
		return mOperand.lettersCallIncoming(state);
	}

	@Override
	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(final STATE succ, final LETTER letter) {
		return mOperand.callPredecessors(succ, letter);
	}

	@Override
	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(final STATE succ) {
		return mOperand.callPredecessors(succ);
	}

	@Override
	public Set<LETTER> lettersReturnIncoming(final STATE state) {
		return mOperand.lettersReturnIncoming(state);
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(final STATE succ, final STATE hier,
			final LETTER letter) {
		return mOperand.returnPredecessors(succ, hier, letter);
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(final STATE succ, final LETTER letter) {
		return mOperand.returnPredecessors(succ, letter);
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(final STATE succ) {
		return mOperand.returnPredecessors(succ);
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final STATE state, final STATE hier,
			final LETTER letter) {
		return mOperand.returnSuccessors(state, hier, letter);
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final STATE state, final LETTER letter) {
		return mOperand.returnSuccessors(state, letter);
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final STATE state) {
		return mOperand.returnSuccessors(state);
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(final STATE state,
			final STATE hier) {
		return mOperand.returnSuccessorsGivenHier(state, hier);
	}

	@Override
	public Set<LETTER> lettersSummary(final STATE state) {
		return mOperand.lettersSummary(state);
	}

	@Override
	public boolean isDoubleDecker(final STATE upState, final STATE downState) {
		return ((IDoubleDeckerAutomaton<LETTER, STATE>) mOperand).isDoubleDecker(upState, downState);
	}

	/**
	 * {@inheritDoc}
	 * 
	 * @deprecated Use the {@link #isDoubleDecker(Object, Object)} check instead.
	 */
	@Override
	@Deprecated
	public Set<STATE> getDownStates(final STATE upState) {
		return ((IDoubleDeckerAutomaton<LETTER, STATE>) mOperand).getDownStates(upState);
	}
}
