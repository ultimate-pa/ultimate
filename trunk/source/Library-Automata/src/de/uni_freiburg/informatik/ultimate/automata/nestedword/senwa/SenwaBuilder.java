/*
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.senwa;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEquivalent;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.senwa.SenwaWalker.ISuccessorVisitor;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.ISenwaStateFactory;

/**
 * Builder for a {@link Senwa}.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public final class SenwaBuilder<LETTER, STATE> extends
		UnaryNwaOperation<LETTER, STATE, INwaInclusionStateFactory<STATE>> implements ISuccessorVisitor<LETTER, STATE> {
	private final ISenwaStateFactory<STATE> mStateFactory;
	private final Senwa<LETTER, STATE> mSenwa;
	// TODO Christian 2016-09-18: Can be made INestedWordAutomatonSimple when guarding assertions.
	private final INestedWordAutomaton<LETTER, STATE> mNwa;
	// private final Set<STATE> mAdded = new HashSet<>();

	private final Map<STATE, STATE> mResult2Operand = new HashMap<>();
	private final Map<STATE, Map<STATE, STATE>> mEntry2Operand2Result = new HashMap<>();

	/**
	 * Constructor.
	 *
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param nwa
	 *            nested word automaton
	 * @throws AutomataOperationCanceledException
	 *             if timeout exceeds
	 */
	public SenwaBuilder(final AutomataLibraryServices services, final ISenwaStateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> nwa) throws AutomataOperationCanceledException {
		super(services);
		mStateFactory = stateFactory;
		mNwa = nwa;
		mLogger.info(startMessage());
		mSenwa = new Senwa<>(mServices, mNwa.getVpAlphabet(),
				stateFactory);
		new SenwaWalker<>(mServices, mSenwa, this, true);
		mLogger.info(exitMessage());
	}

	@Override
	public String exitMessage() {
		return "Finished " + getOperationName() + ". Result " + mSenwa.sizeInformation();
	}

	private STATE getOrConstructResultState(final STATE opEntry, final STATE opState, final boolean isInitial) {
		assert mNwa.getStates().contains(opState);
		assert mNwa.getStates().contains(opEntry);
		Map<STATE, STATE> op2res = mEntry2Operand2Result.get(opEntry);
		if (op2res == null) {
			op2res = new HashMap<>();
			mEntry2Operand2Result.put(opEntry, op2res);
		}
		STATE resState = op2res.get(opState);
		if (resState == null) {
			resState = mStateFactory.senwa(opEntry, opState);
			op2res.put(opState, resState);
			mResult2Operand.put(resState, opState);
			final STATE resEntry = op2res.get(opEntry);
			assert resEntry != null;
			mSenwa.addState(resState, isInitial, mNwa.isFinal(opState), resEntry);
		}
		return resState;
	}

	private STATE getOperandState(final STATE resState) {
		assert mSenwa.getStates().contains(resState);
		final STATE opState = mResult2Operand.get(resState);
		assert opState != null;
		return opState;
	}

	@Override
	public Iterable<STATE> getInitialStates() {
		final Set<STATE> resInits = new HashSet<>();
		for (final STATE opState : mNwa.getInitialStates()) {
			final STATE resState = getOrConstructResultState(opState, opState, true);
			resInits.add(resState);
		}
		return resInits;
	}

	@Override
	public Iterable<STATE> visitAndGetInternalSuccessors(final STATE resState) {
		final STATE resEntry = mSenwa.getEntry(resState);
		final STATE opEntry = getOperandState(resEntry);
		final Set<STATE> resSuccs = new HashSet<>();
		final STATE opState = getOperandState(resState);
		for (final LETTER letter : mNwa.lettersInternal(opState)) {
			for (final OutgoingInternalTransition<LETTER, STATE> trans : mNwa.internalSuccessors(opState, letter)) {
				final STATE opSucc = trans.getSucc();
				final STATE resSucc = getOrConstructResultState(opEntry, opSucc, false);
				resSuccs.add(resSucc);
				mSenwa.addInternalTransition(resState, letter, resSucc);
			}
		}
		return resSuccs;
	}

	@Override
	public Iterable<STATE> visitAndGetCallSuccessors(final STATE resState) {
		final Set<STATE> resSuccs = new HashSet<>();
		final STATE opState = getOperandState(resState);
		for (final LETTER letter : mNwa.lettersCall(opState)) {
			for (final OutgoingCallTransition<LETTER, STATE> trans : mNwa.callSuccessors(opState, letter)) {
				final STATE opSucc = trans.getSucc();
				final STATE resSucc = getOrConstructResultState(opSucc, opSucc, false);
				resSuccs.add(resSucc);
				mSenwa.addCallTransition(resState, letter, resSucc);
			}
		}
		return resSuccs;
	}

	@Override
	public Iterable<STATE> visitAndGetReturnSuccessors(final STATE resState, final STATE resHier) {
		final STATE opState = getOperandState(resState);
		final STATE opHier = getOperandState(resHier);
		final STATE resHierEntry = mSenwa.getEntry(resHier);
		final STATE opHierEntry = getOperandState(resHierEntry);
		final Set<STATE> resSuccs = new HashSet<>();
		for (final OutgoingReturnTransition<LETTER, STATE> trans : mNwa.returnSuccessorsGivenHier(opState, opHier)) {
			final STATE opSucc = trans.getSucc();
			final STATE resSucc = getOrConstructResultState(opHierEntry, opSucc, false);
			resSuccs.add(resSucc);
			mSenwa.addReturnTransition(resState, resHier, trans.getLetter(), resSucc);
		}
		return resSuccs;
	}

	@Override
	protected INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getOperand() {
		return mNwa;
	}

	@Override
	public Senwa<LETTER, STATE> getResult() {
		return mSenwa;
	}

	@Override
	public boolean checkResult(final INwaInclusionStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Start testing correctness of " + getOperationName());
		}

		boolean correct;
		correct = new IsEquivalent<>(mServices, stateFactory, mNwa, mSenwa).getResult();
		if (!correct) {
			AutomatonDefinitionPrinter.writeToFileIfPreferred(mServices, getOperationName() + "Failed", "", mNwa);
		}

		if (mLogger.isInfoEnabled()) {
			mLogger.info("Finished testing correctness of " + getOperationName());
		}
		return correct;
	}
}
