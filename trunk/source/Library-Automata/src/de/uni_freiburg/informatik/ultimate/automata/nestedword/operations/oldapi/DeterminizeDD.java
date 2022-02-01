/*
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsDeterministic;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEquivalent;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IDeterminizeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;

/**
 * Determinizes a nested word automaton.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class DeterminizeDD<LETTER, STATE> extends DoubleDeckerBuilder<LETTER, STATE>
		implements IOperation<LETTER, STATE, INwaInclusionStateFactory<STATE>> {
	protected INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mOperand;
	protected IStateDeterminizer<LETTER, STATE> mStateDeterminizer;

	/**
	 * Maps a DeterminizedState to its representative in the resulting automaton.
	 */
	protected Map<DeterminizedState<LETTER, STATE>, STATE> mDet2res = new HashMap<>();

	/**
	 * Maps a state in resulting automaton to the DeterminizedState for which it was created.
	 */
	protected final Map<STATE, DeterminizedState<LETTER, STATE>> mRes2det = new HashMap<>();

	/**
	 * Constructor which uses a {@link PowersetDeterminizer}.
	 *
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            operand
	 * @param stateFactory
	 *            state factory used in the state determinizer
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public DeterminizeDD(final AutomataLibraryServices services, final IDeterminizeStateFactory<STATE> stateFactory,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand) throws AutomataOperationCanceledException {
		this(services, stateFactory, operand, new PowersetDeterminizer<>(operand, true, stateFactory));
	}

	/**
	 * Constructor.
	 *
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            operand
	 * @param stateDeterminizer
	 *            state determinizer
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public DeterminizeDD(final AutomataLibraryServices services,
			final IEmptyStackStateFactory<STATE> emptyStackFactory,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand,
			final IStateDeterminizer<LETTER, STATE> stateDeterminizer) throws AutomataOperationCanceledException {
		super(services);
		mOperand = operand;
		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}

		mStateDeterminizer = stateDeterminizer;
		super.mTraversedNwa = new NestedWordAutomaton<>(mServices, operand.getVpAlphabet(), emptyStackFactory);
		mRemoveDeadEnds = false;
		traverseDoubleDeckerGraph();
		assert new IsDeterministic<>(mServices, mTraversedNwa).getResult();

		if (mLogger.isInfoEnabled()) {
			mLogger.debug(exitMessage());
		}
	}

	@Override
	public final String startMessage() {
		return "Start " + getOperationName() + ". Operand " + mOperand.sizeInformation();
	}

	@Override
	public final String exitMessage() {
		return "Finished " + getOperationName() + ". Result " + mTraversedNwa.sizeInformation();
	}

	@Override
	protected Collection<STATE> getInitialStates() {
		// final ArrayList<STATE> resInitials = new ArrayList<>(mOperand.getInitialStates().size());
		final ArrayList<STATE> resInitials = new ArrayList<>();
		final DeterminizedState<LETTER, STATE> detState = mStateDeterminizer.initialState();
		final STATE resState = mStateDeterminizer.getState(detState);
		((NestedWordAutomaton<LETTER, STATE>) mTraversedNwa).addState(true, detState.containsFinal(), resState);
		mDet2res.put(detState, resState);
		mRes2det.put(resState, detState);
		resInitials.add(resState);

		return resInitials;
	}

	@Override
	protected Collection<STATE> buildInternalSuccessors(final DoubleDecker<STATE> doubleDecker) {
		final List<STATE> resInternalSuccessors = new LinkedList<>();
		final STATE resState = doubleDecker.getUp();

		final DeterminizedState<LETTER, STATE> detState = mRes2det.get(resState);

		for (final LETTER symbol : mOperand.getVpAlphabet().getInternalAlphabet()) {
			final DeterminizedState<LETTER, STATE> detSucc = mStateDeterminizer.internalSuccessor(detState, symbol);
			final STATE resSucc = getResState(detSucc);
			((NestedWordAutomaton<LETTER, STATE>) mTraversedNwa).addInternalTransition(resState, symbol, resSucc);
			resInternalSuccessors.add(resSucc);
		}
		return resInternalSuccessors;
	}

	@Override
	protected Collection<STATE> buildCallSuccessors(final DoubleDecker<STATE> doubleDecker) {
		final List<STATE> resCallSuccessors = new LinkedList<>();
		final STATE resState = doubleDecker.getUp();

		final DeterminizedState<LETTER, STATE> detState = mRes2det.get(resState);

		for (final LETTER symbol : mOperand.getVpAlphabet().getCallAlphabet()) {
			final DeterminizedState<LETTER, STATE> detSucc = mStateDeterminizer.callSuccessor(detState, symbol);
			final STATE resSucc = getResState(detSucc);
			((NestedWordAutomaton<LETTER, STATE>) mTraversedNwa).addCallTransition(resState, symbol, resSucc);
			resCallSuccessors.add(resSucc);
		}
		return resCallSuccessors;
	}

	@Override
	@SuppressWarnings("squid:S1698")
	protected Collection<STATE> buildReturnSuccessors(final DoubleDecker<STATE> doubleDecker) {
		final List<STATE> resReturnSuccessors = new LinkedList<>();
		final STATE resLinPred = doubleDecker.getDown();
		// equality intended here
		if (resLinPred == mTraversedNwa.getEmptyStackState()) {
			return resReturnSuccessors;
		}

		final STATE resState = doubleDecker.getUp();
		final DeterminizedState<LETTER, STATE> detLinPred = mRes2det.get(resLinPred);
		final DeterminizedState<LETTER, STATE> detState = mRes2det.get(resState);
		for (final LETTER symbol : mOperand.getVpAlphabet().getReturnAlphabet()) {
			final DeterminizedState<LETTER, STATE> detSucc =
					mStateDeterminizer.returnSuccessor(detState, detLinPred, symbol);
			final STATE resSucc = getResState(detSucc);
			((NestedWordAutomaton<LETTER, STATE>) mTraversedNwa).addReturnTransition(resState, resLinPred, symbol,
					resSucc);
			resReturnSuccessors.add(resSucc);
		}
		return resReturnSuccessors;
	}

	/**
	 * Get the state in the resulting automaton that represents a DeterminizedState. If this state in the resulting
	 * automaton does not exist yet, construct it.
	 */
	protected STATE getResState(final DeterminizedState<LETTER, STATE> detState) {
		if (mDet2res.containsKey(detState)) {
			return mDet2res.get(detState);
		}
		final STATE resState = mStateDeterminizer.getState(detState);
		((NestedWordAutomaton<LETTER, STATE>) mTraversedNwa).addState(false, detState.containsFinal(), resState);
		mDet2res.put(detState, resState);
		mRes2det.put(resState, detState);
		return resState;
	}

	@Override
	public boolean checkResult(final INwaInclusionStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		boolean correct = true;
		if (mStateDeterminizer instanceof PowersetDeterminizer) {
			mLogger.info("Testing correctness of determinization");
			final INestedWordAutomaton<LETTER, STATE> operandOld =
					(new RemoveUnreachable<>(mServices, mOperand)).getResult();
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> resultSadd =
					(new DeterminizeSadd<>(mServices, stateFactory, operandOld)).getResult();
			correct &= new IsEquivalent<>(mServices, stateFactory, resultSadd, mTraversedNwa).getResult();
			mLogger.info("Finished testing correctness of determinization");
		}
		return correct;
	}
}
