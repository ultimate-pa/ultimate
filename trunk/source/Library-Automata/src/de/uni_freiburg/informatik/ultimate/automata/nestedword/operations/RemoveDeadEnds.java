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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations;

import java.util.Collection;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.DoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomatonFilteredStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.TransitionConsistencyCheck;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.ReachableStatesCopy;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

public class RemoveDeadEnds<LETTER, STATE>
		extends UnaryNwaOperation<LETTER, STATE>
		implements IOperation<LETTER, STATE> {
	private final INestedWordAutomatonSimple<LETTER, STATE> mOperand;
	private final NestedWordAutomatonReachableStates<LETTER, STATE> mReach;
	private final IDoubleDeckerAutomaton<LETTER, STATE> mResult;
	
	/**
	 * Given an INestedWordAutomaton nwa return a nested word automaton that has
	 * the same states, but all states that are not reachable or dead ends are
	 * omitted. (A dead end is a state from which no accepting state can be
	 * reached).
	 * Each state of the result also occurred in the input. Only the auxiliary
	 * empty stack state of the result is different.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            operand
	 * @throws AutomataOperationCanceledException
	 *             if timeout exceeds
	 */
	public RemoveDeadEnds(final AutomataLibraryServices services,
			final INestedWordAutomatonSimple<LETTER, STATE> operand)
					throws AutomataOperationCanceledException {
		super(services);
		mOperand = operand;
		mLogger.info(startMessage());
		try {
			mReach = new NestedWordAutomatonReachableStates<LETTER, STATE>(
					mServices, mOperand);
			mReach.computeDeadEnds();
			mResult = new NestedWordAutomatonFilteredStates<LETTER, STATE>(
					mServices, mReach, mReach.getWithOutDeadEnds());
		} catch (final AutomataOperationCanceledException oce) {
			throw new AutomataOperationCanceledException(getClass());
		}
		mLogger.info(exitMessage());
		assert (new TransitionConsistencyCheck<LETTER, STATE>(mResult)).consistentForAll();
	}
	
	@Override
	public String operationName() {
		return "removeDeadEnds";
	}
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Reduced from "
				+ mOperand.sizeInformation() + " to "
				+ mResult.sizeInformation();
	}

	@Override
	protected INestedWordAutomatonSimple<LETTER, STATE> getOperand() {
		return mOperand;
	}
	
	@Override
	public IDoubleDeckerAutomaton<LETTER, STATE> getResult() {
		return mResult;
	}
	
	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataOperationCanceledException {
		mLogger.info("Start testing correctness of " + operationName());
		boolean correct = true;
//		correct &= (ResultChecker.nwaLanguageInclusion(mInput, mResult) == null);
//		correct &= (ResultChecker.nwaLanguageInclusion(mResult, mInput) == null);
		assert correct;
		INestedWordAutomaton<LETTER, STATE> input;
		if (mOperand instanceof INestedWordAutomaton) {
			input = (INestedWordAutomaton<LETTER, STATE>) mOperand;
		} else {
			input = (new RemoveUnreachable<LETTER, STATE>(mServices, mOperand)).getResult();
		}
		final ReachableStatesCopy<LETTER, STATE> rsc =
				(new ReachableStatesCopy<LETTER, STATE>(mServices, input, false, false, false, false));
//		Set<UpDownEntry<STATE>> rsaEntries = new HashSet<UpDownEntry<STATE>>();
//		for (UpDownEntry<STATE> rde : mReach.getRemovedUpDownEntry()) {
//			rsaEntries.add(rde);
//		}
//		Set<UpDownEntry<STATE>> rscEntries = new HashSet<UpDownEntry<STATE>>();
//		for (UpDownEntry<STATE> rde : rsc.getRemovedUpDownEntry()) {
//			rscEntries.add(rde);
//		}
//		correct &= ResultChecker.isSubset(rsaEntries,rscEntries);
//		assert correct;
//		correct &= ResultChecker.isSubset(rscEntries,rsaEntries);
//		assert correct;
		rsc.removeDeadEnds();
		final DoubleDeckerAutomaton<LETTER, STATE> reachalbeStatesCopy =
				(DoubleDeckerAutomaton<LETTER, STATE>) rsc.getResult();
		correct &= mResult.getStates().isEmpty()
				|| ResultChecker.isSubset(reachalbeStatesCopy.getStates(), mResult.getStates());
		assert correct;
		correct &= ResultChecker.isSubset(mResult.getStates(), reachalbeStatesCopy.getStates());
		assert correct;
		final Collection<STATE> rsaStates = mResult.getStates();
		final Collection<STATE> rscStates = reachalbeStatesCopy.getStates();
		correct &= ResultChecker.isSubset(rsaStates, rscStates);
		assert correct;
		correct &= ResultChecker.isSubset(rscStates, rsaStates);
		assert correct;
		for (final STATE state : reachalbeStatesCopy.getStates()) {
			for (final OutgoingInternalTransition<LETTER, STATE> outTrans : reachalbeStatesCopy
					.internalSuccessors(state)) {
				correct &= mReach.containsInternalTransition(state, outTrans.getLetter(), outTrans.getSucc());
				assert correct;
			}
			for (final OutgoingCallTransition<LETTER, STATE> outTrans : reachalbeStatesCopy.callSuccessors(state)) {
				// TODO: fix or remove
				correct &= mReach.containsCallTransition(state, outTrans.getLetter(), outTrans.getSucc());
				// ignore call transitions
				assert correct;
			}
			for (final OutgoingReturnTransition<LETTER, STATE> outTrans : reachalbeStatesCopy.returnSuccessors(state)) {
				correct &= mReach.containsReturnTransition(state, outTrans.getHierPred(), outTrans.getLetter(),
						outTrans.getSucc());
				assert correct;
			}
			for (final OutgoingInternalTransition<LETTER, STATE> outTrans : mResult.internalSuccessors(state)) {
				correct &=
						reachalbeStatesCopy.containsInternalTransition(state, outTrans.getLetter(), outTrans.getSucc());
				assert correct;
			}
			for (final OutgoingCallTransition<LETTER, STATE> outTrans : mResult.callSuccessors(state)) {
				correct &= reachalbeStatesCopy.containsCallTransition(state,
						outTrans.getLetter(), outTrans.getSucc());
				assert correct;
			}
			for (final OutgoingReturnTransition<LETTER, STATE> outTrans : mResult.returnSuccessors(state)) {
				correct &= reachalbeStatesCopy.containsReturnTransition(state,
						outTrans.getHierPred(), outTrans.getLetter(), outTrans.getSucc());
				assert correct;
			}
			final Set<STATE> rCSdownStates = reachalbeStatesCopy.getDownStates(state);
			final Set<STATE> rCAdownStates =
					mReach.getWithOutDeadEnds().getDownStates(state);
			correct &= ResultChecker.isSubset(rCAdownStates, rCSdownStates);
			assert correct;
			// After enhanced non-live/dead end removal the following does not
			// hold.
//			 correct &= ResultChecker.isSubset(rCSdownStates, rCAdownStates);
			assert correct;
		}
		if (!correct) {
			AutomatonDefinitionPrinter.writeToFileIfPreferred(mServices,
					operationName() + "Failed", "language is different",
					mOperand);
		}
		mLogger.info("Finished testing correctness of " + operationName());
		return correct;
	}
}
