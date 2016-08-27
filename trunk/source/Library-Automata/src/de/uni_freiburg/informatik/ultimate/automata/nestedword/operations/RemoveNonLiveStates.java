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

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.DoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomatonFilteredStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiAccepts;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiIsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.ReachableStatesCopy;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

public class RemoveNonLiveStates<LETTER, STATE>
		extends UnaryNwaOperation<LETTER, STATE>
		implements IOperation<LETTER, STATE> {
		
	private final NestedWordAutomatonReachableStates<LETTER, STATE> mReach;
	private final INestedWordAutomaton<LETTER, STATE> mResult;
	
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
	public RemoveNonLiveStates(final AutomataLibraryServices services,
			final INestedWordAutomatonSimple<LETTER, STATE> operand)
					throws AutomataOperationCanceledException {
		super(services, operand);
		mLogger.info(startMessage());
		mReach = new NestedWordAutomatonReachableStates<LETTER, STATE>(
				mServices, mOperand);
		mReach.computeNonLiveStates();
		mResult = new NestedWordAutomatonFilteredStates<LETTER, STATE>(
				mServices, mReach, mReach.getOnlyLiveStates());
		mLogger.info(exitMessage());
//		assert (new TransitionConsitenceCheck<LETTER, STATE>(mResult)).consistentForAll();
	}
	
	@Override
	public String operationName() {
		return "removeNonLiveStates";
	}
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Reduced from "
				+ mOperand.sizeInformation() + " to "
				+ mResult.sizeInformation();
	}
	
	@Override
	public INestedWordAutomaton<LETTER, STATE> getResult() {
		return mResult;
	}
	
	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
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
		rsc.removeNonLiveStates();
		final DoubleDeckerAutomaton<LETTER, STATE> reachableStatesCopy =
				(DoubleDeckerAutomaton<LETTER, STATE>) rsc.getResult();
//		correct &= mResult.getStates().isEmpty() ||
		ResultChecker.isSubset(reachableStatesCopy.getStates(), mResult.getStates());
//		assert correct;
		correct &= ResultChecker.isSubset(mResult.getStates(), reachableStatesCopy.getStates());
		assert correct;
		final Collection<STATE> rsaStates = mResult.getStates();
		final Collection<STATE> rscStates = reachableStatesCopy.getStates();
		correct &= ResultChecker.isSubset(rsaStates, rscStates);
		assert correct;
		// does not hold. Old non-live removal has bugs, see 'removeNonLive-Bug05.ats' example
//		correct &= ResultChecker.isSubset(rscStates,rsaStates);
//		assert correct;
		for (final STATE state : mResult.getStates()) {
			for (final OutgoingInternalTransition<LETTER, STATE> outTrans : reachableStatesCopy
					.internalSuccessors(state)) {
				correct &= mReach.containsInternalTransition(state, outTrans.getLetter(), outTrans.getSucc());
				assert correct;
			}
			for (final OutgoingCallTransition<LETTER, STATE> outTrans : reachableStatesCopy.callSuccessors(state)) {
				correct &= mReach.containsCallTransition(state, outTrans.getLetter(), outTrans.getSucc());
				assert correct;
			}
			for (final OutgoingReturnTransition<LETTER, STATE> outTrans : reachableStatesCopy.returnSuccessors(state)) {
				correct &= mReach.containsReturnTransition(state, outTrans.getHierPred(), outTrans.getLetter(),
						outTrans.getSucc());
				assert correct;
			}
			for (final OutgoingInternalTransition<LETTER, STATE> outTrans : mResult.internalSuccessors(state)) {
				correct &=
						reachableStatesCopy.containsInternalTransition(state, outTrans.getLetter(), outTrans.getSucc());
				assert correct;
			}
			for (final OutgoingCallTransition<LETTER, STATE> outTrans : mResult.callSuccessors(state)) {
				correct &= reachableStatesCopy.containsCallTransition(state, outTrans.getLetter(), outTrans.getSucc());
				assert correct;
			}
			for (final OutgoingReturnTransition<LETTER, STATE> outTrans : mResult.returnSuccessors(state)) {
				correct &= reachableStatesCopy.containsReturnTransition(
						state, outTrans.getHierPred(), outTrans.getLetter(), outTrans.getSucc());
				assert correct;
			}
			final Set<STATE> rCSdownStates = reachableStatesCopy.getDownStates(state);
			final Set<STATE> rCAdownStates = mReach.getOnlyLiveStates().getDownStates(state);
			correct &= ResultChecker.isSubset(rCAdownStates, rCSdownStates);
			assert correct;
			// After enhanced non-live/dead end removal the following does not
			// hold.
			// correct &= ResultChecker.isSubset(rCSdownStates, rCAdownStates);
			assert correct;
		}
		
		final List<NestedLassoWord<LETTER>> lassoWords = new ArrayList<NestedLassoWord<LETTER>>();
		final BuchiIsEmpty<LETTER, STATE> operandEmptiness =
				new BuchiIsEmpty<LETTER, STATE>(mServices, mOperand);
		final boolean operandEmpty = operandEmptiness.getResult();
		if (!operandEmpty) {
			lassoWords.add(operandEmptiness.getAcceptingNestedLassoRun().getNestedLassoWord());
		}
		final BuchiIsEmpty<LETTER, STATE> resultEmptiness = new BuchiIsEmpty<LETTER, STATE>(mServices, mResult);
		final boolean resultEmpty = resultEmptiness.getResult();
		if (!resultEmpty) {
			lassoWords.add(resultEmptiness.getAcceptingNestedLassoRun().getNestedLassoWord());
		}
		correct &= (operandEmpty == resultEmpty);
		assert correct;
		final int numberLassoWords = 10;
		for (int i = 0; i < numberLassoWords; i++) {
			lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, mResult.size()));
			lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, mOperand.size()));
		}
		
		for (final NestedLassoWord<LETTER> nlw : lassoWords) {
			correct &= checkAcceptance(nlw, mOperand);
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
	
	private boolean checkAcceptance(final NestedLassoWord<LETTER> nlw,
			final INestedWordAutomatonSimple<LETTER, STATE> operand)
					throws AutomataLibraryException {
		final boolean op =
				(new BuchiAccepts<LETTER, STATE>(mServices, operand, nlw)).getResult();
		final boolean res =
				(new BuchiAccepts<LETTER, STATE>(mServices, mResult, nlw)).getResult();
		final boolean correct = (op == res);
		assert correct : operationName() + " wrong result!";
		return correct;
	}
}
