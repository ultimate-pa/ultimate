package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.inclusion;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;

public class RemoveUnusedStates<LETTER, STATE> {

	private final AbstractGeneralizedAutomatonReachableStates<LETTER, STATE> mOperand;
	private final AutomataLibraryServices mServices;

	public RemoveUnusedStates(final AutomataLibraryServices services,
			final AbstractGeneralizedAutomatonReachableStates<LETTER, STATE> operand)
			throws AutomataOperationCanceledException {
		mServices = services;
		mOperand = operand;
		removeUnusedStates();
	}

	private void removeUnusedStates() throws AutomataOperationCanceledException {

		final Set<STATE> unusedStates = new HashSet<>(mOperand.getStates());
		final LinkedList<STATE> list = new LinkedList<>();
		final Set<STATE> visited = new HashSet<>();
		for (final STATE st : mOperand.mFinalStates) {
			list.addFirst(st);
		}
		while (!list.isEmpty()) {
			if (!mServices.getProgressAwareTimer().continueProcessing()) {
				final RunningTaskInfo rti = constructRunningTaskInfo();
				throw new AutomataOperationCanceledException(rti);
			}
			final STATE state = list.poll();
			visited.add(state);
			unusedStates.remove(state);
			final StateContainer<LETTER, STATE> cont = mOperand.getStateContainer(state);
			for (final IncomingInternalTransition<LETTER, STATE> trans : cont.internalPredecessors()) {
				if (!visited.contains(trans.getPred())) {
					list.addFirst(trans.getPred());
				}
			}
		}

		// remove all transitions for unused states
		for (final STATE st : unusedStates) {
			final StateContainer<LETTER, STATE> cont = mOperand.getStateContainer(st);
			final Set<STATE> pred = new HashSet<>();
			for (final IncomingInternalTransition<LETTER, STATE> trans : cont.internalPredecessors()) {
				if (!mServices.getProgressAwareTimer().continueProcessing()) {
					final RunningTaskInfo rti = constructRunningTaskInfo();
					throw new AutomataOperationCanceledException(rti);
				}
				final StateContainer<LETTER, STATE> predCont = mOperand.getStateContainer(trans.getPred());
				if (predCont != null) {
					predCont.removeSuccessor(st);
				}
				pred.add(trans.getPred());
			}
			cont.removePredecessors(pred);
			mOperand.removeStates(st);
		}
	}

	private RunningTaskInfo constructRunningTaskInfo() {
		final String taskDescription = "remove unused states (" + mOperand.getClass().getSimpleName() + ")";
		final RunningTaskInfo rti = new RunningTaskInfo(getClass(), taskDescription);
		return rti;
	}

	public INestedWordAutomaton<LETTER, STATE> getResult() {
		return mOperand;
	}

}
