package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.AlternatingAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.CompoundState;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;

public class NonDeterminizeAA<LETTER, STATE> implements IOperation<LETTER, STATE> {

	//	AlternatingAutomaton<LETTER, STATE> oldAutomaton;
	NestedWordAutomaton<LETTER, CompoundState<STATE>> newAutomaton;

	public NonDeterminizeAA(AlternatingAutomaton<LETTER, STATE> aa) {
		//		this.oldAutomaton = aa;
		this.newAutomaton = nondeterminize(aa);

	}
	public NestedWordAutomaton<LETTER, CompoundState<STATE>> nondeterminize(AlternatingAutomaton<LETTER, STATE> aa) {
		NestedWordAutomaton<LETTER, CompoundState<STATE>> newNwa = new NestedWordAutomaton<>(
				aa.getAlphabet(), 
				Collections.<LETTER> emptySet(), 
				Collections.<LETTER> emptySet(), 
				new StateFactory<CompoundState<STATE>>() {
				});


		ArrayDeque<CompoundState<STATE>> openStates = new ArrayDeque<>();
		for (STATE initialState : aa.getInitialStates()) {
			CompoundState<STATE> newInitState = new CompoundState<>(Collections.singleton(initialState));
			openStates.add(newInitState);
			newNwa.addState(true, aa.getFinalStates().contains(initialState), newInitState);
		}

		while (!openStates.isEmpty()) {
			CompoundState<STATE> currentState = openStates.pollFirst();

			for (LETTER l : aa.getAlphabet()) {
				Set<CompoundState<STATE>> successors = computeSuccessorsOfCompoundState(aa, l, currentState);
				for (CompoundState<STATE> suc : successors) {
					if (!newNwa.getStates().contains(suc)) {
						boolean isFinal = true;
						for (STATE s : suc.getStates()) {
							isFinal &= aa.getFinalStates().contains(s);
						}
						newNwa.addState(false, isFinal, suc); //TODO: insert the real conditions for isFinal and isInitial
						openStates.add(suc);
					}
					newNwa.addInternalTransition(currentState, l, suc);
				}
			}
		}
		return newNwa;
	}

	/**
	 * computes the successors of a compundState in the new NWA by looking at the states contained in
	 * it, and the old transition relation.
	 */
	private Set<CompoundState<STATE>> computeSuccessorsOfCompoundState(
			AlternatingAutomaton<LETTER, STATE> aa,
			LETTER l,
			CompoundState<STATE> currentState) {
		HashSet<STATE> exStates = new HashSet<>();
		HashSet<STATE> univStates = new HashSet<>();
		for (STATE s : currentState.getStates()) {
			if (aa.getExistentialStates().contains(s)) {
				exStates.add(s);
			} else if (aa.getUniversalStates().contains(s)) {
				univStates.add(s);
			} else {
				assert false;
			}
		}
		
		HashSet<HashSet<STATE>> tuples = new HashSet<>();
		//compute the cross product for the existential states' targets
		//(for one given letter, we may enter into any combination of the existential states target states..)
		for (STATE exState : exStates) {
			Set<STATE> exStateTargets = aa.getTransitionsMap().get(exState).get(l);
			if (exStateTargets == null || exStateTargets.isEmpty())
				return Collections.emptySet();
			if (tuples.isEmpty()) {
				for (STATE est : exStateTargets) {
					HashSet<STATE> al = new HashSet<>();
					al.add(est);
					tuples.add(al);
				}
			} else {
				for (HashSet<STATE> t : tuples) {
					for (STATE est : exStateTargets) {
						t.add(est);
					}
				}
			}
		}
		//to each of the tuples add all targes of universal states
		//(as they are always entered for the given letter)
		if (exStates.isEmpty()) {
			tuples.add(new HashSet<STATE>()); //if there are no existential states we have one resulting tuple
		}
		ArrayList<HashSet<STATE>> toRemove = new ArrayList<>();
		for (HashSet<STATE> t : tuples) {
			for (STATE univState : univStates) {
				Set<STATE> univStateTargets = aa.getTransitionsMap().get(univState).get(l);
				if (univStateTargets == null || univStateTargets.isEmpty())
					return Collections.emptySet();
				if (univStateTargets != null) {
					t.addAll(univStateTargets);
				}
			}
			if (t.isEmpty())
				toRemove.add(t);
		}
		for (HashSet<STATE> t : toRemove)
			tuples.remove(t);

		
		HashSet<CompoundState<STATE>> result = new HashSet<>();
		for (HashSet<STATE> t : tuples) {
			result.add(new CompoundState<STATE>(t));
		}

		return result;
	}

	@Override
	public String operationName() {
		return "nondeterminizeAA";
	}

	@Override
	public String startMessage() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String exitMessage() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
//	public Object getResult() throws OperationCanceledException {
	public NestedWordAutomaton<LETTER, CompoundState<STATE>> getResult() throws OperationCanceledException {
		return newAutomaton;
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		// TODO implement a check?
		return true;
	}

}
