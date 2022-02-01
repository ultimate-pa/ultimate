package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class ScopedConsistencyGeneratorDelayedSimulationDoubleton<T, LETTER, STATE> extends ScopedConsistencyGeneratorDelayedSimulation<Doubleton<T>, LETTER, STATE> {

	public ScopedConsistencyGeneratorDelayedSimulationDoubleton(boolean compressPaths, AutomataLibraryServices services,
			INestedWordAutomaton<LETTER, STATE> operand) {
		super(compressPaths, services, operand);
		// TODO Auto-generated constructor stub
	}
	
	@Override
	public void addVariable(Doubleton<T> doubleton) {
		assert mContent2node.containsKey(doubleton.getOneElement()) && mContent2node.containsKey(doubleton.getOtherElement());
	}
	
	@Override
	//Checks if the merge states overlap with the simulation results
	public Iterable<Pair<Doubleton<T>, Boolean>> checkAssignment(final Doubleton<T> doubleton, final boolean newStatus){
		
		try {
			updateWinningStates();
		} catch (AutomataOperationCanceledException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		STATE lhs = ((Doubleton<STATE>)doubleton).getOneElement();
		STATE rhs = ((Doubleton<STATE>)doubleton).getOtherElement();
		
		if (newStatus && (!mSpoilerWinnings.containsPair(lhs, rhs) || !mSpoilerWinnings.containsPair(rhs, lhs))) {
			final Pair<Doubleton<T>, Boolean> corrected = new Pair<Doubleton<T>, Boolean>(doubleton, false);	
			List<Pair<Doubleton<T>, Boolean>> result = new ArrayList<>();
			result.add(corrected);
			return result;
		}
		//TODO: How do we deal with the rest in a smart way?
		else {
			return Collections.emptySet();
		}
	}
}
