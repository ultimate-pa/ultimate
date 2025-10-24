package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class ScopedConsistencyGeneratorDelayedSimulationPair<T, LETTER, STATE>
		extends ScopedConsistencyGeneratorDelayedSimulation<Pair<T, T>, LETTER, STATE> {

	public ScopedConsistencyGeneratorDelayedSimulationPair(final boolean compressPaths,
			final AutomataLibraryServices services, final INestedWordAutomaton<LETTER, STATE> operand) {
		super(compressPaths, services, operand);
		// TODO Auto-generated constructor stub
	}

	@Override
	public void addVariable(final Pair<T, T> pair) {
		assert mContent2node.containsKey(pair.getFirst()) && mContent2node.containsKey(pair.getSecond());
	}

	@Override
	public Iterable<Pair<Pair<T, T>, Boolean>> checkAssignment(final Pair<T, T> pair, final boolean newStatus) {

		try {
			updateWinningStates();
		} catch (final AutomataOperationCanceledException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		final STATE first = ((Pair<STATE, STATE>) pair).getFirst();
		final STATE second = ((Pair<STATE, STATE>) pair).getSecond();

		if (newStatus && !mSpoilerWinnings.containsPair(first, second)) {
			final Pair<Pair<T, T>, Boolean> corrected = new Pair<>(pair, false);
			final List<Pair<Pair<T, T>, Boolean>> result = new ArrayList<>();
			result.add(corrected);
			return result;
		}
		// TODO: How do we deal with the rest in a smart way?
		else {
			return Collections.emptySet();
		}

	}

}
