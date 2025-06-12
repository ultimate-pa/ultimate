package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.ScopedTransitivityGenerator.NormalNode;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.ScopedTransitivityGenerator.ScopeStack;
import de.uni_freiburg.informatik.ultimate.automata.util.ISetOfPairs;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public abstract class ScopedConsistencyGeneratorDelayedSimulation<T, LETTER, STATE>
		implements IAssignmentCheckerAndGenerator<T> {

	protected final Map<STATE, NormalNode<STATE>> mContent2node;

	private final ScopeStack<STATE> mStack;

	private final boolean mCompressPaths;

	protected ISetOfPairs<STATE, ?> mSpoilerWinnings;
	protected ISetOfPairs<STATE, ?> mDuplicatorWinnings;

	public final INestedWordAutomaton<LETTER, STATE> mOperand;
	private final AutomataLibraryServices mServices;

	public ScopedConsistencyGeneratorDelayedSimulation(final boolean compressPaths,
			final AutomataLibraryServices services, final INestedWordAutomaton<LETTER, STATE> operand) {
		mContent2node = new HashMap<>();
		mStack = new ScopeStack<>();
		mCompressPaths = compressPaths;
		mSpoilerWinnings = null;
		mDuplicatorWinnings = null;
		mOperand = operand;
		mServices = services;
	}

	@Override
	public void addScope() {
		mStack.addScope();
	}

	@Override
	public void makeAssignmentsPersistent() {
		mStack.makeAllScopesPersistent();
	}

	@Override
	public void revertOneScope() {
		mStack.revertOneScope();
	}

	@Override
	public abstract void addVariable(final T var);

	public void addContent(final STATE s) {
		mContent2node.put(s, new NormalNode<>(s));
	}

	@Override
	public abstract Iterable<Pair<T, Boolean>> checkAssignment(final T doubleton, final boolean newStatus);

	// Recomputes the winning states for Spoiler and Duplicator
	protected void updateWinningStates() throws AutomataOperationCanceledException {
		final BiPredicateStateMap<STATE> areStatesMerged = new BiPredicateStateMap<>(mContent2node, mCompressPaths);
		final NwaApproximateDelayedSimulation<LETTER, STATE> simulation =
				new NwaApproximateDelayedSimulation<>(mServices, mOperand, areStatesMerged);
		mSpoilerWinnings = simulation.getSpoilerWinningStates();
		mDuplicatorWinnings = simulation.getDuplicatorEventuallyAcceptingStates();
	}
}
