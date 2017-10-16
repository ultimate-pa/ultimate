package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.BiPredicate;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.util.ISetOfPairs;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.ScopedTransitivityGenerator.INode;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.ScopedTransitivityGenerator.INodePredicate;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.ScopedTransitivityGenerator.NormalNode;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.ScopedTransitivityGenerator.PersistentRootPredicate;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.ScopedTransitivityGenerator.ScopeStack;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.ScopedTransitivityGenerator.TemporaryRootPredicate;


public class ScopedConsistencyGeneratorDelayedSimulation<T, LETTER, STATE> implements IAssignmentCheckerAndGenerator<T> {

	protected final Map<STATE, NormalNode<STATE>> mContent2node;

	private final ScopeStack<STATE> mStack;

	private final boolean mCompressPaths;
	
	private ISetOfPairs<STATE, ?> mSpoilerWinnings;
	private ISetOfPairs<STATE, ?> mDuplicatorWinnings;
	
	private final INestedWordAutomaton<LETTER, STATE> mOperand;
	private final AutomataLibraryServices mServices;
	
	public ScopedConsistencyGeneratorDelayedSimulation(boolean compressPaths, final AutomataLibraryServices services, final INestedWordAutomaton<LETTER, STATE> operand) {
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
	public void addVariable(final T doubleton) {
		assert mContent2node.containsKey(((Doubleton<STATE>) doubleton).getOneElement()) && mContent2node.containsKey(((Doubleton<STATE>) doubleton).getOtherElement());
	}
	
	public void addContent(final STATE s) {
		mContent2node.put(s, new NormalNode<STATE>(s));
	}
	
	@Override
	//Checks if the merge states overlap with the simulation results
	public Iterable<Pair<T, Boolean>> checkAssignment(final T doubleton, final boolean newStatus){
		
		try {
			updateWinningStates();
		} catch (AutomataOperationCanceledException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		//TODO: Not very nice: explicit cast to pair type. Could be solved by using a Doubleton class version.
		assert doubleton instanceof Doubleton<?> : "Type error: pairs of states needed.";
		STATE lhs = ((Doubleton<STATE>) doubleton).getOneElement();
		STATE rhs = ((Doubleton<STATE>) doubleton).getOtherElement();
		
		if (newStatus && (!mSpoilerWinnings.containsPair(lhs, rhs) && !mSpoilerWinnings.containsPair(rhs, lhs))) {
			final Pair<T, Boolean> corrected = new Pair<T, Boolean>(doubleton, false);	
			List<Pair<T, Boolean>> result = new ArrayList<>();
			result.add(corrected);
			return result;
		}
		//TODO: How do we deal with the rest in a smart way?
		else {
			return Collections.emptySet();
		}
	}
	
	//Recomputes the winning states for Spoiler and Duplicator
	protected void updateWinningStates() throws AutomataOperationCanceledException {
		final BiPredicateStateMap<STATE> areStatesMerged = new BiPredicateStateMap<STATE>(mContent2node, mCompressPaths);
		NwaApproximateDelayedSimulation<LETTER,STATE> simulation = new NwaApproximateDelayedSimulation<LETTER, STATE>(mServices, mOperand, areStatesMerged);
		mSpoilerWinnings = simulation.getSpoilerWinningStates();
		mDuplicatorWinnings = simulation.getDuplicatorEventuallyAcceptingStates();
	}
}