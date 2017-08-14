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

	private final TemporaryRootPredicate mTemporaryRootPredicate;
	private final PersistentRootPredicate mPersistentRootPredicate;

	private final boolean mCompressPaths;
	
	private ISetOfPairs<STATE, ?> mSpoilerWinnings;
	private ISetOfPairs<STATE, ?> mDuplicatorWinnings;
	
	private final INestedWordAutomaton<LETTER, STATE> mOperand;
	private final AutomataLibraryServices mServices;
	
	public ScopedConsistencyGeneratorDelayedSimulation(boolean compressPaths, final AutomataLibraryServices services, final INestedWordAutomaton<LETTER, STATE> operand) {
		mContent2node = new HashMap<>();
		mStack = new ScopeStack<>();
		mTemporaryRootPredicate = new TemporaryRootPredicate();
		mPersistentRootPredicate = new PersistentRootPredicate();
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
		mContent2node.put(s, new NormalNode<>(s));
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
		
		//Not very nice: explicit cast to pair type. Could be solved by using a Doubleton class version.
		assert doubleton instanceof Doubleton<?> : "Type error: pairs of states needed.";
		STATE lhs = ((Doubleton<STATE>) doubleton).getOneElement();
		STATE rhs = ((Doubleton<STATE>) doubleton).getOtherElement();
		
		//No need to do anything if the results match
		if (newStatus && mSpoilerWinnings.containsPair(lhs, rhs) ||
				!newStatus && mDuplicatorWinnings.containsPair(lhs, rhs)) {
			return Collections.emptySet();
		}
		//correct wrongly merge states
		else if (newStatus && mDuplicatorWinnings.containsPair(lhs, rhs)) {
			final Pair<T, Boolean> corrected = new Pair<T, Boolean>(doubleton, false);
			List<Pair<T, Boolean>> result = new ArrayList<>();
			result.add(corrected);
			return result;
		}
		//here we can merge more
		else if (!newStatus && mSpoilerWinnings.containsPair(lhs, rhs)) {
			final Pair<T, Boolean> corrected = new Pair<T, Boolean>(doubleton, true);
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
		final BiPredicate<STATE, STATE> areStatesMerged = new BiPredicate<STATE, STATE>() {
			@Override
			public boolean test(final STATE t, final STATE u) {
				final NormalNode<STATE> root1 = find(mContent2node.get(t));
				final NormalNode<STATE> root2 = find(mContent2node.get(u));
				if (root1 == root2) {
					return true;
				}
				else {
					return false;
				}
			}
		};
		NwaApproximateDelayedSimulation<LETTER,STATE> simulation = new NwaApproximateDelayedSimulation<LETTER, STATE>(mServices, mOperand, areStatesMerged);
		mSpoilerWinnings = simulation.getSpoilerWinningStates();
		mDuplicatorWinnings = simulation.getDuplicatorEventuallyAcceptingStates();
	}
	
	@SuppressWarnings("squid:S1698")
	private NormalNode<STATE> find(final NormalNode<STATE> source) {
		if (mCompressPaths) {
			final NormalNode<STATE> persistentParent = findNextRoot(source, mPersistentRootPredicate);
			if (source != persistentParent) {
				// if the source is not the transitive persistent parent of its subtree, compress the path to this node
				final INode<STATE> sourceDirectParent = source.getParent();
				assert sourceDirectParent.getClass() == NormalNode.class : "";
				// remove source from its direct parent's children
				((NormalNode<STATE>) sourceDirectParent).removeNormalChild(source);
				// set source's new parent to transitive parent
				source.setParent(persistentParent);
				// add source to transitive parent's children
				persistentParent.addNormalChild(source);
			}
			return findNextRoot(persistentParent, mTemporaryRootPredicate);
		}
		return findNextRoot(source, mTemporaryRootPredicate);
	}
	
	@SuppressWarnings("hiding")
	private <INodePredicate> NormalNode<STATE> findNextRoot(final NormalNode<STATE> source, final INodePredicate predicate) {
		INode<STATE> node = source;
		while (!((de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.ScopedTransitivityGenerator.INodePredicate) predicate).check(node)) {
			node = node.getParent();
		}
		assert node.getClass() == NormalNode.class : "Invalid tree root.";
		return (NormalNode<STATE>) node;
	}

}
