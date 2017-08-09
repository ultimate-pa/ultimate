package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.function.BiPredicate;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.NwaApproximateSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.NwaApproximateXsimulation.SimulationType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.util.ISetOfPairs;
import de.uni_freiburg.informatik.ultimate.automata.util.MapBackedSetOfPairs;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.ScopedTransitivityGenerator.INode;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.ScopedTransitivityGenerator.INodePredicate;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.ScopedTransitivityGenerator.NormalNode;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.ScopedTransitivityGenerator.PersistentRootPredicate;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.ScopedTransitivityGenerator.ScopeStack;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.ScopedTransitivityGenerator.TemporaryRootPredicate;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;


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
		
	}
	
	@Override
	public void makeAssignmentsPersistent() {
		
	}
	
	@Override
	public void revertOneScope() {
	
	}
	
	@Override
	public void addVariable(final T var) {
		
	}
	
	public void addContent(final STATE s) {
		
	}
	
	@Override
	//TODO: Make output a list of the Spoiler Winnings & implement getFirst/Second
	public Iterable<Pair<T, Boolean>> checkAssignment(final T pair, final boolean newStatus){
		
		try {
			updateWinningStates();
		} catch (AutomataOperationCanceledException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		//Not very nice: explicit cast to pair type. Could be solved by using a Doubleton class version.
		assert pair instanceof Pair<?, ?> : "Type error: pairs of states needed.";
		
		//No need to do anything if the results match
		if (newStatus && mSpoilerWinnings.containsPair(((Pair<STATE, STATE>) pair).getFirst(), ((Pair<STATE, STATE>) pair).getSecond()) ||
				!newStatus && mDuplicatorWinnings.containsPair(((Pair<STATE, STATE>) pair).getFirst(), ((Pair<STATE, STATE>) pair).getSecond())) {
			return Collections.emptySet();
		}
		
		return Collections.emptySet();
	}
	
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
