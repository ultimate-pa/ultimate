package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections;

import java.util.Map;
import java.util.function.BiPredicate;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.ScopedTransitivityGenerator.BridgeNode;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.ScopedTransitivityGenerator.INode;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.ScopedTransitivityGenerator.NormalNode;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.ScopedTransitivityGenerator.PersistentRootPredicate;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.ScopedTransitivityGenerator.TemporaryRootPredicate;

public class BiPredicateStateMap <STATE> implements BiPredicate<STATE, STATE>{
	
	private final Map<STATE, NormalNode<STATE>> mStateMap;
	private final TemporaryRootPredicate mTemporaryRootPredicate;
	private final PersistentRootPredicate mPersistentRootPredicate;
	
	private final boolean mCompressPaths;


	public BiPredicateStateMap (Map<STATE, NormalNode<STATE>> stateMap, boolean compressPaths) {
		mStateMap = stateMap;
		mTemporaryRootPredicate = new TemporaryRootPredicate();
		mPersistentRootPredicate = new PersistentRootPredicate();
		mCompressPaths = compressPaths;
	}

	public boolean test(final STATE t, final STATE u) {
	
		if(mStateMap.isEmpty() || mStateMap.get(t) == null || mStateMap.get(u) == null) {
			return false;
		}
		else {
			final NormalNode<STATE> root1 = find(mStateMap.get(t));
			final NormalNode<STATE> root2 = find(mStateMap.get(u));
			if (root1 == root2) {
				return true;
			}
			else {
				return false;
			}
		}
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

		while (node.isRoot()) { //|| predicate instanceof TemporaryRootPredicate && (node.getParent().getClass() == BridgeNode.class)) {
			node = node.getParent();
		}
		assert node.getClass() == NormalNode.class : "Invalid tree root.";
		return (NormalNode<STATE>) node;
	}
}