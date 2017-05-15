package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqGraphNode;

public class CongruenceGraph<NODE extends IEqNodeIdentifier<FUNCTION>, FUNCTION> {
	
	private boolean mIsFrozen = false;
	
	private final Map<NODE, EqGraphNode<NODE, FUNCTION>> mNodeToEqGraphNode;
	
	
	private final Set<VPDomainSymmetricPair<NODE>> mDisequalities;
	
	public CongruenceGraph() {
		mNodeToEqGraphNode = new HashMap<>();
		mDisequalities = new HashSet<>();
	}
	
	/**
	 * This should only be called from "EqState".
	 * Note that this is not symmetric in that the representative of the first node is changed!
	 * 
	 * @param node1
	 * @param node2
	 */
	void merge(NODE node1, NODE node2) {
		assert !mIsFrozen;
		
		final EqGraphNode<NODE, FUNCTION> egn1 = mNodeToEqGraphNode.get(node1);
		final EqGraphNode<NODE, FUNCTION> egn2 = mNodeToEqGraphNode.get(node2);

		if (egn1 == egn2 || egn1.find() == egn2.find()) {
			// nothing to do
			return;
		}

		union(egn1, egn2);
		equalityPropagation(egn1, egn2);
	}
	
	private void equalityPropagation(final EqGraphNode<NODE, FUNCTION> node1,
			final EqGraphNode<NODE, FUNCTION> node2) {

		final Set<EqGraphNode<NODE, FUNCTION>> p1 = node1.find().getCcpar();
		final Set<EqGraphNode<NODE, FUNCTION>> p2 = node2.find().getCcpar();

		for (final EqGraphNode<NODE, FUNCTION> t1 : p1) {
			for (final EqGraphNode<NODE, FUNCTION> t2 : p2) {
				if (!(t1.find().equals(t2.find())) && congruent(t1, t2)) {
					merge(t1.getNode(), t2.getNode());
				}
			}
		}
	}
	
	/**
	 * Check whether @param node1 and @param node2 are congruent.
	 *
	 * @param node1
	 * @param node2
	 * @return true if they are congruent
	 */
	protected boolean congruent(final EqGraphNode<NODE, FUNCTION> node1, final EqGraphNode<NODE, FUNCTION> node2) {
		if (!(node1.mNodeIdentifier.isFunction()) || !(node2.mNodeIdentifier.isFunction())) {
			return false;
		}

		if (!(node1.mNodeIdentifier.getFunction().equals(node2.mNodeIdentifier.getFunction()))) {
			return false;
		}
		return VPFactoryHelpers.congruentIgnoreFunctionSymbol(node1, node2);
	}
	
		/**
	 * Union of two equivalence classes. The representative of node1 will become the representative of node2.
	 *
	 * @param node1
	 * @param node2
	 */
	protected void union(final EqGraphNode<NODE, FUNCTION> node1, final EqGraphNode<NODE, FUNCTION> node2) {
		
//		assert VPDomainHelpers.disEqualitySetContainsOnlyRepresentatives(mDisEqualitySet, this);

		if (node1.find().equals(node2.find())) {
			assert false : "this should have been checked before calling union";
			return;
		}
		
		final EqGraphNode<NODE, FUNCTION> oldNode1Representative = node1.find();
		
		node2.find().addToReverseRepresentative(node1.find());
		node2.find().addToCcpar(node1.find().getCcpar());
		node2.find().addToCcchild(node1.find().getCcchild());
		// this set-operation must come after the other 3 above (because find is called on node1 for all the others)!!
		node1.find().setRepresentative(node2.find());

//		assert VPDomainHelpers.disEqualityRelationIrreflexive(this.mDisequalities, this);

		/*
		 * Because node1.find has a new representative, any disequality that contains its old representative must be
		 * updated to its new representative
		 *
		 */
		final Set<VPDomainSymmetricPair<NODE>> copyOfDisEqSet = new HashSet<>(mDisequalities);
		for (final VPDomainSymmetricPair<NODE> pair : copyOfDisEqSet) {
			final EqGraphNode<NODE, FUNCTION> firstEqnInDisEquality = getEqGraphNode(pair.getFirst());
			final EqGraphNode<NODE, FUNCTION> secondEqnInDisEquality = getEqGraphNode(pair.getSecond());

			if (firstEqnInDisEquality != oldNode1Representative && secondEqnInDisEquality != oldNode1Representative) {
				// pair does not contain node1's old representative
				continue;
			}
			
			NODE newFirst = pair.getFirst();
			NODE newSecond = pair.getSecond();
			
			if (firstEqnInDisEquality == oldNode1Representative) {
				newFirst = node1.find().mNodeIdentifier;
			}
			if (secondEqnInDisEquality == oldNode1Representative) {
				newSecond = node1.find().mNodeIdentifier;
			}

			mDisequalities.remove(pair);
			mDisequalities.add(new VPDomainSymmetricPair<NODE>(newFirst, newSecond));
//			assert VPDomainHelpers.disEqualityRelationIrreflexive(this.mDisEqualitySet, this); // this may happen if, 
																						//in fact, we have a conflict
		}

//		assert VPDomainHelpers.disEqualitySetContainsOnlyRepresentatives(mDisequalities, this);
	}

	private EqGraphNode<NODE, FUNCTION> getEqGraphNode(NODE node) {
		return mNodeToEqGraphNode.get(node);
	}

	public NODE find(NODE node) {
		return mNodeToEqGraphNode.get(node).find().getNode();
	}
	
	public void havoc (NODE node) {
		assert !mIsFrozen;
		
	}
	
	/**
	 * Use disEqualitySet to check if there exist contradiction in the graph.
	 *
	 * @return true if there is contradiction
	 */
	boolean checkContradiction() {
		
		for (final VPDomainSymmetricPair<NODE> disEqPair : mDisequalities) {
			if (getEqGraphNode(disEqPair.getFirst()).find().equals(getEqGraphNode(disEqPair.getSecond()).find())) {
				return true;
			}
		}
		return false;
	}
	
	public void freeze() {
		assert !mIsFrozen;

		mIsFrozen = true;
	}

	public Set<VPDomainSymmetricPair<NODE>> getDisequalities() {
		return mDisequalities;
	}

	public void addDisequality(NODE find, NODE find2) {
		mDisequalities.add(new VPDomainSymmetricPair<NODE>(find, find2));
	}
}
