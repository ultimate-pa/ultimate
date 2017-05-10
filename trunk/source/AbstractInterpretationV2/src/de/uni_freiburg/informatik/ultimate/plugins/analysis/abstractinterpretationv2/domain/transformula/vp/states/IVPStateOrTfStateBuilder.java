/*
 * Copyright (C) 2016 Yu-Wen Chen
 * Copyright (C) 2016 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainHelpers;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqGraphNode;

/**
 * VPStateBuilder and VPTfStateBuilder are structurally similar, they both manage equalities through congruence closure 
 * and disequalities through a set, and allow updating on those.
 * This abstract class captures this overlap.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <T>
 * @param <NODEID>
 * @param <ARRAYID>
 */
public abstract class IVPStateOrTfStateBuilder<T extends IVPStateOrTfState<NODEID, ARRAYID>, NODEID extends IEqNodeIdentifier<ARRAYID>, ARRAYID> {
	
	protected final Set<VPDomainSymmetricPair<NODEID>> mDisEqualitySet;

	protected boolean mIsTop = true;
	
	/**
	 * copy constructor
	 *
	 * @param builder
	 */
	public IVPStateOrTfStateBuilder(final IVPStateOrTfStateBuilder<T, NODEID, ARRAYID> builder) {
		mDisEqualitySet = new HashSet<>(builder.mDisEqualitySet);
//		mVars = new HashSet<>(builder.mVars);
		mIsTop = builder.mIsTop;
	}
	
	/**
	 * constructor for empty builder
	 * @param initialDisequalities 
	 */
	public IVPStateOrTfStateBuilder(Set<VPDomainSymmetricPair<NODEID>> initialDisequalities) {
		mDisEqualitySet = new HashSet<>(initialDisequalities);
//		mVars = new HashSet<>();
	}

	public abstract EqGraphNode<NODEID, ARRAYID> getEqGraphNode(NODEID i2);
	
	abstract Collection<EqGraphNode<NODEID, ARRAYID>> getAllEqGraphNodes();

	abstract T build();
	
	IVPStateOrTfStateBuilder<T, NODEID, ARRAYID> setIsTop(final boolean b) {
		mIsTop = b;
		return this;
	}

	/**
	 * Merge two congruence class. propagation.
	 *
	 * @param i1
	 * @param i2
	 */
	public void merge(final EqGraphNode<NODEID, ARRAYID> node1, final EqGraphNode<NODEID, ARRAYID> node2) {
		if (node1 == node2 || node1.find() == node2.find()) {
			// nothing to do
			return;
		}

		setIsTop(false);

		union(node1, node2);
		equalityPropagation(node1, node2);

//		assert VPDomainHelpers.disEqualityRelationIrreflexive(this.mDisEqualitySet, this);
	}

	/**
	 * Union of two equivalence classes. The representative of node1 will become the representative of node2.
	 *
	 * @param node1
	 * @param node2
	 */
	protected void union(final EqGraphNode<NODEID, ARRAYID> node1, final EqGraphNode<NODEID, ARRAYID> node2) {
		
		assert VPDomainHelpers.disEqualitySetContainsOnlyRepresentatives(mDisEqualitySet, this);

		if (node1.find().equals(node2.find())) {
			assert false : "this should have been checked before calling union";
			return;
		}
		
		final EqGraphNode<NODEID, ARRAYID> oldNode1Representative = node1.find();
		
		node2.find().addToReverseRepresentative(node1.find());
		node2.find().addToCcpar(node1.find().getCcpar());
		node2.find().addToCcchild(node1.find().getCcchild());
		// this set-operation must come after the other 3 above (because find is called on node1 for all the others)!!
		node1.find().setRepresentative(node2.find());

		assert VPDomainHelpers.disEqualityRelationIrreflexive(this.mDisEqualitySet, this);

		/*
		 * Because node1.find has a new representative, any disequality that contains its old representative must be
		 * updated to its new representative
		 *
		 */
		final Set<VPDomainSymmetricPair<NODEID>> copyOfDisEqSet = new HashSet<>(mDisEqualitySet);
		for (final VPDomainSymmetricPair<NODEID> pair : copyOfDisEqSet) {
			final EqGraphNode<NODEID, ARRAYID> firstEqnInDisEquality = getEqGraphNode(pair.getFirst());
			final EqGraphNode<NODEID, ARRAYID> secondEqnInDisEquality = getEqGraphNode(pair.getSecond());

			if (firstEqnInDisEquality != oldNode1Representative && secondEqnInDisEquality != oldNode1Representative) {
				// pair does not contain node1's old representative
				continue;
			}
			
			NODEID newFirst = pair.getFirst();
			NODEID newSecond = pair.getSecond();
			
			if (firstEqnInDisEquality == oldNode1Representative) {
				newFirst = node1.find().mNodeIdentifier;
			}
			if (secondEqnInDisEquality == oldNode1Representative) {
				newSecond = node1.find().mNodeIdentifier;
			}

			mDisEqualitySet.remove(pair);
			mDisEqualitySet.add(new VPDomainSymmetricPair<NODEID>(newFirst, newSecond));
//			assert VPDomainHelpers.disEqualityRelationIrreflexive(this.mDisEqualitySet, this); // this may happen if, 
																						//in fact, we have a conflict
		}

		assert VPDomainHelpers.disEqualitySetContainsOnlyRepresentatives(mDisEqualitySet, this);
//		assert VPDomainHelpers.disEqualityRelationIrreflexive(this.mDisEqualitySet, this);
	}

	private void equalityPropagation(final EqGraphNode<NODEID, ARRAYID> node1,
			final EqGraphNode<NODEID, ARRAYID> node2) {
		final Set<EqGraphNode<NODEID, ARRAYID>> p1 = ccpar(node1);
		final Set<EqGraphNode<NODEID, ARRAYID>> p2 = ccpar(node2);

		for (final EqGraphNode<NODEID, ARRAYID> t1 : p1) {
			for (final EqGraphNode<NODEID, ARRAYID> t2 : p2) {
				if (!(t1.find().equals(t2.find())) && congruent(t1, t2)) {
					merge(t1, t2);
				}
			}
		}
//		assert VPDomainHelpers.disEqualityRelationIrreflexive(this.mDisEqualitySet, this);
	}

	/**
	 * Check whether @param node1 and @param node2 are congruent.
	 *
	 * @param node1
	 * @param node2
	 * @return true if they are congruent
	 */
	protected boolean congruent(final EqGraphNode<NODEID, ARRAYID> node1, final EqGraphNode<NODEID, ARRAYID> node2) {
		if (!(node1.mNodeIdentifier.isFunction()) || !(node2.mNodeIdentifier.isFunction())) {
			return false;
		}

		// final EqFunctionNode fnNode1 = (EqFunctionNode) node1.eqNode;
		// final EqFunctionNode fnNode2 = (EqFunctionNode) node2.eqNode;

		if (!(node1.mNodeIdentifier.getFunction().equals(node2.mNodeIdentifier.getFunction()))) {
			return false;
		}
		return VPFactoryHelpers.congruentIgnoreFunctionSymbol(node1, node2);
	}

	/*
	 * Returns the parents of all nodes in @param node's congruence class.
	 *
	 * @param node
	 *
	 * @return
	 */
	private Set<EqGraphNode<NODEID, ARRAYID>> ccpar(final EqGraphNode<NODEID, ARRAYID> node) {
		return node.find().getCcpar();
	}

	/**
	 * Adds a pair to the set of disequality pairs that this builder holds.
	 * 
	 * Note: This does not close the state, thus the result might not be a "state" in the strict sense. Should only be
	 *  called from more high-level methods that will later deal with possible propagations.
	 * 
	 * @param id1
	 * @param id2
	 */
	public void addDisEquality(final NODEID id1, final NODEID id2) {
		assert !id1.equals(id2);
		// assert getEqGraphNode(id1).find() == getEqGraphNode(id1) :
		// "the caller of this procedure has to make sure to call it on representatives only!";
		// assert getEqGraphNode(id2).find() == getEqGraphNode(id2) :
		// "the caller of this procedure has to make sure to call it on representatives only! "
		// + getEqGraphNode(id2).find() + " vs " + getEqGraphNode(id2);
		setIsTop(false);
		
		assert !id1.equals(id2);
		
		final EqGraphNode<NODEID, ARRAYID> egn1 = getEqGraphNode(id1);
		final EqGraphNode<NODEID, ARRAYID> egn2 = getEqGraphNode(id2);
		assert !egn1.equals(egn2);
		mDisEqualitySet.add(new VPDomainSymmetricPair<NODEID>(egn1.find().mNodeIdentifier, egn2.find().mNodeIdentifier));
		// mDisEqualitySet.add(new VPDomainSymmetricPair<NODEID>(id1, id2));
	}
//
//	public void addDisEquality(final VPDomainSymmetricPair<NODEID> newDisequality) {
//		// assert getEqGraphNode(newDisequality.getFirst()).find() == getEqGraphNode(newDisequality.getFirst()) :
//		// "the caller of this procedure has to make sure to call it on representatives only!";
//		// assert getEqGraphNode(newDisequality.getSecond()).find() == getEqGraphNode(newDisequality.getSecond()) :
//		// "the caller of this procedure has to make sure to call it on representatives only!";
//		setIsTop(false);
//		// mDisEqualitySet.add(newDisequality);
//		addDisEquality(newDisequality.getFirst(), newDisequality.getSecond());
//	}
//
//	public void addDisEqualites(final Set<VPDomainSymmetricPair<NODEID>> newDisequalities) {
//		// for (VPDomainSymmetricPair<NODEID> newDisequality : newDisequalities) {
//		// assert getEqGraphNode(newDisequality.getFirst()).find() == getEqGraphNode(newDisequality.getFirst()) :
//		// "the caller of this procedure has to make sure to call it on representatives only!";
//		// assert getEqGraphNode(newDisequality.getSecond()).find() == getEqGraphNode(newDisequality.getSecond()) :
//		// "the caller of this procedure has to make sure to call it on representatives only!";
//		// }
//
//		setIsTop(false);
//		for (final VPDomainSymmetricPair<NODEID> newDisequality : newDisequalities) {
//			addDisEquality(newDisequality);
//		}
//		// mDisEqualitySet.addAll(newDisequalities);
//	}


	
	/**
	 * Use disEqualitySet to check if there exist contradiction in the graph.
	 *
	 * @return true if there is contradiction
	 */
	boolean checkContradiction() {
		
		for (final VPDomainSymmetricPair<NODEID> disEqPair : mDisEqualitySet) {
			if (getEqGraphNode(disEqPair.getFirst()).find().equals(getEqGraphNode(disEqPair.getSecond()).find())) {
				return true;
			}
		}
		return false;
	}
	
	public boolean isTopConsistent() {
		if (!mIsTop) {
			return true;
		}
		for (final VPDomainSymmetricPair<NODEID> pair : mDisEqualitySet) {
			if (!pair.getFirst().isLiteral() || !pair.getSecond().isLiteral()) {
				return false;
			}
		}
		
		for (final EqGraphNode<NODEID, ARRAYID> egn : getAllEqGraphNodes()) {
			if (egn.getRepresentative() != egn) {
				return false;
			}
		}
		return true;
	}
	
	@Override
	public String toString() {
		return "Builder:\n" + this.build().toString();
	}

	public Set<VPDomainSymmetricPair<NODEID>> getDisEqualitySet() {
		return Collections.unmodifiableSet(mDisEqualitySet);
	}

	public boolean isTop() {
		return mIsTop;
	}

	public void removeDisEquality(final VPDomainSymmetricPair<NODEID> diseq) {
		mDisEqualitySet.remove(diseq);
	}
}
