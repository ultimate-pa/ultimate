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
import java.util.List;
import java.util.Set;
import java.util.Map.Entry;

import org.eclipse.osgi.internal.loader.ModuleClassLoader.GenerationProtectionDomain;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainHelpers;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqGraphNode;

public abstract class IVPStateOrTfStateBuilder<T extends IVPStateOrTfState<NODEID, ARRAYID>, NODEID extends IEqNodeIdentifier<ARRAYID>, ARRAYID> {

	protected final Set<VPDomainSymmetricPair<NODEID>> mDisEqualitySet;

	protected final Set<IProgramVar> mVars;
	
	protected boolean mIsTop = true;
	
	/**
	 * copy constructor
	 * @param builder
	 */
	public IVPStateOrTfStateBuilder(IVPStateOrTfStateBuilder<T, NODEID, ARRAYID> builder) {
		mDisEqualitySet = new HashSet<>(builder.mDisEqualitySet);
		mVars = new HashSet<>(builder.mVars);
		mIsTop = builder.mIsTop;
	}
	
	/**
	 * constructor for empty builder
	 */
	public IVPStateOrTfStateBuilder() {
		mDisEqualitySet = new HashSet<>();
		mVars = new HashSet<>();
	}

	public abstract EqGraphNode<NODEID, ARRAYID> getEqGraphNode(NODEID i2);
	
	abstract Collection<EqGraphNode<NODEID, ARRAYID>> getAllEqGraphNodes();

	abstract T build();
	
	IVPStateOrTfStateBuilder<T, NODEID, ARRAYID> setIsTop(boolean b) {
		mIsTop = b;
		return this;
	}

	/**
	 * Merge two congruence class. propagation.
	 *
	 * @param i1
	 * @param i2
	 */
	void merge(final EqGraphNode<NODEID, ARRAYID> node1, final EqGraphNode<NODEID, ARRAYID> node2) {
		if (node1 == node2) {
			//nothing to do
			return;
		}

		setIsTop(false);
			
		if (!node1.find().equals(node2.find())) {
			union(node1, node2);
			equalityPropagation(node1, node2);
		}
	}	

	/**
	 * Union of two equivalence classes. 
	 * The representative of node1 will become the representative of node2.
	 *
	 * @param node1
	 * @param node2
	 */
	protected void union(final EqGraphNode<NODEID, ARRAYID> node1, final EqGraphNode<NODEID, ARRAYID> node2) {
		
		assert VPDomainHelpers.disEqualitySetContainsOnlyRepresentatives(mDisEqualitySet, this);

		//			final EqGraphNode graphNode1Find = find(node1);
		//			final EqGraphNode graphNode2Find = find(node2);

		if (node1.find().equals(node2.find())) {
			return;
		}
		node2.find().addToReverseRepresentative(node1.find());
		node2.find().addToCcpar(node1.find().getCcpar());
		node2.find().addToCcchild(node1.find().getCcchild());
		// this set-operation must come after the other 3 above (because find is called on node1 for all the others)!!
		node1.find().setRepresentative(node2.find());

//		for (final Entry<ARRAYID, List<EqGraphNode<NODEID, ARRAYID>>> entry : node1.find().getCcchild().entrySet()) {
//			node2.find().getCcchild().addPair(entry.getKey(), entry.getValue());
//		}

		/*
		 * Because of the change of representative, the disequality set also need to be updated.
		 */
		Set<VPDomainSymmetricPair<NODEID>> copyOfDisEqSet = new HashSet<>(mDisEqualitySet);
		for (VPDomainSymmetricPair<NODEID> pair : copyOfDisEqSet) {
			NODEID first = pair.getFirst();
			EqGraphNode<NODEID, ARRAYID> firstEqn = getEqGraphNode(first);
			NODEID second = pair.getSecond();
			EqGraphNode<NODEID, ARRAYID> secondEqn = getEqGraphNode(second);
//			if (first.isLiteral() && second.isLiteral()) {
//				continue;
//			}
			if (firstEqn != node1 
					&& secondEqn != node1
					&& firstEqn != node2
					&& secondEqn != node2) {
				// pair does not contain one of the unified nodes
				continue;
			}
			
			if (firstEqn.find() == firstEqn 
					&& secondEqn.find() == secondEqn) {
				continue;
			}
			
			NODEID newFirst = firstEqn.find().nodeIdentifier;
			NODEID newSecond = secondEqn.find().nodeIdentifier;

			mDisEqualitySet.remove(pair);
			mDisEqualitySet.add(
					new VPDomainSymmetricPair<NODEID>(newFirst, newSecond));
		}

		assert VPDomainHelpers.disEqualitySetContainsOnlyRepresentatives(mDisEqualitySet, this);
	}

	private void equalityPropagation(final EqGraphNode<NODEID, ARRAYID> node1, final EqGraphNode<NODEID, ARRAYID> node2) {
		final Set<EqGraphNode<NODEID, ARRAYID>> p1 = ccpar(node1);
		final Set<EqGraphNode<NODEID, ARRAYID>> p2 = ccpar(node2);
	
		for (final EqGraphNode<NODEID, ARRAYID> t1 : p1) {
			for (final EqGraphNode<NODEID, ARRAYID> t2 : p2) {
				if (!(t1.find().equals(t2.find())) && congruent(t1, t2)) {
					merge(t1, t2);
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
	protected boolean congruent(final EqGraphNode<NODEID, ARRAYID> node1, final EqGraphNode<NODEID, ARRAYID> node2) {
		if (!(node1.nodeIdentifier.isFunction()) || !(node2.nodeIdentifier.isFunction())) {
			return false;
		}

		//			final EqFunctionNode fnNode1 = (EqFunctionNode) node1.eqNode;
		//			final EqFunctionNode fnNode2 = (EqFunctionNode) node2.eqNode;

		if (!(node1.nodeIdentifier.getFunction().equals(node2.nodeIdentifier.getFunction()))) {
			return false;
		}
		return VPFactoryHelpers.congruentIgnoreFunctionSymbol(node1, node2);
	}

	/* Returns the parents of all nodes in @param node's congruence class.
	 *
	 * @param node
	 * @return
	 */
	private Set<EqGraphNode<NODEID, ARRAYID>> ccpar(final EqGraphNode<NODEID, ARRAYID> node) {
		return node.find().getCcpar();
	}

	public void addDisEquality(NODEID id1, NODEID id2) {
		assert !id1.equals(id2);
//		assert getEqGraphNode(id1).find() == getEqGraphNode(id1) : 
//			"the caller of this procedure has to make sure to call it on representatives only!";
//		assert getEqGraphNode(id2).find() == getEqGraphNode(id2) : 
//			"the caller of this procedure has to make sure to call it on representatives only! " 
//			+ getEqGraphNode(id2).find() + " vs " + getEqGraphNode(id2);
		setIsTop(false);
		
		EqGraphNode<NODEID, ARRAYID> egn1 = getEqGraphNode(id1);
		EqGraphNode<NODEID, ARRAYID> egn2 = getEqGraphNode(id2);
		mDisEqualitySet.add(new VPDomainSymmetricPair<NODEID>(egn1.find().nodeIdentifier, egn2.find().nodeIdentifier));
//		mDisEqualitySet.add(new VPDomainSymmetricPair<NODEID>(id1, id2));
	}

	public void addDisEquality(VPDomainSymmetricPair<NODEID> newDisequality) {
//		assert getEqGraphNode(newDisequality.getFirst()).find() == getEqGraphNode(newDisequality.getFirst()) : 
//			"the caller of this procedure has to make sure to call it on representatives only!";
//		assert getEqGraphNode(newDisequality.getSecond()).find() == getEqGraphNode(newDisequality.getSecond()) : 
//			"the caller of this procedure has to make sure to call it on representatives only!";
		setIsTop(false);
//		mDisEqualitySet.add(newDisequality);
		addDisEquality(newDisequality.getFirst(), newDisequality.getSecond());
	}

	public void addDisEqualites(Set<VPDomainSymmetricPair<NODEID>> newDisequalities) {
//		for (VPDomainSymmetricPair<NODEID> newDisequality : newDisequalities) {
//			assert getEqGraphNode(newDisequality.getFirst()).find() == getEqGraphNode(newDisequality.getFirst()) : 
//				"the caller of this procedure has to make sure to call it on representatives only!";
//			assert getEqGraphNode(newDisequality.getSecond()).find() == getEqGraphNode(newDisequality.getSecond()) : 
//				"the caller of this procedure has to make sure to call it on representatives only!";
//		}

		setIsTop(false);
		for (VPDomainSymmetricPair<NODEID> newDisequality : newDisequalities) {
			addDisEquality(newDisequality);
		}
//		mDisEqualitySet.addAll(newDisequalities);
	}

	public IVPStateOrTfStateBuilder<T, NODEID, ARRAYID> addVars(Collection<IProgramVar> newVars) {
		mVars.addAll(newVars);
		return this;
	}

	public IVPStateOrTfStateBuilder<T, NODEID, ARRAYID> removeVars(Collection<IProgramVar> vars) {
		mVars.removeAll(vars);
		return this;
	}
	
	/**
	 * Use disEqualitySet to check if there exist contradiction in the graph.
	 *
	 * @return true if there is contradiction
	 */
	boolean checkContradiction() {

		for (final VPDomainSymmetricPair<NODEID> disEqPair : mDisEqualitySet) {
			if (getEqGraphNode(disEqPair.getFirst()).find()
					.equals(getEqGraphNode(disEqPair.getSecond()).find())) {
				return true;
			}
		}
		return false;
	}
	
	public boolean isTopConsistent() {
		if (!mIsTop) {
			return true;
		}
		for (VPDomainSymmetricPair<NODEID> pair : mDisEqualitySet) {
			if (!pair.getFirst().isLiteral() || !pair.getSecond().isLiteral()) {
				return false;
			}
		}
		
		for (EqGraphNode<NODEID, ARRAYID> egn : getAllEqGraphNodes()) {
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

	public void removeDisEquality(VPDomainSymmetricPair<NODEID> diseq) {
		mDisEqualitySet.remove(diseq);
	}
}
