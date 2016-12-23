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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;

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

	abstract EqGraphNode<NODEID, ARRAYID> getEqGraphNode(NODEID i2);
	
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
		
	//			final EqGraphNode graphNode1Find = find(node1);
	//			final EqGraphNode graphNode2Find = find(node2);
		
				if (!node1.find().equals(node2.find())) {
					node2.find().addToReverseRepresentative(node1.find());
					node1.find().setRepresentative(node2.find());
					node2.find().addToCcpar(node1.find().getCcpar());
					for (final Entry<ARRAYID, List<EqGraphNode<NODEID, ARRAYID>>> entry : node1.find().getCcchild().entrySet()) {
						node2.find().getCcchild().addPair(entry.getKey(), entry.getValue());
					}
					
					/*
					 * Because of the change of representative, the disequality set also need to be updated.
					 */
					Set<VPDomainSymmetricPair<NODEID>> copyOfDisEqSet = new HashSet<>(mDisEqualitySet);
					for (VPDomainSymmetricPair<NODEID> pair : copyOfDisEqSet) {
						if (pair.contains(node1.find().nodeIdentifier)) {
							NODEID first = pair.getFirst();
							NODEID second = pair.getSecond();
							
							/*
							 * TODO check: If both nodes in pair are constant, ignore it.
							 */
							if (first.isLiteral() && second.isLiteral()) {
								continue;
							}
							
							mDisEqualitySet.remove(pair);
							if (first.equals(node1.find().nodeIdentifier)) {
								mDisEqualitySet.add(
										new VPDomainSymmetricPair<NODEID>(node1.find().nodeIdentifier, second));
							} else {
								mDisEqualitySet.add(
										new VPDomainSymmetricPair<NODEID>(first, node2.find().nodeIdentifier));
							}
						}
					}
				}
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
		setIsTop(false);
		mDisEqualitySet.add(new VPDomainSymmetricPair<NODEID>(id1, id2));
	}

	public void addDisEquality(VPDomainSymmetricPair<NODEID> newDisequality) {
		setIsTop(false);
		mDisEqualitySet.add(newDisequality);
	}

	public void addDisEqualites(Set<VPDomainSymmetricPair<NODEID>> newDisequalities) {
		setIsTop(false);
		mDisEqualitySet.addAll(newDisequalities);
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
	
	protected boolean isTopConsistent() {
		if (!mIsTop) {
			return true;
		}
		for (VPDomainSymmetricPair<NODEID> pair : mDisEqualitySet) {
			if (!pair.mFst.isLiteral() || !pair.mSnd.isLiteral()) {
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
}
