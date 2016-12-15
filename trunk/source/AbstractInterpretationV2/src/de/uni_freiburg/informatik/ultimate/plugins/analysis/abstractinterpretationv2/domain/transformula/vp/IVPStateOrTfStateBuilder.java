package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;

public abstract class IVPStateOrTfStateBuilder<T extends IVPStateOrTfState> {

	protected Set<VPDomainSymmetricPair<VPNodeIdentifier>> mDisEqualitySet;

	protected Set<IProgramVar> mVars;
	
	protected EqGraph mEqGraph;
	
	abstract EqGraphNode getEqGraphNode(VPNodeIdentifier i2);

	abstract IVPStateOrTfStateBuilder<T> setIsTop(boolean b);

	abstract void addToDisEqSet(VPNodeIdentifier nodeIdentifier, VPNodeIdentifier nodeIdentifier2);

	abstract T build();

//	abstract void merge(EqGraphNode gn1, EqGraphNode gn2);

//	abstract boolean checkContradiction();
	
	/**
	 * Merge two congruence class. propagation.
	 *
	 * @param i1
	 * @param i2
	 */
	void merge(final EqGraphNode node1, final EqGraphNode node2) {
		if (!node1.find().equals(node2.find())) {
			mEqGraph.union(node1, node2);
			mEqGraph.equalityPropagation(node1, node2);
		}
	}	

	
	/**
	 * Checks if the arguments of the given EqFunctionNodes are all congruent.
	 *
	 * @param fnNode1
	 * @param fnNode2
	 * @return
	 */
	boolean congruentIgnoreFunctionSymbol(final EqGraphNode fnNode1, final EqGraphNode fnNode2) {
//		assert fnNode1.getArgs() != null && fnNode2.getArgs() != null;
//		assert fnNode1.getArgs().size() == fnNode2.getArgs().size();
		assert fnNode1.nodeIdentifier.isFunction();
		assert fnNode2.nodeIdentifier.isFunction();

		for (int i = 0; i < fnNode1.getInitCcchild().size(); i++) {
			final EqGraphNode fnNode1Arg = fnNode1.getInitCcchild().get(i);
			final EqGraphNode fnNode2Arg = fnNode2.getInitCcchild().get(i);
			if (!fnNode1Arg.find().equals(fnNode2Arg.find())) {
				return false;
			}
		}
		return true;
	}	

	protected class EqGraph {
		/**
		 * Union of two equivalence classes. 
		 * The representative of node1 will become the representative of node2.
		 *
		 * @param node1
		 * @param node2
		 */
		protected void union(final EqGraphNode node1, final EqGraphNode node2) {
	
//			final EqGraphNode graphNode1Find = find(node1);
//			final EqGraphNode graphNode2Find = find(node2);
	
			if (!node1.find().equals(node2.find())) {
				node2.find().addToReverseRepresentative(node1.find());
				node1.find().setRepresentative(node2.find());
				node2.find().addToCcpar(node1.find().getCcpar());
				for (final Entry<VPArrayIdentifier, List<EqGraphNode>> entry : node1.find().getCcchild().entrySet()) {
					node2.find().getCcchild().addPair(entry.getKey(), entry.getValue());
				}
				
				/*
				 * Because of the change of representative, the disequality set also need to be updated.
				 */
				Set<VPDomainSymmetricPair<VPNodeIdentifier>> copyOfDisEqSet = new HashSet<>(mDisEqualitySet);
				for (VPDomainSymmetricPair<VPNodeIdentifier> pair : copyOfDisEqSet) {
					if (pair.contains(node1.find().nodeIdentifier)) {
						VPNodeIdentifier first = pair.getFirst();
						VPNodeIdentifier second = pair.getSecond();
						
						/*
						 * TODO check: If both nodes in pair are constant, ignore it.
						 */
						if (first.isLiteral() && second.isLiteral()) {
							continue;
						}
						
						mDisEqualitySet.remove(pair);
						if (first.equals(node1.find().nodeIdentifier)) {
							mDisEqualitySet.add(
									new VPDomainSymmetricPair<VPNodeIdentifier>(node1.find().nodeIdentifier, second));
						} else {
							mDisEqualitySet.add(
									new VPDomainSymmetricPair<VPNodeIdentifier>(first, node2.find().nodeIdentifier));
						}
					}
				}
			}
		}

		private void equalityPropagation(final EqGraphNode node1, final EqGraphNode node2) {
			final Set<EqGraphNode> p1 = ccpar(node1);
			final Set<EqGraphNode> p2 = ccpar(node2);

			for (final EqGraphNode t1 : p1) {
				for (final EqGraphNode t2 : p2) {
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
		private boolean congruent(final EqGraphNode node1, final EqGraphNode node2) {
			if (!(node1.nodeIdentifier.isFunction()) || !(node2.nodeIdentifier.isFunction())) {
				return false;
			}

//			final EqFunctionNode fnNode1 = (EqFunctionNode) node1.eqNode;
//			final EqFunctionNode fnNode2 = (EqFunctionNode) node2.eqNode;

			if (!(node1.nodeIdentifier.getFunction().equals(node2.nodeIdentifier.getFunction()))) {
				return false;
			}
			return congruentIgnoreFunctionSymbol(node1, node2);
		}
		
		/* Returns the parents of all nodes in @param node's congruence class.
		 *
		 * @param node
		 * @return
		 */
		private Set<EqGraphNode> ccpar(final EqGraphNode node) {
			return node.find().getCcpar();
		}
	}

	public void addDisEqualites(Set<VPDomainSymmetricPair<VPNodeIdentifier>> newDisequalities) {
		mDisEqualitySet.addAll(newDisequalities);
	}

	public void addVars(Set<IProgramVar> newVars) {
		mVars.addAll(newVars);
	}
	
	/**
	 * Use disEqualitySet to check if there exist contradiction in the graph.
	 *
	 * @return true if there is contradiction
	 */
	boolean checkContradiction() {

		for (final VPDomainSymmetricPair<VPNodeIdentifier> disEqPair : mDisEqualitySet) {
			if (getEqGraphNode(disEqPair.getFirst()).find()
					.equals(getEqGraphNode(disEqPair.getSecond()).find())) {
				return true;
			}
		}
		return false;
	}
}
