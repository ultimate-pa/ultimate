package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;

public class VPStateBuilder {

	private Set<IProgramVar> mVars;
	private Set<VPDomainSymmetricPair<EqNode>> mDisEqualitySet;
	protected final VPDomain mDomain;
	private boolean mIsTop;
	private EqGraph mEqGraph;
	
	public VPStateBuilder(VPDomain domain) {
		mDomain = domain;
		mEqGraph = new EqGraph();
	}
	
	public VPStateBuilder setVars(Set<IProgramVar> vars) { 
		mVars = vars;
		return this;
	}

	public VPStateBuilder setEqGraphNodes(Map<EqNode, EqGraphNode> map) {
		mEqGraph.mEqNodeToEqGraphNodeMap = map;
		return this;
	}
	
	VPState build() {
		return new VPState(mEqGraph.mEqNodeToEqGraphNodeMap, mDisEqualitySet, mVars, mDomain, mIsTop);
	}

	public VPStateBuilder setDisEqualites(Set<VPDomainSymmetricPair<EqNode>> disEqualitySet) {
		mDisEqualitySet = disEqualitySet;
		return this;
	}

	public Map<EqNode, EqGraphNode> getEqNodeToEqGraphNodeMap() {
		return mEqGraph.getEqNodeToEqGraphNodeMap();
	}

	public Set<VPDomainSymmetricPair<EqNode>> getDisEqualitySet() {
		return mDisEqualitySet;
	}
	
	public VPStateBuilder setIsTop(boolean b) {
		mIsTop = b;
		return this;
	}
	
	public void addToDisEqSet(final EqNode node1, final EqNode node2) {
		getDisEqualitySet().add(new VPDomainSymmetricPair<>(node1, node2));
	}
	
	/**
	 * Returns the representative of a @param node's equivalence class.
	 *
	 * @param node
	 * @return
	 */
	public EqGraphNode find(final EqGraphNode node) {
		return node.find();
	}
	
	/**
	 * Use disEqualitySet to check if there exist contradiction in the graph.
	 *
	 * @return true if there is contradiction
	 */
	boolean checkContradiction() {

		for (final VPDomainSymmetricPair<EqNode> disEqPair : getDisEqualitySet()) {
			if (find(mEqGraph.mEqNodeToEqGraphNodeMap.get(disEqPair.getFirst()))
					.equals(find(mEqGraph.mEqNodeToEqGraphNodeMap.get(disEqPair.getSecond())))) {
				return true;
			}
		}
		return false;
	}
	
	public EqGraph getEqGraph() {
		return mEqGraph;
	}
	
	
	/**
	 * Merge two congruence class. propagation.
	 *
	 * @param i1
	 * @param i2
	 */
	void merge(final EqGraphNode node1, final EqGraphNode node2) {
		if (!find(node1).equals(find(node2))) {
			mEqGraph.union(node1, node2);
			mEqGraph.equalityPropagation(node1, node2);
		}
	}


	void restorePropagation(final EqFunctionNode node) {
	
		final Set<EqFunctionNode> fnNodeSet = mDomain.getArrayIdToEqFnNodeMap().getImage(node.getFunction());
		for (final EqFunctionNode fnNode1 : fnNodeSet) {
			for (final EqFunctionNode fnNode2 : fnNodeSet) {
				if (!fnNode1.equals(fnNode2) && find(getEqNodeToEqGraphNodeMap().get(fnNode1))
						.equals(find(getEqNodeToEqGraphNodeMap().get(fnNode2)))) {
					mEqGraph.equalityPropagation(getEqNodeToEqGraphNodeMap().get(fnNode1),
							getEqNodeToEqGraphNodeMap().get(fnNode2));
				}
			}
		}
	}
	
	public void addVariable(IProgramVar pv) {
		mVars.add(pv);
	}

	public void removeVariable(IProgramVar pv) {
		mVars.add(pv);
	}

	private class EqGraph {
		private Map<EqNode, EqGraphNode> mEqNodeToEqGraphNodeMap;

		/**
		 * Union of two equivalence classes.
		 *
		 * @param node1
		 * @param node2
		 */
		private void union(final EqGraphNode node1, final EqGraphNode node2) {
	
			final EqGraphNode graphNode1Find = find(node1);
			final EqGraphNode graphNode2Find = find(node2);
	
			if (!graphNode1Find.equals(graphNode2Find)) {
				graphNode2Find.addToReverseRepresentative(graphNode1Find);
				graphNode1Find.setRepresentative(graphNode2Find);
				graphNode2Find.addToCcpar(graphNode1Find.getCcpar());
				for (final Entry<IProgramVarOrConst, List<EqGraphNode>> entry : graphNode1Find.getCcchild().entrySet()) {
					graphNode2Find.getCcchild().addPair(entry.getKey(), entry.getValue());
				}
				// graphNode2Find.addToCcchild(graphNode1Find.getCcchild());
			}
		}

		private void equalityPropagation(final EqGraphNode node1, final EqGraphNode node2) {
			final Set<EqGraphNode> p1 = ccpar(node1);
			final Set<EqGraphNode> p2 = ccpar(node2);

			for (final EqGraphNode t1 : p1) {
				for (final EqGraphNode t2 : p2) {
					if (!(find(t1).equals(find(t2))) && congruent(t1, t2)) {
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
			if (!(node1.eqNode instanceof EqFunctionNode) || !(node2.eqNode instanceof EqFunctionNode)) {
				return false;
			}

			final EqFunctionNode fnNode1 = (EqFunctionNode) node1.eqNode;
			final EqFunctionNode fnNode2 = (EqFunctionNode) node2.eqNode;

			if (!(fnNode1.getFunction().equals(fnNode2.getFunction()))) {
				return false;
			}
			return congruentIgnoreFunctionSymbol(fnNode1, fnNode2);
		}
		
		/* Returns the parents of all nodes in @param node's congruence class.
		 *
		 * @param node
		 * @return
		 */
		private Set<EqGraphNode> ccpar(final EqGraphNode node) {
			return find(node).getCcpar();
		}

		public Map<EqNode, EqGraphNode> getEqNodeToEqGraphNodeMap() {
			return mEqNodeToEqGraphNodeMap;
		}
	}

	public void addVariables(Collection<IProgramVar> variables) {
		mVars.addAll(variables);
	}

	public void removeVariables(Collection<IProgramVar> variables) {
		mVars.removeAll(variables);
	}
	
	/**
	 * Checks if the arguments of the given EqFunctionNodes are all congruent.
	 *
	 * @param fnNode1
	 * @param fnNode2
	 * @return
	 */
	boolean congruentIgnoreFunctionSymbol(final EqFunctionNode fnNode1, final EqFunctionNode fnNode2) {
		assert fnNode1.getArgs() != null && fnNode2.getArgs() != null;
		assert fnNode1.getArgs().size() == fnNode2.getArgs().size();

		for (int i = 0; i < fnNode1.getArgs().size(); i++) {
			final EqNode fnNode1Arg = fnNode1.getArgs().get(i);
			final EqNode fnNode2Arg = fnNode2.getArgs().get(i);
			if (!find(getEqNodeToEqGraphNodeMap().get(fnNode1Arg))
					.equals(find(getEqNodeToEqGraphNodeMap().get(fnNode2Arg)))) {
				return false;
			}
		}
		return true;
	}
}
