package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

public class VPStateOperations {
	
	private final VPDomain mDomain;

	public VPStateOperations(VPDomain vpdomain) {
		mDomain = vpdomain;
	}
	
	/**
	 * Three steps for adding equality relation into graph: 1) Union two nodes.
	 * 2) Propagate (merge congruence class). 3) Check for contradiction.
	 * 
	 * @param graphNode1
	 * @param graphNode2
	 * @return true if contradiction is met.
	 */
	public VPState addEquality(final EqGraphNode graphNode1, final EqGraphNode graphNode2, final VPState originalState) {
		VPState resultState = originalState.copy();
		resultState.merge(graphNode1, graphNode2);
		boolean contradiction = resultState.checkContradiction();
		if (contradiction) {
			return mDomain.getBottomState();
		}
		return resultState;
	}

	public List<VPState> addDisEquality(EqGraphNode n1, EqGraphNode n2, VPState originalState) {

		List<VPState> result = new ArrayList<>();
		
		VPStateBottom bottom = originalState.getDomain().getBottomState();
		
		/*
		 * check if the disequality introduces a contradiction, return bottom in that case
		 */
		if (originalState.find(n1).equals(originalState.find(n2))) {
			return Collections.singletonList(bottom);
		}
		
		/*
		 * no contradiction --> introduce disequality
		 */
		originalState.addToDisEqSet(n1, n2);
		
		
		/*
		 * propagate disequality to children
		 */
		
		//TODO
	
		
//		Set<List<EqGraphNode>> ccchild1 = originalState.ccchild(n1);
//		Set<List<EqGraphNode>> ccchild2 = originalState.ccchild(n2);
//		
//		List<VPState> stateList = new ArrayList<>();
//		
//		// propagation of disequality
//		for (int i = 0; i < ((EqFunctionNode)n1.eqNode).getArgs().size(); i++) {
//			VPState newState = originalState.copy();
//			stateList.addAll(addDisEquality(n1.getInitCcchild().get(i), n2.getInitCcchild().get(i), newState));
//		}

		return result;
		
	}
	
	/**
	 * To havoc a node. There are three main parts to handle: (1) Handling the
	 * outgoing edge chain. (2) Handling the incoming edges. (3) Handling the
	 * node itself.
	 * 
	 * @param EqGraphNode
	 *            to be havoc
	 */
	public VPState havoc(final EqGraphNode graphNode, final VPState originalState) {
		VPState resultState = originalState.copy();

		// Handling the outgoing edge chain
		EqGraphNode nextRepresentative = graphNode.getRepresentative();
		nextRepresentative.getReverseRepresentative().remove(graphNode);
		while (!(nextRepresentative.equals(nextRepresentative.getRepresentative()))) {
			nextRepresentative.getCcpar().removeAll(graphNode.getCcpar());
			nextRepresentative.getCcchild().removeAll(graphNode.getCcchild());
			nextRepresentative = nextRepresentative.getRepresentative();
		}
		nextRepresentative.getCcpar().removeAll(graphNode.getCcpar());
		nextRepresentative.getCcchild().removeAll(graphNode.getCcchild());

		// Handling the incoming edges
		for (final EqGraphNode reverseNode : graphNode.getReverseRepresentative()) {
			reverseNode.setRepresentative(reverseNode);
		}

		// Handling the node itself
		graphNode.setNodeToInitial();
		for (final VPDomainSymmetricPair<EqGraphNode> disEqPair : resultState.getDisEqualitySet()) {
			if (disEqPair.getFirst().equals(graphNode)) {
				resultState.getDisEqualitySet().remove(disEqPair);
			} else if (disEqPair.getSecond().equals(graphNode)) {
				resultState.getDisEqualitySet().remove(disEqPair);
			}
		}

		if (graphNode.eqNode instanceof EqFunctionNode) {
			resultState.restorePropagation((EqFunctionNode) graphNode.eqNode);
		}

		// also havoc the function nodes which index had been havoc.
		if (!graphNode.getInitCcpar().isEmpty()) {
			for (final EqGraphNode initCcpar : graphNode.getInitCcpar()) {
				resultState = havoc(initCcpar, resultState);
			}
		}
		return resultState;
	}
	
	/**
	 * To havoc an array. All the element in this array will be havoc.
	 * 
	 * @param term
	 */
	public VPState havocArray(final Term term, VPState originalState) {
		assert mDomain.isArray(term);
		VPState resultState = originalState.copy();

		for (final EqFunctionNode fnNode : mDomain.getArrayIdToEqFnNodeMap()
				.getImage(mDomain.getPreAnalysis().getIProgramVarOrConst(term))) {
			resultState = this.havoc(resultState.getEqNodeToEqGraphNodeMap().get(fnNode), resultState);
		}
		return resultState;
	}

	/**
	 * To havoc a set of nodes. If this set contains array, it will not be havoc
	 * here.
	 * 
	 * @param assignmentVars
	 */
	public VPState havocBaseNode(final Set<IProgramVar> assignmentVars, VPState originalState) {
		VPState resultState = originalState.copy();
		TermVariable tv;

		for (final IProgramVar var : assignmentVars) {

			tv = var.getTermVariable();
			if (mDomain.isArray(tv)) {
				continue;
			}

			if (mDomain.getTermToEqNodeMap().containsKey(tv)) {
				assert resultState.getEqNodeToEqGraphNodeMap().containsKey(mDomain.getTermToEqNodeMap().get(tv));
				resultState = havoc(resultState.getEqNodeToEqGraphNodeMap().get(mDomain.getTermToEqNodeMap().get(tv)), resultState);
			}
		}
		return resultState;
	}
	
		/**
	 * Join two @VPState. Two steps: 1) Create a new @VPState conjoinedState
	 * based on thisState, add all the edge(equality relation) from otherState
	 * into conjoinedState. 2) Join the disEqualitySet form thisState and
	 * otherState into conjoinedState.
	 * 
	 * @param second
	 * @return conjoinedState
	 */
	public VPState conjoin(VPState first, VPState second) {

		if (first instanceof VPStateBottom || second instanceof VPStateBottom) {
			return mDomain.getBottomState();
		}

		if (first instanceof VPStateTop) {
			return second;
		} else if (second instanceof VPStateTop) {
			return first;
		}

		VPState conjoinedState = first.copy();
		EqGraphNode conStateGraphNode;
		EqGraphNode conStateGraphNodeRe;

		for (VPDomainSymmetricPair<EqGraphNode> otherPair : second.getDisEqualitySet()) {
			conjoinedState.getDisEqualitySet()
					.add(new VPDomainSymmetricPair<EqGraphNode>(otherPair.getFirst(), otherPair.getSecond()));
		}

		for (final EqGraphNode otherGraphNode : second.mEqGraphNodeSet) {
			if (!otherGraphNode.getRepresentative().equals(otherGraphNode)) {
				conStateGraphNode = conjoinedState.getEqNodeToEqGraphNodeMap().get(otherGraphNode.eqNode);
				conStateGraphNodeRe = conjoinedState.getEqNodeToEqGraphNodeMap()
						.get(otherGraphNode.getRepresentative().eqNode);
				conjoinedState = addEquality(conStateGraphNode, conStateGraphNodeRe, conjoinedState);
			}
		}
		return conjoinedState;
	}
	
		/**
		 * Disjoin two @VPState. For each node x, if in both state, x.representative
		 * is the same, say it's i, then newState.addEquality(x, i). If
		 * x.representative is different, say in thisState x.representative = i, in
		 * otherState x.representative = j, then we have another if-else branch: If
		 * otherState.find(x) = otherState.find(i), this means in both state, x and
		 * i are in the same equivalence class, so newState.addEquality(x, i). Else
		 * if thisState.find(x) = thisState.find(j), this means in both state, x and
		 * j are in the same equivalence class, so newState.addEquality(x, j).
		 * 
		 * @param second
		 * @return disjoinedState
		 */
		public VPState disjoin(final VPState first, final VPState second) {
		
			if (first instanceof VPStateTop || second instanceof VPStateTop) {
				return mDomain.getTopState();
			}
		
			if (first instanceof VPStateBottom) {
				return second;
			} else if (second instanceof VPStateBottom) {
				return first;
			}
		
			VPState disjoinedState = first.copy();
			EqGraphNode otherGraphNode;
		
			disjoinedState.clearState();
		
			for (final VPDomainSymmetricPair<EqGraphNode> otherPair : second.getDisEqualitySet()) {
				if (first.getDisEqualitySet().contains(otherPair)) {
					disjoinedState.getDisEqualitySet()
							.add(new VPDomainSymmetricPair<EqGraphNode>(otherPair.getFirst(), otherPair.getSecond()));
				}
			}
		
			for (final EqGraphNode thisGraphNode : first.mEqGraphNodeSet) {
		
				otherGraphNode = second.getEqNodeToEqGraphNodeMap().get(thisGraphNode.eqNode);
		
				EqGraphNode thisNodeRepresentative = thisGraphNode.getRepresentative();
				EqGraphNode otherNodeRepresentative = otherGraphNode.getRepresentative();
		
				if (thisNodeRepresentative.equals(otherNodeRepresentative)) {
					disjoinedState = addEquality(
							disjoinedState.getEqNodeToEqGraphNodeMap().get(thisGraphNode.eqNode),
							disjoinedState.getEqNodeToEqGraphNodeMap().get(thisNodeRepresentative.eqNode),
							disjoinedState);
				} else {
		
					if (first.find(otherGraphNode)
							.equals(first.find(second.getEqNodeToEqGraphNodeMap().get(thisNodeRepresentative.eqNode)))) {
						disjoinedState = addEquality(
								disjoinedState.getEqNodeToEqGraphNodeMap().get(thisGraphNode.eqNode),
								disjoinedState.getEqNodeToEqGraphNodeMap().get(thisNodeRepresentative.eqNode),
								disjoinedState);
					} else if (first.find(thisGraphNode)
							.equals(first.find(first.getEqNodeToEqGraphNodeMap().get(otherNodeRepresentative.eqNode)))) {
						disjoinedState = addEquality(
								disjoinedState.getEqNodeToEqGraphNodeMap().get(thisGraphNode.eqNode),
								disjoinedState.getEqNodeToEqGraphNodeMap().get(otherNodeRepresentative.eqNode),
								disjoinedState);
					}
				}
			}
		
			return disjoinedState;
		}

		/**
	 * Updates this state according to the added information that firstArray
	 * equals secondArray. I.e., we ensure that they are equal on all points
	 * that we track.
	 * 
	 * @param firstArray
	 * @param secondArray
	 */
	public VPState arrayAssignment(final Term firstArray, final Term secondArray, VPState originalState) {
		VPState resultState = originalState.copy();
		resultState = havocArray(firstArray, resultState);

		for (final EqFunctionNode fnNode1 : mDomain.getArrayIdToEqFnNodeMap()
				.getImage(
						mDomain.getPreAnalysis().getIProgramVarOrConst(firstArray))) {
			for (final EqFunctionNode fnNode2 : mDomain.getArrayIdToEqFnNodeMap()
					.getImage(
							mDomain.getPreAnalysis().getIProgramVarOrConst(secondArray))) {
				if (resultState.congruentIgnoreFunctionSymbol(fnNode1, fnNode2)) {
					resultState = addEquality(resultState.getEqNodeToEqGraphNodeMap().get(fnNode1),
							resultState.getEqNodeToEqGraphNodeMap().get(fnNode2), resultState);
				}
			}
		}
		return resultState;
	}
}
