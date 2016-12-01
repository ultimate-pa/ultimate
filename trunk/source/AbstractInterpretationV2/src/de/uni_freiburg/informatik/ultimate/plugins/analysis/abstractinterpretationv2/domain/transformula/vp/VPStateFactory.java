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

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class VPStateFactory {
	
	private final VPDomain mDomain;
	private final VPStateBottom mBottomState;
	private final VPState mTopState;

	public VPStateFactory(VPDomain vpdomain) {
		mDomain = vpdomain;
		mBottomState = new VPStateBottom(vpdomain);
		mTopState = createTopState();
	}
	
	private VPState createTopState() {
		Map<EqNode, EqGraphNode> eqNodeToEqGraphNodeMap = new HashMap<>();
		Set<EqNode> literalSet = new HashSet<>();
		Set<VPDomainSymmetricPair<EqNode>> disEqualitySet = new HashSet<>();
		
		/*
		 * Create fresh EqGraphNodes from EqNodes.
		 */
		for (EqNode eqNode : mDomain.getTermToEqNodeMap().values()) {
			getOrConstructEqGraphNode(eqNode, eqNodeToEqGraphNodeMap);
			if (eqNode.isLiteral()) {
				literalSet.add(eqNode);
			}
		}
		
		/*
		 * Generate disequality set for constants
		 */
		for (EqNode node1 : literalSet) {
			for (EqNode node2 : literalSet) {
				if (!node1.equals(node2)) {
					disEqualitySet.add(new VPDomainSymmetricPair<EqNode>(node1, node2));
				}
			}
		}
		
		return new VPState(eqNodeToEqGraphNodeMap, disEqualitySet, mDomain);
	}
	
	private EqGraphNode getOrConstructEqGraphNode(EqNode eqNode, Map<EqNode, EqGraphNode> eqNodeToEqGraphNode) {
		
		if (eqNodeToEqGraphNode.containsKey(eqNode)) {
			return eqNodeToEqGraphNode.get(eqNode);
		}
		
		final EqGraphNode graphNode = new EqGraphNode(eqNode);
		List<EqGraphNode> argNodes = new ArrayList<>();
		
		if (eqNode instanceof EqFunctionNode) {

			for (EqNode arg : ((EqFunctionNode)eqNode).getArgs()) {
				EqGraphNode argNode = getOrConstructEqGraphNode(arg, eqNodeToEqGraphNode);
				argNode.addToInitCcpar(graphNode);
				argNode.addToCcpar(graphNode);
				argNodes.add(argNode);
			}
			graphNode.addToInitCcchild(argNodes);
			graphNode.getCcchild().addPair(((EqFunctionNode)eqNode).getFunction(), argNodes);
		}
		eqNodeToEqGraphNode.put(eqNode, graphNode);
		return graphNode;
	}
	
	public VPStateBottom getBottomState() {
		return mBottomState;
	}
	
	public VPState getTopState() {
		return mTopState;
	}
	
	public VPState copy(VPState originalState) {
		if (originalState.isTop()) {
			assert mTopState == originalState : "we have more than one top state";
			return originalState;
		}
		
		VPState result = createTopState();
		
		
		for (EqGraphNode gNode : result.getEqNodeToEqGraphNodeMap().values()) {
			gNode.copyFields(originalState.getEqNodeToEqGraphNodeMap().get(gNode.eqNode), result);
		}
		
		for (VPDomainSymmetricPair<EqNode> pair : originalState.getDisEqualitySet()) {
			result.getDisEqualitySet().add(pair);
		}
		
		result.setIsTop(false);

		return result;
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
		VPState resultState = copy(originalState);
		resultState.merge(resultState.getEqNodeToEqGraphNodeMap().get(graphNode1.eqNode), 
				resultState.getEqNodeToEqGraphNodeMap().get(graphNode2.eqNode));
		boolean contradiction = resultState.checkContradiction();
		if (contradiction) {
			return this.getBottomState();
		}
		return resultState;
	}

	public List<VPState> addDisEquality(EqGraphNode n1, EqGraphNode n2, VPState originalState) {
		VPState originalStateCopy = copy(originalState);

		List<VPState> result = new ArrayList<>();
		
		VPStateBottom bottom = this.getBottomState();
		
		/*
		 * check if the disequality introduces a contradiction, return bottom in that case
		 */
		if (originalStateCopy.find(n1).equals(originalStateCopy.find(n2))) {
			return Collections.singletonList(bottom);
		}
		
		/*
		 * no contradiction --> introduce disequality
		 */
		originalStateCopy.addToDisEqSet(n1.eqNode, n2.eqNode);
		
		
		/*
		 * propagate disequality to children
		 */
		HashRelation<IProgramVarOrConst, List<EqGraphNode>> ccchild1 = originalStateCopy.ccchild(n1);
		HashRelation<IProgramVarOrConst, List<EqGraphNode>> ccchild2 = originalStateCopy.ccchild(n2);
		
		for (IProgramVarOrConst arrayId : ccchild1.getDomain()) {
			for (List<EqGraphNode> list1 : ccchild1.getImage(arrayId)) {
				for (List<EqGraphNode> list2 : ccchild2.getImage(arrayId)) {
					for (int i = 0; i < list1.size(); i++) {
						EqGraphNode c1 = list1.get(i);
						EqGraphNode c2 = list2.get(i);
						result.addAll(addDisEquality(c1, c2, originalStateCopy));
					}
				}
			}
		}

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
	public VPState havoc(final EqGraphNode node, final VPState originalState) {
		VPState resultState = copy(originalState);
		EqGraphNode graphNode = resultState.getEqNodeToEqGraphNodeMap().get(node.eqNode);

		// Handling the outgoing edge chain
		EqGraphNode nextRepresentative = graphNode.getRepresentative();
		nextRepresentative.getReverseRepresentative().remove(graphNode);
		while (!(nextRepresentative.equals(nextRepresentative.getRepresentative()))) {
			nextRepresentative.getCcpar().removeAll(graphNode.getCcpar());
			// TODO check if pair is correctly removed.
			for (final Entry<IProgramVarOrConst, List<EqGraphNode>> entry : graphNode.getCcchild().entrySet()) {
				nextRepresentative.getCcchild().removePair(entry.getKey(), entry.getValue());
			}
			nextRepresentative = nextRepresentative.getRepresentative();
		}
		nextRepresentative.getCcpar().removeAll(graphNode.getCcpar());
		for (final Entry<IProgramVarOrConst, List<EqGraphNode>> entry : graphNode.getCcchild().entrySet()) {
			nextRepresentative.getCcchild().removePair(entry.getKey(), entry.getValue());
		}

		// Handling the incoming edges
		for (final EqGraphNode reverseNode : graphNode.getReverseRepresentative()) {
			reverseNode.setRepresentative(reverseNode);
		}

		// Handling the node itself
		graphNode.setNodeToInitial();
		for (final VPDomainSymmetricPair<EqNode> disEqPair : resultState.getDisEqualitySet()) {
			if (disEqPair.getFirst().equals(graphNode.eqNode)) {
				resultState.getDisEqualitySet().remove(disEqPair);
			} else if (disEqPair.getSecond().equals(graphNode.eqNode)) {
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
	public VPState havocArray(final IProgramVarOrConst array, VPState originalState) {
		VPState resultState = copy(originalState);

		for (final EqFunctionNode fnNode : mDomain.getArrayIdToEqFnNodeMap()
				.getImage(array)) {
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
	public VPState havocVariables(final Set<IProgramVar> assignmentVars, VPState originalState) {
		VPState resultState = copy(originalState);
		TermVariable tv;

		for (final IProgramVar var : assignmentVars) {

			tv = var.getTermVariable();
			if (tv.getSort().isArraySort()) {
				// assigned to arrays get special treatment..
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

		if (first.isBottom() || second.isBottom()) {
			return this.getBottomState();
		}

		if (first.isTop()) {
			return second;
		} else if (second.isTop()) {
			return first;
		}

		VPState conjoinedState = copy(first);
		EqGraphNode conStateGraphNode;
		EqGraphNode conStateGraphNodeRe;

		for (VPDomainSymmetricPair<EqNode> otherPair : second.getDisEqualitySet()) {
			conjoinedState.getDisEqualitySet()
					.add(new VPDomainSymmetricPair<EqNode>(otherPair.getFirst(), otherPair.getSecond()));
		}

		for (final EqGraphNode otherGraphNode : second.getEqNodeToEqGraphNodeMap().values()) {
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
		
			if (first.isTop() || second.isTop()) {
				return this.getTopState();
			}
		
			if (first.isBottom()) {
				return second;
			} else if (second.isBottom()) {
				return first;
			}
		
			VPState disjoinedState = copy(first);
			EqGraphNode otherGraphNode;
		
			disjoinedState.clearState();
		
			for (final VPDomainSymmetricPair<EqNode> otherPair : second.getDisEqualitySet()) {
				if (first.getDisEqualitySet().contains(otherPair)) {
					disjoinedState.getDisEqualitySet()
							.add(new VPDomainSymmetricPair<EqNode>(otherPair.getFirst(), otherPair.getSecond()));
				}
			}
		
			for (final EqGraphNode thisGraphNode : first.getEqNodeToEqGraphNodeMap().values()) {
		
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
	public VPState arrayAssignment(final IProgramVarOrConst firstArray, final IProgramVarOrConst secondArray, VPState originalState) {
		VPState resultState = copy(originalState);
		resultState = havocArray(firstArray, resultState);

		for (final EqFunctionNode fnNode1 : mDomain.getArrayIdToEqFnNodeMap()
				.getImage(
						firstArray)) {
			for (final EqFunctionNode fnNode2 : mDomain.getArrayIdToEqFnNodeMap()
					.getImage(
							secondArray)) {
				if (resultState.congruentIgnoreFunctionSymbol(fnNode1, fnNode2)) {
					resultState = addEquality(resultState.getEqNodeToEqGraphNodeMap().get(fnNode1),
							resultState.getEqNodeToEqGraphNodeMap().get(fnNode2), resultState);
				}
			}
		}
		return resultState;
	}
}
