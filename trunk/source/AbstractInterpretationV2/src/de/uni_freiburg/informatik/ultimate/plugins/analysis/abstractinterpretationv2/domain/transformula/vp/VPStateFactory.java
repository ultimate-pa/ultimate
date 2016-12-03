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
import java.util.stream.Collectors;
import java.util.stream.Stream;
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
		mTopState = createEmptyState().build();
	}
	
	private VPStateBuilder createEmptyState() {
		
		/*
		 * Create fresh EqGraphNodes from EqNodes.
		 */
		Set<EqNode> literalSet = new HashSet<>();
		Map<EqNode, EqGraphNode> eqNodeToEqGraphNodeMap = new HashMap<>();
		for (EqNode eqNode : mDomain.getTermToEqNodeMap().values()) {
			getOrConstructEqGraphNode(eqNode, eqNodeToEqGraphNodeMap);
			if (eqNode.isLiteral()) {
				literalSet.add(eqNode);
			}
		}
		eqNodeToEqGraphNodeMap = Collections.unmodifiableMap(eqNodeToEqGraphNodeMap);
		
		/*
		 * When all EqGraphNodes for the VPState have been created, we can set their
		 * initCcpar and initCcchild fields
		 */
		for (EqGraphNode egn : eqNodeToEqGraphNodeMap.values()) {
			egn.setupNode(eqNodeToEqGraphNodeMap);
		}
		
		/*
		 * Generate disequality set for constants
		 */
		Set<VPDomainSymmetricPair<EqNode>> disEqualitySet = new HashSet<>();
		for (EqNode node1 : literalSet) {
			for (EqNode node2 : literalSet) {
				if (!node1.equals(node2)) {
					disEqualitySet.add(new VPDomainSymmetricPair<EqNode>(node1, node2));
				}
			}
		}
		
		/*
		 * The set of tracked variables (as exposed to the fixpointengine) is empty, initially.
		 */
		Set<IProgramVar> vars = new HashSet<>();
		VPStateBuilder builder = new VPStateBuilder(mDomain)
				.setEqGraphNodes(eqNodeToEqGraphNodeMap)
				.setVars(vars)
				.setDisEqualites(disEqualitySet)
				.setIsTop(true);
		return builder;
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
//				argNode.addToInitCcpar(graphNode);
				argNode.addToCcpar(graphNode);
				argNodes.add(argNode);
			}
//			graphNode.addToInitCcchild(argNodes);
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
		assert !originalState.isBottom();
		assert !originalState.isTop();
		
		VPStateBuilder builder = createEmptyState();
		
		for (EqNode eqNode : mDomain.getTermToEqNodeMap().values()) {
			EqGraphNode newGraphNode = builder.getEqNodeToEqGraphNodeMap().get(eqNode);
			EqGraphNode oldGraphNode = originalState.getEqNodeToEqGraphNodeMap().get(eqNode);
			newGraphNode.copyFields(oldGraphNode, builder.getEqNodeToEqGraphNodeMap());
		}
		
		for (VPDomainSymmetricPair<EqNode> pair : originalState.getDisEqualitySet()) {
			builder.getDisEqualitySet().add(pair);
		}
		
		builder.setIsTop(false);

		return builder.build();
	}
	
	/**
	 * Three steps for adding equality relation into graph: 1) Union two nodes.
	 * 2) Propagate (merge congruence class). 3) Check for contradiction.
	 * 
	 * @param graphNode1
	 * @param eqNode2
	 * @return true if contradiction is met.
	 */
	public Set<VPState> addEquality(final EqNode eqNode1, final EqNode eqNode2, final VPState originalState) {
		VPState resultState = copy(originalState);
		EqGraphNode gn1 = resultState.getEqNodeToEqGraphNodeMap().get(eqNode1);
		EqGraphNode gn2 = resultState.getEqNodeToEqGraphNodeMap().get(eqNode2);
		resultState.merge(gn1, gn2);
		boolean contradiction = resultState.checkContradiction();
		if (contradiction) {
			return Collections.singleton(this.getBottomState());
		}
		
		
		/**
		 * Propagate disequalites
		 */
		Set<VPState> resultStates = new HashSet<>();
		for (EqNode other : getDisEqualites(originalState, gn1.eqNode)) {
			resultStates.addAll(
					propagateDisEqualites(
							resultState, gn1, resultState.getEqNodeToEqGraphNodeMap().get(other)));
		}
		for (EqNode other : getDisEqualites(originalState, gn2.eqNode)) {
			resultStates.addAll(
					propagateDisEqualites(
							resultState, gn2, resultState.getEqNodeToEqGraphNodeMap().get(other)));
		}
	
		if (resultStates.isEmpty()) {
			return Collections.singleton(resultState);
		}
		
		return resultStates;
	}

	private Set<EqNode> getDisEqualites(VPState originalState, EqNode eqNode) {
		Set<EqNode> result = new HashSet<>();
		 for (VPDomainSymmetricPair<EqNode> pair : originalState.getDisEqualitySet()) {
			 if (pair.contains(eqNode)) {
				 result.add(pair.getOther(eqNode));
			 }
		 }
		 return result;
	}

	public Set<VPState> addDisEquality(EqNode n1, EqNode n2, VPState originalState) {
		VPState originalStateCopy = copy(originalState);
		
		EqGraphNode gn1 = originalStateCopy.getEqNodeToEqGraphNodeMap().get(n1);
		EqGraphNode gn2 = originalStateCopy.getEqNodeToEqGraphNodeMap().get(n2);


		VPStateBottom bottom = this.getBottomState();
		
		/*
		 * check if the disequality introduces a contradiction, return bottom in that case
		 */
		if (originalStateCopy.find(gn1).equals(originalStateCopy.find(gn2))) {
			return Collections.singleton(bottom);
		}
		
		/*
		 * no contradiction --> introduce disequality
		 */
		originalStateCopy.addToDisEqSet(n1, n2);
		
		
		/*
		 * propagate disequality to children
		 */
		Set<VPState> result = propagateDisEqualites(originalStateCopy, gn1, gn2);

		return result;
	}

	/**
	 * Takes a preState and two representatives of different equivalence classes.
	 * Under the assumption that a disequality between the equivalence classes has been introduced, propagates
	 * all the disequalities that follow from that disequality.
	 * 
	 * @param originalStateCopy
	 * @param representative1
	 * @param representative2
	 * @return
	 */
	private Set<VPState> propagateDisEqualites(
			VPState originalStateCopy, 
			EqGraphNode representative1, 
			EqGraphNode representative2) {
//		assert representative1.getRepresentative() == representative1
//				&& representative2.getRepresentative() == representative2;
//		assert !representative1.equals(representative2);
		Set<VPState> result = new HashSet<>();
		
		HashRelation<IProgramVarOrConst, List<EqGraphNode>> ccchild1 = originalStateCopy.ccchild(representative1);
		HashRelation<IProgramVarOrConst, List<EqGraphNode>> ccchild2 = originalStateCopy.ccchild(representative2);
		
		for (IProgramVarOrConst arrayId : ccchild1.getDomain()) {
			for (List<EqGraphNode> list1 : ccchild1.getImage(arrayId)) {
				for (List<EqGraphNode> list2 : ccchild2.getImage(arrayId)) {
					for (int i = 0; i < list1.size(); i++) {
						EqGraphNode c1 = list1.get(i);
						EqGraphNode c2 = list2.get(i);
						result.addAll(addDisEquality(c1.eqNode, c2.eqNode, originalStateCopy));
					}
				}
			}
		}
		
		if (result.isEmpty()) {
			// no propagations -- return the input state
			return Collections.singleton(originalStateCopy);
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
	public VPState havoc(final EqNode node, final VPState originalState) {
		VPState resultState = copy(originalState);
		EqGraphNode graphNode = resultState.getEqNodeToEqGraphNodeMap().get(node);

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
				resultState = havoc(initCcpar.eqNode, resultState);
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
			resultState = this.havoc(fnNode, resultState);
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
				resultState = havoc(mDomain.getTermToEqNodeMap().get(tv), resultState);
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
	public Set<VPState> conjoin(VPState first, VPState second) {

		if (first.isBottom() || second.isBottom()) {
			return Collections.singleton(this.getBottomState());
		}

		if (first.isTop()) {
			return Collections.singleton(second);
		} else if (second.isTop()) {
			return Collections.singleton(first);
		}

		VPState conjoinedState = copy(first);
		EqNode conStateGraphNode;
		EqNode conStateGraphNodeRe;

		for (VPDomainSymmetricPair<EqNode> otherPair : second.getDisEqualitySet()) {
			conjoinedState.getDisEqualitySet()
					.add(new VPDomainSymmetricPair<EqNode>(otherPair.getFirst(), otherPair.getSecond()));
		}

		Set<VPState> resultStates = new HashSet<>();
		for (final EqGraphNode otherGraphNode : second.getEqNodeToEqGraphNodeMap().values()) {
			if (!otherGraphNode.getRepresentative().equals(otherGraphNode)) {
				conStateGraphNode = otherGraphNode.eqNode;
				conStateGraphNodeRe = otherGraphNode.getRepresentative().eqNode;
				resultStates.addAll(addEquality(conStateGraphNode, conStateGraphNodeRe, conjoinedState));
			}
		}
		return resultStates;
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
		
			VPStateBuilder builder = new VPStateBuilder(mDomain);
			builder.setIsTop(false);
			
			/**
			 * the disjoined state contains the disequalities that both first and second contain. (i.e. intersection)
			 */
			Set<VPDomainSymmetricPair<EqNode>> newDisequalities = new HashSet<>(first.getDisEqualitySet());
			newDisequalities.retainAll(second.getDisEqualitySet());
			builder.setDisEqualites(newDisequalities);
			
			/**
			 * the disjoined state has the intersection of the prior state's variables
			 */
			Set<IProgramVar> newVars = new HashSet<>(first.getVariables());
			newVars.retainAll(second.getVariables());
			builder.setVars(newVars);
			
			/**
			 * the disjoined state contains exactly the equalities that both and second contain.(i.e. intersection)
			 */
			VPState disjoinedState = builder.build();
			for (final EqGraphNode firstGraphNode : first.getEqNodeToEqGraphNodeMap().values()) {
		
				EqGraphNode secondGraphNode = second.getEqNodeToEqGraphNodeMap().get(firstGraphNode.eqNode);
		
				EqGraphNode firstNodeRepresentative = firstGraphNode.getRepresentative();
				EqGraphNode secondNodeRepresentative = secondGraphNode.getRepresentative();
		
				if (firstNodeRepresentative.equals(secondNodeRepresentative)) {
					Set<VPState> addEq = addEquality(
							firstGraphNode.eqNode,
							firstNodeRepresentative.eqNode,
							disjoinedState);
					assert addEq.size() == 1;
					disjoinedState = addEq.iterator().next();
				} else {
		
					if (first.find(secondGraphNode)
							.equals(first.find(second.getEqNodeToEqGraphNodeMap().get(firstNodeRepresentative.eqNode)))) {
						Set<VPState> addEq = addEquality(
								firstGraphNode.eqNode,
								firstNodeRepresentative.eqNode,
								disjoinedState);
						assert addEq.size() == 1;
						disjoinedState = addEq.iterator().next();
					} else if (first.find(firstGraphNode)
							.equals(first.find(first.getEqNodeToEqGraphNodeMap().get(secondNodeRepresentative.eqNode)))) {
						Set<VPState> addEq = addEquality(
								firstGraphNode.eqNode,
								secondNodeRepresentative.eqNode,
								disjoinedState);
						assert addEq.size() == 1;
						disjoinedState = addEq.iterator().next();
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
	public Set<VPState> arrayEquality(final IProgramVarOrConst firstArray, final IProgramVarOrConst secondArray, VPState originalState) {
		VPState resultState = copy(originalState);
		resultState = havocArray(firstArray, resultState);

		Set<VPState> resultStates = new HashSet<>();
		for (final EqFunctionNode fnNode1 : mDomain.getArrayIdToEqFnNodeMap()
				.getImage(
						firstArray)) {
			for (final EqFunctionNode fnNode2 : mDomain.getArrayIdToEqFnNodeMap()
					.getImage(
							secondArray)) {
				if (resultState.congruentIgnoreFunctionSymbol(fnNode1, fnNode2)) {
					resultStates.addAll(addEquality(fnNode1, fnNode2, resultState));
				}
			}
		}
		return resultStates;
	}
}
