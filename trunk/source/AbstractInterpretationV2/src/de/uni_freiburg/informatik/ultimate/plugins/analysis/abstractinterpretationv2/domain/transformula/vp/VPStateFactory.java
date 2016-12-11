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

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class VPStateFactory {
	
	private final VPDomain mDomain;
//	private final VPStateBottom mBottomState;
	private final Map<Set<IProgramVar>, VPStateBottom> mBottomStates = new HashMap<>();

	public VPStateFactory(VPDomain vpdomain) {
		mDomain = vpdomain;
//		mBottomState = new VPStateBottom(vpdomain);
	}
	
	VPStateBuilder createEmptyStateBuilder() {
		
		VPStateBuilder builder = new VPStateBuilder(mDomain);
		
		/*
		 * When all EqGraphNodes for the VPState have been created, we can set their
		 * initCcpar and initCcchild fields
		 */
		for (EqGraphNode egn : builder.getEqNodeToEqGraphNodeMap().values()) {
			egn.setupNode(builder.getEqNodeToEqGraphNodeMap());
		}
		
		/*
		 * Generate disequality set for constants
		 */
		Set<EqNode> literalSet = mDomain.getLiteralEqNodes();
		Set<VPDomainSymmetricPair<EqNode>> disEqualitySet = new HashSet<>();
		for (EqNode node1 : literalSet) {
			for (EqNode node2 : literalSet) {
				if (!node1.equals(node2)) {
					disEqualitySet.add(new VPDomainSymmetricPair<EqNode>(node1, node2));
				}
			}
		}
		builder.setDisEqualites(disEqualitySet);
		
		/*
		 * The set of tracked variables (as exposed to the fixpointengine) is empty, initially.
		 */
		Set<IProgramVar> vars = new HashSet<>();
		builder.setVars(vars);

		builder.setIsTop(true);

		return builder;
	}
	
	public VPStateBottom getBottomState(Set<IProgramVar> set) {
		VPStateBottom result = mBottomStates.get(set);
		if (result == null) {
			VPStateBottomBuilder builder = new VPStateBottomBuilder(mDomain);
			builder.addVariables(set);
			result = builder.build();
			mBottomStates.put(set, result);
		}
		return result;
	}
	
	public VPState getTopState(Set<IProgramVar> vars) {
		return createEmptyStateBuilder().setVars(vars).build();
	}

	public VPStateBuilder copy(VPState originalState) {
		if (originalState.isBottom()) {
			return new VPStateBottomBuilder(mDomain).setVars(originalState.getVariables());
		}
		
		final VPStateBuilder builder = createEmptyStateBuilder();
		
		for (EqNode eqNode : mDomain.getTermToEqNodeMap().values()) {
			EqGraphNode newGraphNode = builder.getEqNodeToEqGraphNodeMap().get(eqNode);
			EqGraphNode oldGraphNode = originalState.getEqNodeToEqGraphNodeMap().get(eqNode);
			newGraphNode.copyFields(oldGraphNode, builder.getEqNodeToEqGraphNodeMap());
			assert !originalState.isTop() || newGraphNode.getRepresentative() == newGraphNode;
		}
		
		for (VPDomainSymmetricPair<EqNode> pair : originalState.getDisEqualitySet()) {
			builder.getDisEqualitySet().add(pair);
			assert !originalState.isTop() || (pair.mFst.isLiteral() && pair.mSnd.isLiteral()) : 
				"The only disequalites in a top state are between constants";
		}
		
		builder.setVars(new HashSet<>(originalState.getVariables()));
		
		builder.setIsTop(originalState.isTop());

		assert builder.mVars.equals(originalState.getVariables());
		return builder;
	}
	
	
	public Set<VPState> addEquality(final EqNode eqNode1, final EqNode eqNode2, final Set<VPState> originalStates) {
		Set<VPState> result = new HashSet<>();
		
		for (VPState originalState : originalStates) {
			result.addAll(addEquality(eqNode1, eqNode2, originalState));
		}
		return result;
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
		if (originalState.isBottom()) {
			return Collections.singleton(originalState);
		}
		VPStateBuilder builder = copy(originalState);
		EqGraphNode gn1 = builder.getEqNodeToEqGraphNodeMap().get(eqNode1);
		EqGraphNode gn2 = builder.getEqNodeToEqGraphNodeMap().get(eqNode2);
		builder.merge(gn1, gn2);
		builder.setIsTop(false);
		boolean contradiction = builder.checkContradiction();
		if (contradiction) {
			return Collections.singleton(
					new VPStateBottomBuilder(mDomain)
						.setVars(originalState.getVariables()).build());
		}
		
		VPState resultState = builder.build();
		
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

		assert VPDomainHelpers.allStatesHaveSameVariables(resultStates);
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

	public Set<VPState> addDisEquality(EqNode n1, EqNode n2, Set<VPState> originalStates) {
		Set<VPState> result = new HashSet<>();
		
		for (VPState originalState : originalStates) {
			result.addAll(addDisEquality(n1, n2, originalState));
		}

		return result;
	}

	public Set<VPState> addDisEquality(EqNode n1, EqNode n2, VPState originalState) {
		if (originalState.isBottom()) {
			return Collections.singleton(originalState);
		}
		
		
		VPStateBuilder builder = copy(originalState);
		
		EqGraphNode gn1 = builder.getEqNodeToEqGraphNodeMap().get(n1);
		EqGraphNode gn2 = builder.getEqNodeToEqGraphNodeMap().get(n2);

		EqGraphNode gn1Find = builder.find(gn1);
		EqGraphNode gn2Find = builder.find(gn2);
		
		/*
		 * check if the disequality introduces a contradiction, return bottom in that case
		 */
		if (gn1Find.equals(gn2Find)) {
			return Collections.singleton(getBottomState(originalState.getVariables()));
		}
		
		/*
		 * no contradiction --> introduce disequality
		 */
		builder.addToDisEqSet(gn1Find.eqNode, gn2Find.eqNode);
		
		builder.setIsTop(false);
		
		
		/*
		 * propagate disequality to children
		 */
		Set<VPState> result = propagateDisEqualites(builder.build(), gn1Find, gn2Find);

		assert VPDomainHelpers.allStatesHaveSameVariables(result);
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
		result.add(originalStateCopy);
		
		HashRelation<IProgramVarOrConst, List<EqGraphNode>> ccchild1 = originalStateCopy.ccchild(representative1);
		HashRelation<IProgramVarOrConst, List<EqGraphNode>> ccchild2 = originalStateCopy.ccchild(representative2);
		
		for (IProgramVarOrConst arrayId : ccchild1.getDomain()) {
			for (List<EqGraphNode> list1 : ccchild1.getImage(arrayId)) {
				for (List<EqGraphNode> list2 : ccchild2.getImage(arrayId)) {
					Set<VPState> intermediateResult = new HashSet<>(result);
					result = new HashSet<>();
					for (int i = 0; i < list1.size(); i++) {
						EqGraphNode c1 = list1.get(i);
						EqGraphNode c2 = list2.get(i);
						if (originalStateCopy.getDisEqualitySet().contains(
								new VPDomainSymmetricPair<EqNode>(c1.find().eqNode, c2.find().eqNode))){
							continue;
						}
						result.addAll(addDisEquality(c1.eqNode, c2.eqNode, intermediateResult));
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
		if (originalState.isBottom()) {
			return originalState;
		}
		
		
		VPStateBuilder builder = copy(originalState);
		EqGraphNode graphNode = builder.getEqNodeToEqGraphNodeMap().get(node);
		
		// TODO: determine if state becomes top through the havoc!

		// Handling the outgoing edge chain
		final EqGraphNode firstRepresentative = graphNode.getRepresentative();
		EqGraphNode nextRepresentative = firstRepresentative;
		nextRepresentative.getReverseRepresentative().remove(graphNode);
		while (!(nextRepresentative.equals(nextRepresentative.getRepresentative()))) {
			nextRepresentative.getCcpar().removeAll(graphNode.getCcpar());
			for (final Entry<IProgramVarOrConst, List<EqGraphNode>> entry : graphNode.getCcchild().entrySet()) {
				nextRepresentative.getCcchild().removePair(entry.getKey(), entry.getValue());
			}
			nextRepresentative = nextRepresentative.getRepresentative();
		}
		nextRepresentative.getCcpar().removeAll(graphNode.getCcpar());
		HashRelation<IProgramVarOrConst, List<EqGraphNode>> copyOfGraphNodeCcchild = new HashRelation<>();
		for (final Entry<IProgramVarOrConst, List<EqGraphNode>> entry : graphNode.getCcchild().entrySet()) {
			copyOfGraphNodeCcchild.addPair(entry.getKey(), entry.getValue());
		}
		for (final Entry<IProgramVarOrConst, List<EqGraphNode>> entry : copyOfGraphNodeCcchild.entrySet()) {
			nextRepresentative.getCcchild().removePair(entry.getKey(), entry.getValue());
		}

		/*
		 *  Handling the incoming edges (reverseRepresentative).
		 *  Point nodes in reverseRepresentative to the representative of the node that is being havoc.
		 *  For example, y -> x -> z. Havoc x, then we have y -> z
		 *  But if the node that is being havoc is its own representative, 
		 *  then point nodes in reverseRepresentative to one of them.
		 *  For example, y -> x <- z, Havoc x, then we have y -> z or z -> y.
		 */
		EqGraphNode firstReserveRepresentativeNode = null;
		if (!graphNode.getReverseRepresentative().isEmpty()) {
			firstReserveRepresentativeNode = graphNode.getReverseRepresentative().iterator().next();
		}
		for (final EqGraphNode reverseNode : graphNode.getReverseRepresentative()) {
			// first reset the representative of all the reverseRepresentative nodes.
			reverseNode.setRepresentative(reverseNode);
		}
		
		boolean havocNodeIsItsRepresentative = false;
		VPState resultState = builder.build();
		for (final EqGraphNode reverseNode : graphNode.getReverseRepresentative()) {
			// case y -> x <- z
			if (firstRepresentative.equals(graphNode)) {
				havocNodeIsItsRepresentative = true;
				if (graphNode.getReverseRepresentative().size() > 1) {
					assert firstReserveRepresentativeNode != null;
					resultState = disjoinAll(addEquality(reverseNode.eqNode, firstReserveRepresentativeNode.eqNode, resultState));
				}
			} else { // case y -> x -> z
				resultState = disjoinAll(addEquality(reverseNode.eqNode, firstRepresentative.eqNode, resultState));
			}
		}
		
		builder = copy(resultState);
		graphNode = builder.getEqNodeToEqGraphNodeMap().get(node);
		
		/*
		 * Handling the node itself:
		 * First update disequality set.
		 * Then set havoc node to initial.
		 */
		if (havocNodeIsItsRepresentative) {
			Set<VPDomainSymmetricPair<EqNode>> newDisEqualitySet = new HashSet<>();
			for (VPDomainSymmetricPair<EqNode> pair : builder.getDisEqualitySet()) {
				if (pair.contains(graphNode.eqNode)) {
					newDisEqualitySet.add(
							new VPDomainSymmetricPair<EqNode>(pair.getOther(graphNode.eqNode), resultState.find(firstReserveRepresentativeNode).eqNode));
				} else {
					newDisEqualitySet.add(pair);
				}
			}
			builder.setDisEqualites(newDisEqualitySet);
		} else {
			// do nothing: no need to update disequality set, because if x is not representative, then x should not be in disequality set.
		}
//		if (graphNode.getRepresentative().equals(graphNode)) {
//			Set<VPDomainSymmetricPair<EqNode>> newSet = 
//					builder.getDisEqualitySet().stream()
//					.filter(pair -> !pair.contains(node))
//					.collect(Collectors.toSet());
//			builder.setDisEqualites(newSet);
//		}
		graphNode.setNodeToInitial();

		if (node instanceof EqFunctionNode) {
			builder.restorePropagation((EqFunctionNode) node);
		}
		resultState = builder.build();
		
		// also havoc the function nodes which index had been havoc.
		if (!graphNode.getInitCcpar().isEmpty()) {
			for (final EqGraphNode initCcpar : graphNode.getInitCcpar()) {
				resultState = havoc(initCcpar.eqNode, resultState);
			}
		}
		
		/*
		 * havoc all the non-atomic EqNodes which depend on this one
		 */
		if (node instanceof EqAtomicBaseNode) {
			for (EqNonAtomicBaseNode  dependentNode : ((EqAtomicBaseNode) node).getDependentNonAtomicBaseNodes()) {
				resultState = havoc(dependentNode, resultState);
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
		VPState resultState = copy(originalState).build();

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
		VPState resultState = copy(originalState).build();
		for (final IProgramVar var : assignmentVars) {

			if (var.getTerm().getSort().isArraySort()) {
				// assigned to arrays get special treatment..
				continue;
			}

			EqNode node = mDomain.getPreAnalysis().getEqNode(var.getTerm(), Collections.emptyMap());
			
			if (node != null) {
				resultState = havoc(node, resultState);
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
		
		if (first.equals(second)) {
			return Collections.singleton(first);
		}

		if (first.isBottom()) {
			return Collections.singleton(first);
		}
		if (second.isBottom()) {
			return Collections.singleton(second);
		}
		if (first.isTop()) {
			return Collections.singleton(second);
		} else if (second.isTop()) {
			return Collections.singleton(first);
		}

//		VPState conjoinedState = copy(first).build();
		VPStateBuilder builder = copy(first);
		EqNode conStateGraphNode;
		EqNode conStateGraphNodeRe;

		for (VPDomainSymmetricPair<EqNode> otherPair : second.getDisEqualitySet()) {
			builder.getDisEqualitySet()
					.add(new VPDomainSymmetricPair<EqNode>(otherPair.getFirst(), otherPair.getSecond()));
		}

		VPState conjoinedState = builder.build();
		Set<VPState> resultStates = new HashSet<>();
		for (final EqGraphNode otherGraphNode : second.getEqNodeToEqGraphNodeMap().values()) {
			if (!otherGraphNode.getRepresentative().equals(otherGraphNode)) {
				conStateGraphNode = otherGraphNode.eqNode;
				conStateGraphNodeRe = otherGraphNode.getRepresentative().eqNode;
				resultStates.addAll(addEquality(conStateGraphNode, conStateGraphNodeRe, conjoinedState));
			}
		}
		assert VPDomainHelpers.allStatesHaveSameVariables(resultStates);
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
		
			if (first.isTop()) {
				return first;
			}
			if (second.isTop()) {
				return second;
			}
			if (first.isBottom()) {
				return second;
			} 
			if (second.isBottom()) {
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
		VPState resultState = copy(originalState).build();
		resultState = havocArray(firstArray, resultState);

		Set<VPState> resultStates = new HashSet<>();
		for (final EqFunctionNode fnNode1 : mDomain.getArrayIdToEqFnNodeMap()
				.getImage(
						firstArray)) {
			for (final EqFunctionNode fnNode2 : mDomain.getArrayIdToEqFnNodeMap()
					.getImage(
							secondArray)) {
				if (resultState.congruentIgnoreFunctionSymbol(fnNode1, fnNode2)) {
					resultStates = conjoinAll(resultStates, addEquality(fnNode1, fnNode2, resultState));
				}
			}
		}
		if (resultStates.isEmpty()) {
			resultStates.add(resultState);
		}
		return resultStates;
	}

	/**
	 * Conjoins two sets of states (which are implicit disjunctions), and returns a set of states.
	 * Example {A, B, C} , {D, E} becomes {(A /\ D), (A /\ E), (B /\ D), (B /\ E), ...}.
	 * 
	 * @param resultStates
	 * @param addEquality
	 * @return
	 */
	public Set<VPState> conjoinAll(Set<VPState> set1, Set<VPState> set2) {
		Set<VPState> resultStates = new HashSet<>();
		
		for (VPState state1 : set1) {
			for (VPState state2 : set2) {
				// (the result of conjoin is again a disjunction -- that's ok)
				resultStates.addAll(conjoin(state1, state2));
			}
		}
		
		return resultStates;
	}

	public VPState disjoinAll(Set<VPState> resultStates) {
		return resultStates.stream().reduce((s1, s2) -> disjoin(s1,s2)).get();
	}

	public Set<VPState> havoc(EqNode node, Set<VPState> states) {
		Set<VPState> result = new HashSet<>();
		for (VPState state : states) {
			result.add(havoc(node, state));
		}
		return result;
	}
}
