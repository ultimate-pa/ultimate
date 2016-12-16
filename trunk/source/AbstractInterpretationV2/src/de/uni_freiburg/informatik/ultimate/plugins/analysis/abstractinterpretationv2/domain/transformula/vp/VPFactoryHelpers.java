package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.List;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

import javax.lang.model.type.ExecutableType;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class VPFactoryHelpers {

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
	public static <T extends IVPStateOrTfState> Set<T> propagateDisEqualites(
			T originalStateCopy, 
			EqGraphNode representative1, 
			EqGraphNode representative2,
			IVPFactory<T> factory) {
//		assert representative1.getRepresentative() == representative1
//				&& representative2.getRepresentative() == representative2;
//		assert !representative1.equals(representative2);
		Set<T> result = new HashSet<>();
		result.add(originalStateCopy);
		
		HashRelation<VPArrayIdentifier, List<EqGraphNode>> ccchild1 = representative1.find().getCcchild();
		HashRelation<VPArrayIdentifier, List<EqGraphNode>> ccchild2 = representative2.find().getCcchild();
		
		for (VPArrayIdentifier arrayId : ccchild1.getDomain()) {
			for (List<EqGraphNode> list1 : ccchild1.getImage(arrayId)) {
				for (List<EqGraphNode> list2 : ccchild2.getImage(arrayId)) {
					Set<T> intermediateResult = new HashSet<>(result);
					result = new HashSet<>();
					for (int i = 0; i < list1.size(); i++) {
						EqGraphNode c1 = list1.get(i);
						EqGraphNode c2 = list2.get(i);
						if (originalStateCopy.containsDisEquality(c1.find().nodeIdentifier, c2.find().nodeIdentifier)) {
							continue;
						}
						result.addAll(addDisEquality(c1.nodeIdentifier, c2.nodeIdentifier, intermediateResult, factory));
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
	
	public static <T extends IVPStateOrTfState> Set<T>  addDisEquality(
			VPNodeIdentifier n1, VPNodeIdentifier n2, Set<T> originalStates, IVPFactory<T> factory) {
		Set<T> result = new HashSet<>();
		
		for (T originalState : originalStates) {
			result.addAll(addDisEquality(n1, n2, originalState, factory));
		}

		return result;
	}
	
	public static <T extends IVPStateOrTfState> Set<T> 
			addDisEquality(VPNodeIdentifier i1, VPNodeIdentifier i2, T originalState, IVPFactory<T> factory) {
		if (originalState.isBottom()) {
			return Collections.singleton(originalState);
		}

		IVPStateOrTfStateBuilder<T> builder = factory.copy(originalState);
		
		EqGraphNode gn1 = builder.getEqGraphNode(i1);
		EqGraphNode gn2 = builder.getEqGraphNode(i2);

		/*
		 * check if the disequality introduces a contradiction, return bottom in that case
		 */
		if (gn1.find().equals(gn2.find())) {
			return Collections.singleton(factory.getBottomState(originalState.getVariables()));
		}
		
		/*
		 * no contradiction --> introduce disequality
		 */
		builder.addDisEquality(gn1.find().nodeIdentifier, gn2.find().nodeIdentifier);
		
		builder.setIsTop(false);
		
		/*
		 * propagate disequality to children
		 */
		Set<T> result = propagateDisEqualites(builder.build(), gn1.find(), gn2.find(), factory);

//		assert VPDomainHelpers.allStatesHaveSameVariables(result);
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
	public static <T extends IVPStateOrTfState> Set<T> 
			addEquality(final VPNodeIdentifier eqNode1, 
					final VPNodeIdentifier eqNode2, 
					final T originalState, 
					IVPFactory<T> factory) {
		if (originalState.isBottom()) {
			return Collections.singleton(originalState);
		}
		IVPStateOrTfStateBuilder<T> builder = factory.copy(originalState);

		EqGraphNode gn1 = builder.getEqGraphNode(eqNode1);
		EqGraphNode gn2 = builder.getEqGraphNode(eqNode2);
		if (gn1.find() == gn2.find()) {
			// the given identifiers are already equal in the originalState
			return Collections.singleton(originalState);
		}

		builder.merge(gn1, gn2);
		builder.setIsTop(false);
		boolean contradiction = builder.checkContradiction();
		if (contradiction) {
			return Collections.singleton(
					factory.getBottomState(originalState.getVariables()));
		}
		
		T resultState = builder.build();
		
		/**
		 * Propagate disequalites
		 */
		Set<T> resultStates = new HashSet<>();
		for (VPNodeIdentifier other : originalState.getDisequalities(gn1.nodeIdentifier)) {
			resultStates.addAll(
					propagateDisEqualites(
							resultState, gn1, resultState.getEqGraphNode(other), factory));
		}
		for (VPNodeIdentifier other : originalState.getDisequalities(gn2.nodeIdentifier)) {
			resultStates.addAll(
					propagateDisEqualites(
							resultState, gn2, resultState.getEqGraphNode(other), factory));
		}
	
		if (resultStates.isEmpty()) {
			return Collections.singleton(resultState);
		}

//		assert VPDomainHelpers.allStatesHaveSameVariables(resultStates);
		return resultStates;
	}

	public static <T extends IVPStateOrTfState> Set<T> addEquality(
			final VPNodeIdentifier eqNode1, 
			final VPNodeIdentifier eqNode2, 
			final Set<T> originalStates, 
			IVPFactory<T> factory) {
		Set<T> result = new HashSet<>();
		
		for (T originalState : originalStates) {
			result.addAll(addEquality(eqNode1, eqNode2, originalState, factory));
		}
		return result;
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
	public static <T extends IVPStateOrTfState> T disjoin(final T first, final T second, IVPFactory<T> factory) {
	
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
	
		IVPStateOrTfStateBuilder<T> builder = 
				factory.createEmptyStateBuilder(first instanceof VPTfState ? ((VPTfState) first).getTransFormula() : null);
		
		/**
		 * the disjoined state contains the disequalities that both first and second contain. (i.e. intersection)
		 */
		Set<VPDomainSymmetricPair<VPNodeIdentifier>> newDisequalities = new HashSet<>(first.getDisEqualities());
		newDisequalities.retainAll(second.getDisEqualities());
		builder.addDisEqualites(newDisequalities);
		if (!newDisequalities.isEmpty()) {
			builder.setIsTop(false);
		}
		
		/**
		 * the disjoined state has the intersection of the prior state's variables
		 */
		Set<IProgramVar> newVars = new HashSet<>(first.getVariables());
		newVars.retainAll(second.getVariables());
		builder.addVars(newVars);
		
		/**
		 * the disjoined state contains exactly the equalities that both and second contain.(i.e. intersection)
		 * 
		 * algorithmic plan:
		 *  - go through the edges in the equality graph of the "first" state (by asking each node for its representative)
		 *  - when the second state agrees that the nodes on the two ends of the edge are equal, add the equality
		 *    to the result state
		 */
		T disjoinedState = builder.build();
		for (final EqGraphNode firstGraphNode : first.getAllEqGraphNodes()) {
			
			if (firstGraphNode.getRepresentative() == firstGraphNode) {
				// no edge
				continue;
			}
	
			EqGraphNode firstGraphNodeInSecondState = second.getEqGraphNode(firstGraphNode.nodeIdentifier);
			EqGraphNode firstGraphNodeRepresentativeInSecondState = second.getEqGraphNode(
					firstGraphNode.getRepresentative().nodeIdentifier);
			
			if (firstGraphNodeInSecondState.find().equals(firstGraphNodeRepresentativeInSecondState)) {
				Set<T> eqResultStates = addEquality(firstGraphNodeInSecondState.nodeIdentifier, 
						firstGraphNodeRepresentativeInSecondState.nodeIdentifier, 
						disjoinedState, 
						factory);
				assert eqResultStates.size() == 1;
				disjoinedState = eqResultStates.iterator().next();
			}
	
//			EqGraphNode firstNodeRepresentative = firstGraphNode.getRepresentative();
//			EqGraphNode secondNodeRepresentative = secondGraphNode.getRepresentative();
//	
//			if (firstNodeRepresentative.equals(secondNodeRepresentative)) {
//				Set<T> addEq = addEquality(
//						firstGraphNode.nodeIdentifier,
//						firstNodeRepresentative.nodeIdentifier,
//						disjoinedState,
//						factory);
//				assert addEq.size() == 1;
//				disjoinedState = addEq.iterator().next();
//			} else {
//	
//				if (first.find(secondGraphNode.nodeIdentifier)
//						.equals(first.find(second.getEqNodeToEqGraphNodeMap().get(firstNodeRepresentative.eqNode)))) {
//					Set<T> addEq = addEquality(
//							firstGraphNode.nodeIdentifier,
//							firstNodeRepresentative.nodeIdentifier,
//							disjoinedState,
//							factory);
//					assert addEq.size() == 1;
//					disjoinedState = addEq.iterator().next();
//				} else if (first.find(firstGraphNode)
//						.equals(first.find(first.getEqNodeToEqGraphNodeMap().get(secondNodeRepresentative.eqNode)))) {
//					Set<T> addEq = addEquality(
//							firstGraphNode.nodeIdentifier,
//							secondNodeRepresentative.nodeIdentifier,
//							disjoinedState,
//							factory);
//					assert addEq.size() == 1;
//					disjoinedState = addEq.iterator().next();
//				}
//			}
		}
	
		return disjoinedState;
	}

	public static <T extends IVPStateOrTfState> T disjoinAll(Set<T> resultStates, IVPFactory<T> factory) {
		return resultStates.stream().reduce((s1, s2) -> disjoin(s1,s2, factory)).get();
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
	public static <T extends IVPStateOrTfState> Set<T> conjoin(T first, T second, IVPFactory<T> factory) {
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

		IVPStateOrTfStateBuilder<T> builder = factory.copy(first);
		
		builder.addDisEqualites(second.getDisEqualities());

		T conjoinedState = builder.build();

		Set<T> resultStates = new HashSet<>();
		for (final EqGraphNode otherGraphNode : second.getAllEqGraphNodes()) {
			if (otherGraphNode.getRepresentative().equals(otherGraphNode)) {
				// no (outgoing) equality edge here..
				continue;
			}
			VPNodeIdentifier conStateGraphNode = otherGraphNode.nodeIdentifier;
			VPNodeIdentifier conStateGraphNodeRe = otherGraphNode.getRepresentative().nodeIdentifier;
			resultStates.addAll(addEquality(conStateGraphNode, conStateGraphNodeRe, conjoinedState, factory));
		}
//		assert VPDomainHelpers.allStatesHaveSameVariables(resultStates);
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
	public static <T extends IVPStateOrTfState> Set<T> conjoinAll(
			Set<T> set1, Set<T> set2, IVPFactory<T> factory) {
		Set<T> resultStates = new HashSet<>();
		
		for (T state1 : set1) {
			for (T state2 : set2) {
				// (the result of conjoin is again a disjunction -- that's ok)
				resultStates.addAll(conjoin(state1, state2, factory));
			}
		}
		
		return resultStates;
	}
	
	public static <T extends IVPStateOrTfState> Set<T> conjoinAll(
			List<Set<T>> sets, IVPFactory<T> factory) {
		Set<T> result = sets.stream().reduce((set1, set2) -> conjoinAll(set1, set2, factory)).get();
		assert result != null;
		return result;
	}

	/**
	 * Updates this state according to the added information that firstArray
	 * equals secondArray. I.e., we ensure that they are equal on all points
	 * that we track.
	 * 
	 * @param firstArray
	 * @param secondArray
	 */
	public static <T extends IVPStateOrTfState> Set<T> arrayEquality(
			final VPArrayIdentifier firstArray, final VPArrayIdentifier secondArray, 
			T originalState, IVPFactory<T> factory) {
		return arrayEqualityWithException(firstArray, secondArray, null, null, originalState, factory);
	}
	
	public static <T extends IVPStateOrTfState> Set<T> arrayEqualityWithException(
			VPArrayIdentifier firstArray,
			VPArrayIdentifier secondArray, 
			VPNodeIdentifier exceptionArrayNode, 
			VPNodeIdentifier exceptionValueNode,
			T state, 
			IVPFactory<T> factory) {
		assert (exceptionArrayNode == null) == (exceptionValueNode == null);
		T resultState = factory.copy(state).build();

		Set<T> resultStates = new HashSet<>();
		for (final VPNodeIdentifier fnNode1 : factory.getFunctionNodesForArray(resultState, firstArray)) {
			for (final VPNodeIdentifier fnNode2 : factory.getFunctionNodesForArray(resultState, secondArray)) {
				EqGraphNode gn1 = resultState.getEqGraphNode(fnNode1);
				EqGraphNode gn2 = resultState.getEqGraphNode(fnNode2);
				
				if (fnNode1.equals(exceptionArrayNode) || fnNode2.equals(exceptionArrayNode)) {
					// this arrayIndex is excepted -- we will set it to exceptionValueNode instead
					continue;
				}
				
				if (congruentIgnoreFunctionSymbol(gn1, gn2)) {
					resultStates = conjoinAll(
							resultStates, 
							addEquality(fnNode1, fnNode2, resultState, factory), 
							factory);
				}
			}
		}

		if (exceptionArrayNode != null) {
			resultStates = conjoinAll(
					resultStates, 
					addEquality(exceptionArrayNode, exceptionValueNode, resultState, factory), 
					factory);
		}
	
		
		if (resultStates.isEmpty()) {
			resultStates.add(resultState);
		}
		return resultStates;
	}

	/**
	 * Checks if the arguments of the given EqFunctionNodes are all congruent.
	 *
	 * @param fnNode1
	 * @param fnNode2
	 * @return
	 */
	public static boolean congruentIgnoreFunctionSymbol(final EqGraphNode fnNode1, final EqGraphNode fnNode2) {
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
}
