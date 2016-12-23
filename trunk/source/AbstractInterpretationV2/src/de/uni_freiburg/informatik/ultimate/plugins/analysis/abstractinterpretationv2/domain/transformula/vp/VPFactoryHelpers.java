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
	public static <STATE extends IVPStateOrTfState<NODEID, ARRAYID>, NODEID extends IEqNodeIdentifier<ARRAYID>, ARRAYID> 
		Set<STATE> propagateDisEqualites(
			STATE originalStateCopy, 
			EqGraphNode<NODEID, ARRAYID> representative1, 
			EqGraphNode<NODEID, ARRAYID> representative2,
			IVPFactory<STATE, NODEID, ARRAYID> factory) {
		factory.getBenchmark().unpause(VPSFO.propagateDisEqualitiesClock);
		if (factory.isDebugMode()) {
			factory.getLogger().debug("VPFactoryHelpers: propagateDisEqualities(..)");
		}
		
		Set<STATE> result = new HashSet<>();
		result.add(originalStateCopy);
		
		HashRelation<ARRAYID, List<EqGraphNode<NODEID, ARRAYID>>> ccchild1 = representative1.find().getCcchild();
		HashRelation<ARRAYID, List<EqGraphNode<NODEID, ARRAYID>>> ccchild2 = representative2.find().getCcchild();
		
		for (ARRAYID arrayId : ccchild1.getDomain()) {
			for (List<EqGraphNode<NODEID, ARRAYID>> list1 : ccchild1.getImage(arrayId)) {
				for (List<EqGraphNode<NODEID, ARRAYID>> list2 : ccchild2.getImage(arrayId)) {
					Set<STATE> intermediateResult = new HashSet<>(result);
					result = new HashSet<>();
					for (int i = 0; i < list1.size(); i++) {
						EqGraphNode<NODEID, ARRAYID> c1 = list1.get(i);
						EqGraphNode<NODEID, ARRAYID> c2 = list2.get(i);
						if (originalStateCopy.containsDisEquality(c1.find().nodeIdentifier, c2.find().nodeIdentifier)) {
							continue;
						}
						factory.getBenchmark().stop(VPSFO.propagateDisEqualitiesClock);
						result.addAll(addDisEquality(c1.nodeIdentifier, c2.nodeIdentifier, intermediateResult, factory));
						factory.getBenchmark().unpause(VPSFO.propagateDisEqualitiesClock);
					}
				}
			}
		}
		
		if (result.isEmpty()) {
			// no propagations -- return the input state
			factory.getBenchmark().stop(VPSFO.propagateDisEqualitiesClock);
			return Collections.singleton(originalStateCopy);
		}
		factory.getBenchmark().stop(VPSFO.propagateDisEqualitiesClock);
		return result;
	}
	
	public static <T extends IVPStateOrTfState<NODEID, ARRAYID>, NODEID extends IEqNodeIdentifier<ARRAYID>, ARRAYID> Set<T>  addDisEquality(
			NODEID n1, NODEID n2, Set<T> originalStates, IVPFactory<T, NODEID, ARRAYID> factory) {
		Set<T> result = new HashSet<>();
		if (factory.isDebugMode()) {
			factory.getLogger().debug("VPFactoryHelpers: addDisEquality(..)");
		}
		
		for (T originalState : originalStates) {
			result.addAll(addDisEquality(n1, n2, originalState, factory));
		}

		return result;
	}
	
	public static <T extends IVPStateOrTfState<NODEID, ARRAYID>, NODEID extends IEqNodeIdentifier<ARRAYID>, ARRAYID> Set<T> 
			addDisEquality(NODEID i1, NODEID i2, T originalState, IVPFactory<T, NODEID, ARRAYID> factory) {
		if (factory.isDebugMode()) {
			factory.getLogger().debug("VPFactoryHelpers: addDisEquality(..)");
		}
		if (originalState.isBottom()) {
			return Collections.singleton(originalState);
		}

		IVPStateOrTfStateBuilder<T, NODEID, ARRAYID> builder = factory.copy(originalState);
		
		EqGraphNode<NODEID, ARRAYID> gn1 = builder.getEqGraphNode(i1);
		EqGraphNode<NODEID, ARRAYID> gn2 = builder.getEqGraphNode(i2);

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
	 * @param node2
	 * @return true if contradiction is met.
	 */
	public static <T extends IVPStateOrTfState<NODEID, ARRAYID>, NODEID extends IEqNodeIdentifier<ARRAYID>, ARRAYID> Set<T> 
			addEquality(final NODEID node1, 
					final NODEID node2, 
					final T originalState, 
					IVPFactory<T, NODEID, ARRAYID> factory) {
		factory.getBenchmark().unpause(VPSFO.addEqualityClock);
		if (factory.isDebugMode()) {
			factory.getLogger().debug("VPFactoryHelpers: addEquality(" + node1 + ", " + node2 + ", " + "..." + ")");
		}
		if (originalState.isBottom()) {
			factory.getBenchmark().stop(VPSFO.addEqualityClock);
			return Collections.singleton(originalState);
		}
		
		if (node1 == node2 || node1.equals(node2)) {
			factory.getBenchmark().stop(VPSFO.addEqualityClock);
			return Collections.singleton(originalState);
		}
		
		IVPStateOrTfStateBuilder<T, NODEID, ARRAYID> builder = factory.copy(originalState);

		EqGraphNode<NODEID, ARRAYID> gn1 = builder.getEqGraphNode(node1);
		EqGraphNode<NODEID, ARRAYID> gn2 = builder.getEqGraphNode(node2);
		if (gn1.find() == gn2.find()) {
			// the given identifiers are already equal in the originalState
			factory.getBenchmark().stop(VPSFO.addEqualityClock);
			return Collections.singleton(originalState);
		}

		builder.merge(gn1, gn2);
		builder.setIsTop(false);
		boolean contradiction = builder.checkContradiction();
		if (contradiction) {
			Set<T> result = Collections.singleton(
					factory.getBottomState(originalState.getVariables()));
			assert result.stream().filter(element -> element == null).count() == 0;
			factory.getBenchmark().stop(VPSFO.addEqualityClock);
			return result;
		}
		
		T resultState = builder.build();
		
		/**
		 * Propagate disequalites
		 */
		Set<T> resultStates = new HashSet<>();
		for (NODEID other : originalState.getDisequalities(gn1.nodeIdentifier)) {
			factory.getBenchmark().stop(VPSFO.addEqualityClock);
			resultStates.addAll(
					propagateDisEqualites(
							resultState, gn1, resultState.getEqGraphNode(other), factory));
			factory.getBenchmark().unpause(VPSFO.addEqualityClock);
		}
		for (NODEID other : originalState.getDisequalities(gn2.nodeIdentifier)) {
			factory.getBenchmark().stop(VPSFO.addEqualityClock);
			resultStates.addAll(
					propagateDisEqualites(
							resultState, gn2, resultState.getEqGraphNode(other), factory));
			factory.getBenchmark().unpause(VPSFO.addEqualityClock);
		}
	
		if (resultStates.isEmpty()) {
			assert resultState != null;
			factory.getBenchmark().stop(VPSFO.addEqualityClock);
			return Collections.singleton(resultState);
		}

//		assert VPDomainHelpers.allStatesHaveSameVariables(resultStates);
		assert resultStates.stream().filter(element -> element == null).count() == 0;
		factory.getBenchmark().stop(VPSFO.addEqualityClock);
		return resultStates;
	}

	public static <T extends IVPStateOrTfState<NODEID, ARRAYID>, NODEID extends IEqNodeIdentifier<ARRAYID>, ARRAYID> Set<T> addEquality(
			final NODEID node1, 
			final NODEID node2, 
			final Set<T> originalStates, 
			IVPFactory<T, NODEID, ARRAYID> factory) {
		if (factory.isDebugMode()) {
			factory.getLogger().debug("VPFactoryHelpers: addEquality(" + node1 + ", " + node2 + ", " 
					+ "..."  + ") -- " + originalStates.size() + " input states");
		}
		
		if (node1 == node2 || node1.equals(node2)) {
			return originalStates;
		}

		Set<T> result = new HashSet<>();
		
		for (T originalState : originalStates) {
			result.addAll(addEquality(node1, node2, originalState, factory));
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
	public static <T extends IVPStateOrTfState<NODEID, ARRAYID>, NODEID extends IEqNodeIdentifier<ARRAYID>, ARRAYID> T disjoin(final T first, final T second, IVPFactory<T, NODEID, ARRAYID> factory) {
		if (factory.isDebugMode()) {
			factory.getLogger().debug("VPFactoryHelpers: disjoin(..)");
		}

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
	
		IVPStateOrTfStateBuilder<T, NODEID, ARRAYID> builder = 
				factory.createEmptyStateBuilder(first instanceof VPTfState ? ((VPTfState) first).getTransFormula() : null);
		
		/**
		 * the disjoined state contains the disequalities that both first and second contain. (i.e. intersection)
		 */
		Set<VPDomainSymmetricPair<NODEID>> newDisequalities = new HashSet<>(first.getDisEqualities());
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
		for (final EqGraphNode<NODEID, ARRAYID> firstGraphNode : first.getAllEqGraphNodes()) {
			
			if (firstGraphNode.getRepresentative() == firstGraphNode) {
				// no edge
				continue;
			}
	
			EqGraphNode<NODEID, ARRAYID> firstGraphNodeInSecondState = second.getEqGraphNode(firstGraphNode.nodeIdentifier);
			EqGraphNode<NODEID, ARRAYID> firstGraphNodeRepresentativeInSecondState = second.getEqGraphNode(
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

	public static <T extends IVPStateOrTfState<NODEID, ARRAYID>, NODEID extends IEqNodeIdentifier<ARRAYID>, ARRAYID> T disjoinAll(Set<T> resultStates, IVPFactory<T, NODEID, ARRAYID> factory) {
		if (factory.isDebugMode()) {
			factory.getLogger().debug("VPFactoryHelpers: disjoinAll(..) -- " + resultStates.size() + " input states"); 
		}
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
	public static <T extends IVPStateOrTfState<NODEID, ARRAYID>, NODEID extends IEqNodeIdentifier<ARRAYID>, ARRAYID> 
			Set<T> conjoin(T first, T second, IVPFactory<T, NODEID, ARRAYID> factory) {
		factory.getBenchmark().unpause(VPSFO.conjoinOverallClock);
		if (factory.isDebugMode()) {
			factory.getLogger().debug("VPFactoryHelpers: conjoin(..)");
		}

		if (first.equals(second)) {
			factory.getBenchmark().pause(VPSFO.conjoinOverallClock);
			return Collections.singleton(first);
		}

		if (first.isBottom()) {
			factory.getBenchmark().pause(VPSFO.conjoinOverallClock);
			return Collections.singleton(first);
		}
		if (second.isBottom()) {
			factory.getBenchmark().pause(VPSFO.conjoinOverallClock);
			return Collections.singleton(second);
		}
		if (first.isTop()) {
			factory.getBenchmark().pause(VPSFO.conjoinOverallClock);
			return Collections.singleton(second);
		} else if (second.isTop()) {
			factory.getBenchmark().pause(VPSFO.conjoinOverallClock);
			return Collections.singleton(first);
		}

		IVPStateOrTfStateBuilder<T, NODEID, ARRAYID> builder = factory.copy(first);
		
		builder.addDisEqualites(second.getDisEqualities());

		T conjoinedState = builder.build();

		Set<T> resultStates = new HashSet<>();
		resultStates.add(conjoinedState);
		for (final EqGraphNode<NODEID, ARRAYID> otherGraphNode : second.getAllEqGraphNodes()) {
			if (otherGraphNode.getRepresentative().equals(otherGraphNode)) {
				// no (outgoing) equality edge here..
				continue;
			}
			NODEID conStateGraphNode = otherGraphNode.nodeIdentifier;
			NODEID conStateGraphNodeRe = otherGraphNode.getRepresentative().nodeIdentifier;
			resultStates.addAll(
					conjoinAll(
							addEquality(conStateGraphNode, conStateGraphNodeRe, conjoinedState, factory), 
							resultStates, 
							factory));
		}
//		assert VPDomainHelpers.allStatesHaveSameVariables(resultStates);
		assert !resultStates.isEmpty();
		factory.getBenchmark().pause(VPSFO.conjoinOverallClock);
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
	public static <T extends IVPStateOrTfState<NODEID, ARRAYID>, NODEID extends IEqNodeIdentifier<ARRAYID>, ARRAYID> Set<T> conjoinAll(
			Set<T> set1, Set<T> set2, IVPFactory<T, NODEID, ARRAYID> factory) {
		if (factory.isDebugMode()) {
			factory.getLogger().debug("VPFactoryHelpers: conjoinAll(..) -- " + set1.size() + " and " + set2.size() + " input states");
		}
		Set<T> resultStates = new HashSet<>();
		
		for (T state1 : set1) {
			for (T state2 : set2) {
				// (the result of conjoin is again a disjunction -- that's ok)
				resultStates.addAll(conjoin(state1, state2, factory));
			}
		}
		assert !resultStates.isEmpty();
		return resultStates;
	}
	
	public static <T extends IVPStateOrTfState<NODEID, ARRAYID>, NODEID extends IEqNodeIdentifier<ARRAYID>, ARRAYID> Set<T> conjoinAll(
			List<Set<T>> sets, IVPFactory<T, NODEID, ARRAYID> factory) {
		if (factory.isDebugMode()) {
			factory.getLogger().debug("VPFactoryHelpers: conjoinAll(..) -- " + sets.size() + " sets of input states");
		}
		Set<T> result = sets.stream().reduce((set1, set2) -> conjoinAll(set1, set2, factory)).get();
		assert result != null;
		assert !result.isEmpty();
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
	public static <T extends IVPStateOrTfState<NODEID, ARRAYID>, NODEID extends IEqNodeIdentifier<ARRAYID>, ARRAYID> Set<T> arrayEquality(
			final ARRAYID firstArray, final ARRAYID secondArray, 
			T originalState, IVPFactory<T, NODEID, ARRAYID> factory) {
		if (factory.isDebugMode()) {
			factory.getLogger().debug("VPFactoryHelpers: arrayEquality(..)");
		}
		return arrayEqualityWithException(firstArray, secondArray, null, null, originalState, factory);
	}
	
	public static <T extends IVPStateOrTfState<NODEID, ARRAYID>, NODEID extends IEqNodeIdentifier<ARRAYID>, ARRAYID> 
					Set<T> arrayEqualityWithException(
			ARRAYID firstArray,
			ARRAYID secondArray, 
			NODEID exceptionArrayNode, 
			NODEID exceptionValueNode,
			T state, 
			IVPFactory<T, NODEID, ARRAYID> factory) {
		if (factory.isDebugMode()) {
			factory.getLogger().debug("VPFactoryHelpers: arrayEqualityWithException(..)");
		}
		assert (exceptionArrayNode == null) == (exceptionValueNode == null);
		T resultState = factory.copy(state).build();

		Set<T> resultStates = new HashSet<>();
		resultStates.add(resultState);
		for (final NODEID fnNode1 : factory.getFunctionNodesForArray(resultState, firstArray)) {
			for (final NODEID fnNode2 : factory.getFunctionNodesForArray(resultState, secondArray)) {
				EqGraphNode<NODEID, ARRAYID> gn1 = resultState.getEqGraphNode(fnNode1);
				EqGraphNode<NODEID, ARRAYID> gn2 = resultState.getEqGraphNode(fnNode2);
				
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
	public static <NODEID extends IEqNodeIdentifier<ARRAYID>, ARRAYID> boolean congruentIgnoreFunctionSymbol(final EqGraphNode<NODEID, ARRAYID> fnNode1, final EqGraphNode<NODEID, ARRAYID> fnNode2) {
		//		assert fnNode1.getArgs() != null && fnNode2.getArgs() != null;
		//		assert fnNode1.getArgs().size() == fnNode2.getArgs().size();
		assert fnNode1.nodeIdentifier.isFunction();
		assert fnNode2.nodeIdentifier.isFunction();
	
		for (int i = 0; i < fnNode1.getInitCcchild().size(); i++) {
			final EqGraphNode<NODEID, ARRAYID> fnNode1Arg = fnNode1.getInitCcchild().get(i);
			final EqGraphNode<NODEID, ARRAYID> fnNode2Arg = fnNode2.getInitCcchild().get(i);
			if (!fnNode1Arg.find().equals(fnNode2Arg.find())) {
				return false;
			}
		}
		return true;
	}
}
