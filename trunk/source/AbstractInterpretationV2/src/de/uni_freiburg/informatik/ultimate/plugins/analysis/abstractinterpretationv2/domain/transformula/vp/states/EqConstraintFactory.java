package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainHelpers;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.IEqFunctionIdentifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class EqConstraintFactory<
			ACTION extends IIcfgTransition<IcfgLocation>, 
			NODE extends IEqNodeIdentifier<NODE, FUNCTION>, 
			FUNCTION extends IEqFunctionIdentifier<FUNCTION>> {

	private EqConstraint<ACTION, NODE, FUNCTION> mBottomConstraint = new EqBottomConstraint<>(this);

	public EqConstraint<ACTION, NODE, FUNCTION> getEmptyConstraint() {
		return null;
	}

	public EqConstraint<ACTION, NODE, FUNCTION> getBottomConstraint() {
//		EqConstraint<ACTION, NODE, FUNCTION> result = mBottomConstraint;;
//		if (result == null)
		return mBottomConstraint;
	}

	public EqConstraint<ACTION, NODE, FUNCTION> unfreeze(EqConstraint<ACTION, NODE, FUNCTION> constraint) {
		assert constraint.isFrozen();
		// TODO Auto-generated method stub
		return null;
	}

//	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> unfreeze(
//			EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> constraint) {
//		// TODO Auto-generated method stub
//		return null;
//	}

	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> 
			getDisjunctiveConstraint(Collection<EqConstraint<ACTION, NODE, FUNCTION>> constraintList) {
		final Collection<EqConstraint<ACTION, NODE, FUNCTION>> bottomsFiltered = constraintList.stream()
				.filter(cons -> (cons instanceof EqBottomConstraint)).collect(Collectors.toSet());
		return new EqDisjunctiveConstraint<ACTION, NODE, FUNCTION>(bottomsFiltered);
	}

	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> conjoin(
			List<EqConstraint<ACTION, NODE, FUNCTION>> conjuncts) {
		
		EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> result = 
				getDisjunctiveConstraint(Collections.singleton(getEmptyConstraint()));
		
		for (EqConstraint<ACTION, NODE, FUNCTION> conjunct : conjuncts) {
			
			for (Entry<NODE, NODE> eq : conjunct.getSupportingElementEqualities().entrySet()) {
				result = addEquality(eq.getKey(), eq.getValue(), result);
			}
			
			for (VPDomainSymmetricPair<NODE> deq : conjunct.getElementDisequalities()) {
				result = addDisequality(deq.getFirst(), deq.getSecond(), result);
			}
			
			for (Entry<FUNCTION, FUNCTION> aEq : conjunct.getSupportingFunctionEqualities()) {
				result = addFunctionEquality(aEq.getKey(), aEq.getValue(), result);
			}
			
			for (VPDomainSymmetricPair<FUNCTION> aDeq : conjunct.getFunctionDisequalites()) {
				result = addFunctionDisequality(aDeq.getFirst(), aDeq.getSecond(), result);
			}
		}
		return result;
	}
	
	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> addFunctionDisequality(FUNCTION f1, FUNCTION f2,
			EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> inputConstraint) {
		EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> result = getDisjunctiveConstraint(Collections.emptySet());

		for (EqConstraint<ACTION, NODE, FUNCTION> inputDisjunct : inputConstraint.getConstraints()) {
//			result = result.union(addFunctionDisequality(f1, f2, inputDisjunct));
			result = disjoinDisjunctiveConstraints(result, addFunctionDisequality(f1, f2, inputDisjunct));
		}

		return result;
	}
		
	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> addFunctionDisequality(FUNCTION f1, FUNCTION f2,
			EqConstraint<ACTION, NODE, FUNCTION> inputConstraint) {
		return null;
	}

	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> addFunctionEquality(FUNCTION f1, FUNCTION f2,
			EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> inputConstraint) {

		EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> result = getDisjunctiveConstraint(Collections.emptySet());

		for (EqConstraint<ACTION, NODE, FUNCTION> inputDisjunct : inputConstraint.getConstraints()) {
//			result = result.union(addFunctionEquality(f1, f2, inputDisjunct));
			result = disjoinDisjunctiveConstraints(result, addFunctionEquality(f1, f2, inputDisjunct));
		}

		return result;
	}
	
	/**
	 * Update the given constraint with an equality between the two given functions/arrays. 
	 * The functions may be identifiers, or array store expressions.
	 * Because of extensionality, we have to add element equalities for the given symbols.
	 * 
	 * @param func1
	 * @param func2
	 * @param inputConstraint
	 * @return
	 */
	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> addFunctionEquality(FUNCTION func1, FUNCTION func2,
			EqConstraint<ACTION, NODE, FUNCTION> inputConstraint) {
//		if (factory.isDebugMode()) {
//			factory.getLogger().debug("VPFactoryHelpers: arrayEqualityWithException(..)");
//		}
//		assert (exceptionArrayNode == null) == (exceptionValueNode == null);

//		final T resultState = factory.copy(state).build();
//		
//		Set<T> resultStates = new HashSet<>();
//		resultStates.add(resultState);
//		for (final NODE fnNode1 : inputConstraint.getFunctionNodesForArray(resultState, func1)) {
//			for (final NODE fnNode2 : inputConstraint.getFunctionNodesForArray(resultState, func2)) {
//				final EqGraphNode<NODE, FUNCTION> gn1 = resultState.getEqGraphNode(fnNode1);
//				final EqGraphNode<NODE, FUNCTION> gn2 = resultState.getEqGraphNode(fnNode2);
//
//				if (inputConstraint.congruentIgnoreFunctionSymbol(gn1, gn2)) {
//					resultStates =
//							conjoinAll(resultStates, addEquality(fnNode1, fnNode2, resultState, factory), factory);
//				}
//			}
//		}
		
//		if (resultStates.isEmpty()) {
//			resultStates.add(resultState);
//		}
//		return resultStates;
		// TODO
		return null;
	}

//	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> conjoin(
//			List<EqConstraint<ACTION, NODE, FUNCTION>> conjuncts) {
//		final EqConstraint<ACTION, NODE, FUNCTION> newConstraint = getEmptyConstraint();
//		
//		for (EqConstraint<ACTION, NODE, FUNCTION> conjunct : conjuncts) {
//			newConstraint.addNodes(conjunct.getAllNodes());
//			
//			for (Entry<NODE, NODE> eq : conjunct.getSupportingElementEqualities().entrySet()) {
//				newConstraint.merge(eq.getKey(), eq.getValue());
//			}
//			
//			for (VPDomainSymmetricPair<NODE> deq : conjunct.getElementDisequalities()) {
//				newConstraint.addRawDisequality(deq.getFirst(), deq.getSecond());
//			}
//			
//			for (Entry<FUNCTION, FUNCTION> aEq : conjunct.getSupportingFunctionEqualities()) {
//				newConstraint.addFunctionEquality(aEq.getKey(), aEq.getValue());
//			}
//			
//			for (VPDomainSymmetricPair<FUNCTION> aDeq : conjunct.getFunctionDisequalites()) {
//				newConstraint.addFunctionDisequality(aDeq.getFirst(), aDeq.getSecond());
//			}
//
//			if (newConstraint.checkForContradiction()) {
//				return getBottomConstraint();
//			}
//		}
//		
//		newConstraint.freeze();
//		return newConstraint;
//	}

//	/**
//	 * Checks if the arguments of the given EqFunctionNodes are all congruent. 
//	 * (and only the arguments, for the standard congruence check from the congruence closure algorithm one will have to
//	 *  compare the function symbol, additionally)
//	 *
//	 * @param fnNode1
//	 * @param fnNode2
//	 * @return
//	 */
//	public static <NODEID extends IEqNodeIdentifier<NODEID, ARRAYID>, ARRAYID> boolean congruentIgnoreFunctionSymbol(
//			final EqGraphNode<NODEID, ARRAYID> fnNode1, final EqGraphNode<NODEID, ARRAYID> fnNode2) {
//		// assert fnNode1.getArgs() != null && fnNode2.getArgs() != null;
//		// assert fnNode1.getArgs().size() == fnNode2.getArgs().size();
//		assert fnNode1.mNodeIdentifier.isFunction();
//		assert fnNode2.mNodeIdentifier.isFunction();
//		
//		for (int i = 0; i < fnNode1.getInitCcchild().size(); i++) {
//			final EqGraphNode<NODEID, ARRAYID> fnNode1Arg = fnNode1.getInitCcchild().get(i);
//			final EqGraphNode<NODEID, ARRAYID> fnNode2Arg = fnNode2.getInitCcchild().get(i);
//			if (!fnNode1Arg.find().equals(fnNode2Arg.find())) {
//				return false;
//			}
//		}
//		return true;
//	}

	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> disjoinDisjunctiveConstraints(
			EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> disjunct1,
			EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> disjunct2) {
		final Set<EqConstraint<ACTION, NODE, FUNCTION>> allConjunctiveConstraints = new HashSet<>();			
		allConjunctiveConstraints.addAll(disjunct1.getConstraints());
		allConjunctiveConstraints.addAll(disjunct2.getConstraints());
		return getDisjunctiveConstraint(allConjunctiveConstraints);
	}

	/**
	 * disjunction/union/meet
	 * 
	 * @param disjuncts
	 * @return
	 */
	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> disjoinDisjunctiveConstraints(
			List<EqDisjunctiveConstraint<ACTION, NODE, FUNCTION>> disjuncts) {
		
		Set<EqConstraint<ACTION, NODE, FUNCTION>> allConjunctiveConstraints = new HashSet<>();			
		for (EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> disjunct : disjuncts) {
			allConjunctiveConstraints.addAll(disjunct.getConstraints());
		}

		return getDisjunctiveConstraint(allConjunctiveConstraints);
	}
	
	/**
	 * conjunction/intersection/join
	 * 
	 * @param conjuncts
	 * @return
	 */
	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> conjoinDisjunctiveConstraints(
			List<EqDisjunctiveConstraint<ACTION, NODE, FUNCTION>> conjuncts) {
		final List<Set<EqConstraint<ACTION, NODE, FUNCTION>>> listOfConstraintSets = conjuncts.stream()
				.map(conjunct -> conjunct.getConstraints()).collect(Collectors.toList());

		final Set<List<EqConstraint<ACTION, NODE, FUNCTION>>> crossProduct = 
				VPDomainHelpers.computeCrossProduct(listOfConstraintSets);

		final Set<Set<EqConstraint<ACTION, NODE, FUNCTION>>> constraintSetSet = crossProduct.stream()
				.map(constraintList -> (conjoin(constraintList).getConstraints()))
				.collect(Collectors.toSet());

		final Set<EqConstraint<ACTION, NODE, FUNCTION>> constraintSetFlat = new HashSet<>();
		constraintSetSet.stream().forEach(cs -> constraintSetFlat.addAll(cs));


		return getDisjunctiveConstraint(constraintSetFlat);
	}
	
	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> addEquality(NODE node1, NODE node2,
			EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> inputConstraint) {
//		if (factory.isDebugMode()) {
//			factory.getLogger().debug("VPFactoryHelpers: addEquality(" + node1 + ", " + node2 + ", " + "..." + ") -- "
//					+ originalStates.size() + " input states");
//		}

		if (node1 == node2 || node1.equals(node2)) {
			return inputConstraint;
		}
		
		EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> result = getDisjunctiveConstraint(Collections.emptySet());

		for (EqConstraint<ACTION, NODE, FUNCTION> inputDisjunct : inputConstraint.getConstraints()) {
//			result = result.union(addEquality(node1, node2, inputDisjunct));
			result = disjoinDisjunctiveConstraints(result, addEquality(node1, node2, inputDisjunct));
		}

		return result;
		
	}
	

	/**
	 * Add an equality to a (conjunctive) EqConstraint and close under propagation.
	 * <ol> Steps:
	 *  <li> merge the two nodes in the congruence graph, this closes under transitivity, symmetry, "forward" function
	 *    congruence; the result is still a conjunction.
	 *  <li> close under backward function congruence, the result may be a disjunction
	 *  <li> (TODO) close wrt array axioms: an added equality may mean that array equalities with store terms may allow
	 *      further conclusions, also select-over-store terms (in the element congruence graph) may allow conclusions
	 * </ol>
	 * 
	 * @param node1
	 * @param node2
	 * @param originalState
	 * @return
	 */
	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> addEquality(NODE node1, NODE node2,
			EqConstraint<ACTION, NODE, FUNCTION> originalState) {
		
//		factory.getBenchmark().unpause(VPSFO.addEqualityClock);
//		if (factory.isDebugMode()) {
//			factory.getLogger().debug("VPFactoryHelpers: addEquality(" + node1 + ", " + node2 + ", " + "..." + ")");
//		}
		if (originalState.isBottom()) {
//			factory.getBenchmark().stop(VPSFO.addEqualityClock);
			return getDisjunctiveConstraint(Collections.singleton(originalState));
		}

		if (node1 == node2 || node1.equals(node2)) {
//			factory.getBenchmark().stop(VPSFO.addEqualityClock);
//			return Collections.singleton(originalState);
			return getDisjunctiveConstraint(Collections.singleton(originalState));
		}

//		final IVPStateOrTfStateBuilder<T, NODEID, ARRAYID> builder = factory.copy(originalState);
		
//		final EqGraphNode<NODE, FUNCTION> gn1 = builder.getEqGraphNode(node1);
//		final EqGraphNode<NODE, FUNCTION> gn2 = builder.getEqGraphNode(node2);
//		if (gn1.find() == gn2.find()) {
		if (originalState.areEqual(node1, node2)) {
			// the given identifiers are already equal in the originalState
//			factory.getBenchmark().stop(VPSFO.addEqualityClock);
//			return Collections.singleton(originalState);
			return getDisjunctiveConstraint(Collections.singleton(originalState));
		}

		EqConstraint<ACTION, NODE, FUNCTION> constraintAfterMerge = unfreeze(originalState);
		
//		builder.merge(gn1, gn2);
		HashRelation<NODE, NODE> mergeHistory = constraintAfterMerge.merge(node1, node2);
//		builder.setIsTop(false);
//		final boolean contradiction = builder.checkContradiction();
		final boolean contradiction = constraintAfterMerge.checkForContradiction();
//		assert contradiction || VPDomainHelpers.disEqualityRelationIrreflexive(builder.getDisEqualitySet(), builder);
		if (contradiction) {
			final Set<EqConstraint<ACTION, NODE, FUNCTION>> result = Collections.singleton(getBottomConstraint());
			assert result.stream().filter(element -> element == null).count() == 0;
//			factory.getBenchmark().stop(VPSFO.addEqualityClock);
//			return result;
			return getDisjunctiveConstraint(result);
		}

//		final EqConstraint<ACTION, NODE, FUNCTION> resultState = newConstraint;

		/*
		 * Propagate disequalites
		 *  <li> the equality we have introduced may, together with preexisting disequalities, allow propagations of 
		 *    disequalities (see the documentation of the propagateDisequalites method for details)
		 *  <li> we need to account for every two equivalence classes that have been merge before, i.e. using the 
		 *    "mergeHistory".. (those may be much more that just node1, node2, because of equality propagation..)
		 *  <li> Note that since all the propagate.. operations only introduce disequalities they don't interfere with
		 *     each other. This means we can collect the results separately and join them into a disjunction afterwards.
		 *      (therefore it is ok for propagateDisequalities to operate on an (conjunctive) EqConstraint only.)
		 */
//		final Set<T> resultStates = new HashSet<>();
		EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> resultState = 
				getDisjunctiveConstraint(Collections.singleton(constraintAfterMerge));
		for (Entry<NODE, NODE> pair : mergeHistory.entrySet()) {
			
			for (final NODE other : originalState.getDisequalities(pair.getKey())) {
				//			factory.getBenchmark().stop(VPSFO.addEqualityClock);
				//			resultStates.addAll(propagateDisEqualites(resultState, node1, other));
//				resultState = resultState.union(propagateDisequalites(constraintAfterMerge, pair.getKey(), other));
				resultState = disjoinDisjunctiveConstraints(
						resultState, propagateDisequalites(constraintAfterMerge, pair.getKey(), other));
				//			factory.getBenchmark().unpause(VPSFO.addEqualityClock);
			}
			for (final NODE other : originalState.getDisequalities(pair.getValue())) {
				//			factory.getBenchmark().stop(VPSFO.addEqualityClock);
//				resultStates.addAll(propagateDisequalites(resultState, node2, other));
//				resultState = resultState.union(propagateDisequalites(constraintAfterMerge, pair.getValue(), other));
				resultState = disjoinDisjunctiveConstraints(
						resultState, propagateDisequalites(constraintAfterMerge, pair.getValue(), other));
				//			factory.getBenchmark().unpause(VPSFO.addEqualityClock);
		}
		}
		
		assert !resultState.getConstraints().isEmpty();
//		if (resultStates.isEmpty()) {
//			assert resultState != null;
////			factory.getBenchmark().stop(VPSFO.addEqualityClock);
//			return getDisjunctiveConstraint(Collections.singleton(resultState));
//		}
		
		// assert VPDomainHelpers.allStatesHaveSameVariables(resultStates);
//		assert resultStates.stream().filter(element -> element == null).count() == 0;
		assert resultState.getConstraints().stream().filter(element -> element == null).count() == 0;
//		factory.getBenchmark().stop(VPSFO.addEqualityClock);
		return resultState;
	}

	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> addDisequality(
			NODE node1, NODE node2, EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> inputConstraint) {
//		final EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> result = getDisjunctiveConstraint(Collections.emptySet());
//		if (factory.isDebugMode()) {
//			factory.getLogger().debug("VPFactoryHelpers: addDisEquality(..)");
//		}
		
		EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> result = getDisjunctiveConstraint(Collections.emptySet());

		for (EqConstraint<ACTION, NODE, FUNCTION> inputDisjunct : inputConstraint.getConstraints()) {
//			result = result.union(addDisequality(node1, node2, inputDisjunct));
			result = disjoinDisjunctiveConstraints(result, addDisequality(node1, node2, inputDisjunct));
		}

		return result;
	}
	
	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> addDisequality(
			final NODE i1, final NODE i2, final EqConstraint<ACTION, NODE, FUNCTION> originalState) {
//		if (factory.isDebugMode()) {
//			factory.getLogger().debug("VPFactoryHelpers: addDisEquality(..)");
//		}
		if (originalState.isBottom()) {
			return getDisjunctiveConstraint(Collections.singleton(originalState));
		}

//		final IVPStateOrTfStateBuilder<T, NODEID, ARRAYID> builder = factory.copy(originalState);

//		final EqGraphNode<NODEID, ARRAYID> gn1 = builder.getEqGraphNode(i1);
//		final EqGraphNode<NODEID, ARRAYID> gn2 = builder.getEqGraphNode(i2);

		/*
		 * check if the disequality introduces a contradiction, return bottom in that case
		 */
//		if (gn1.find().equals(gn2.find())) {
		if (originalState.areEqual(i1, i2)) {
			return getDisjunctiveConstraint(Collections.singleton(getBottomConstraint()));
//			return Collections.singleton(factory.getBottomState(originalState));
		}

		/*
		 * no contradiction --> introduce disequality
		 */
//		builder.addDisEquality(gn1.find().mNodeIdentifier, gn2.find().mNodeIdentifier);
		EqConstraint<ACTION, NODE, FUNCTION> unfrozen = unfreeze(originalState);
		unfrozen.addRawDisequality(i1, i2);
		unfrozen.freeze();

//		builder.setIsTop(false);

		/*
		 * propagate disequality to children
		 */
//		final Set<T> result = propagateDisEqualites(builder.build(), gn1.find(), gn2.find(), factory);
		EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> result = propagateDisequalites(unfrozen, i1, i2);

		// assert VPDomainHelpers.allStatesHaveSameVariables(result);
		return result;
	}
	
	/**
	 * Takes a preState and two representatives of different equivalence classes. Under the assumption that a
	 * disequality between the equivalence classes has been introduced, propagates all the disequalities that follow
	 * from that disequality.
	 * 
	 * Note that the resulting disjunction is guaranteed to subsume the input state. Thus, if no propagations are
	 * possible, the input state is returned.
	 * 
	 * Background: 
	 * <ul>
	 *  <li> our disequality relation is stored as disequalities between equivalence classes
	 *  <li> joining two equivalence may add implicit equalities that allow disequality propagation (via function 
	 *      congruence)
	 * </ul>
	 * 
	 * Furthermore, we store information about which arguments for any function node in each equivalence class are 
	 *  present -- the "ccchild" field, which corresponds to the ccpar field from standard congruence closure.
	 * <p>
	 * This method is a helper that, for two representatives of equivalence classes in the inputState which we know to
	 * be unequal in the inputState, checks if, because of merging the two states, any disequality propagations are 
	 * possible.
	 * It returns a disjunction of states where all possible propagations have been done.
	 * 
	 * Example:
	 *  <li> preState:
	 *   (i = f(y)) , (j != f(x)), (i = j)
	 *  <li> we just added an equality between i and j (did the merge operation)
	 *  <li> one call of this method will be with (preState, i, f(x))
	 *  <li> we will get the output state:
	 *   (i = f(y)) , (j != f(x)), (i = j), (x != y)
	 *
	 * @param inputState
	 * @param representative1
	 * @param representative2
	 * @return
	 */
	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> propagateDisequalites(
			final EqConstraint<ACTION, NODE, FUNCTION> inputState, 
			final NODE representative1,
			final NODE representative2) {
		return propagateDisEqualites(inputState, representative1, representative2, true);
	}
	
	
	public EqConstraint<ACTION, NODE, FUNCTION> propagateDisEqualitesForbidDisjunctions(
			final EqConstraint<ACTION, NODE, FUNCTION> inputState, 
			final NODE representative1,
			final NODE representative2) {
		EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> result = 
				propagateDisEqualites(inputState, representative1, representative2, false);
		assert result.getConstraints().size() == 1;
		return result.getConstraints().iterator().next();
	}



	private EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> propagateDisEqualites(
			final EqConstraint<ACTION, NODE, FUNCTION> inputState, 
			final NODE representative1,
			final NODE representative2,
			final boolean allowDisjunctions) {
		assert inputState.areUnequal(representative1, representative2);

//		factory.getBenchmark().unpause(VPSFO.propagateDisEqualitiesClock);
//		if (factory.isDebugMode()) {
//			factory.getLogger().debug("VPFactoryHelpers: propagateDisEqualities(..)");
//		}

		EqDisjunctiveConstraint<ACTION, NODE, FUNCTION>	result = 
				getDisjunctiveConstraint(Collections.singleton(inputState));
		
		final HashRelation<FUNCTION, List<NODE>> ccchild1 = inputState.getCCChild(representative1);
		final HashRelation<FUNCTION, List<NODE>> ccchild2 = inputState.getCCChild(representative2);

		for (final FUNCTION arrayId : ccchild1.getDomain()) {
			
			// if we disallow disjunction we only propagate disequalities for one-dimensional arrays/unary functions
			if (!allowDisjunctions && arrayId.getArity() > 1) {
				continue;
			}
			
			for (final List<NODE> list1 : ccchild1.getImage(arrayId)) {
				for (final List<NODE> list2 : ccchild2.getImage(arrayId)) {
					/**
					 * the result "frozen" at the start of each propagation of a single function disequality
					 */
					final EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> intermediateResult = 
							getDisjunctiveConstraint(result.getConstraints());
					
					
					/*
					 * reset the result, because it will be filled in the loop
					 */
					result = getDisjunctiveConstraint(Collections.emptySet());

					for (int i = 0; i < list1.size(); i++) {
						final NODE c1 = list1.get(i);
						final NODE c2 = list2.get(i);
						if (inputState.areUnequal(c1, c2)) {
							continue;
						}
//						factory.getBenchmark().stop(VPSFO.propagateDisEqualitiesClock);
//						result = result.union(addDisequality(c1, c2, intermediateResult));
						result = disjoinDisjunctiveConstraints(result,
								addDisequality(c1, c2, intermediateResult));
//						factory.getBenchmark().unpause(VPSFO.propagateDisEqualitiesClock);
					}
				}
			}
		}

		if (result.isEmpty()) {
			// no propagations -- return the input state
//			factory.getBenchmark().stop(VPSFO.propagateDisEqualitiesClock);
			return getDisjunctiveConstraint(Collections.singleton(inputState));
		}
//		factory.getBenchmark().stop(VPSFO.propagateDisEqualitiesClock);
		return result;
	}
	
	/**
	 * Adds the given node to the given constraint, returns the resulting constraint.
	 * 
	 * Adding a node can have side effects, even though no (dis)equality constraint is added.
	 * <ul> Reasons:
	 *  <li> the constraint may have an array equality that, by extensionality, says something about the new node
	 *  <li> .. other reasons?..
	 * </ul>
	 * 
	 * 
	 * @param nodeToAdd
	 * @param constraint
	 * @return
	 */
	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> addNode(NODE nodeToAdd, 
			EqConstraint<ACTION, NODE, FUNCTION> constraint) {
		
		return null;
	}
}
