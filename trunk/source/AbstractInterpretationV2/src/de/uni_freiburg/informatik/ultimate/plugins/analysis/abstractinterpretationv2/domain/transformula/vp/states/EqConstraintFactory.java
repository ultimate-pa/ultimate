package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainHelpers;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNodeAndFunctionFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.IEqFunctionIdentifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class EqConstraintFactory<
			ACTION extends IIcfgTransition<IcfgLocation>, 
			NODE extends IEqNodeIdentifier<NODE, FUNCTION>, 
			FUNCTION extends IEqFunctionIdentifier<NODE, FUNCTION>> {

	private final EqConstraint<ACTION, NODE, FUNCTION> mBottomConstraint;

	private EqStateFactory<ACTION> mEqStateFactory;

	private final EqNodeAndFunctionFactory mEqNodeAndFunctionFactory;
	
	public EqConstraintFactory(EqNodeAndFunctionFactory eqNodeAndFunctionFactory) {
		mBottomConstraint = new EqBottomConstraint<>(this);
		mBottomConstraint.freeze();

		mEqNodeAndFunctionFactory = eqNodeAndFunctionFactory;
	}

	public EqConstraint<ACTION, NODE, FUNCTION> getEmptyConstraint() {
		final EqConstraint<ACTION, NODE, FUNCTION> result = new EqConstraint<>(this);
		result.freeze();
		return result;
	}

	public EqConstraint<ACTION, NODE, FUNCTION> getBottomConstraint() {
//		EqConstraint<ACTION, NODE, FUNCTION> result = mBottomConstraint;;
//		if (result == null)
		return mBottomConstraint;
	}

	public EqConstraint<ACTION, NODE, FUNCTION> unfreeze(EqConstraint<ACTION, NODE, FUNCTION> constraint) {
		assert constraint.isFrozen();
		return new EqConstraint<>(constraint);
	}

//	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> unfreeze(
//			EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> constraint) {
//		// TODO Auto-generated method stub
//		return null;
//	}

	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> 
			getDisjunctiveConstraint(Collection<EqConstraint<ACTION, NODE, FUNCTION>> constraintList) {
		final Collection<EqConstraint<ACTION, NODE, FUNCTION>> bottomsFiltered = constraintList.stream()
				.filter(cons -> !(cons instanceof EqBottomConstraint)).collect(Collectors.toSet());
		return new EqDisjunctiveConstraint<ACTION, NODE, FUNCTION>(bottomsFiltered, this);
	}
	
	
	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> conjoin(
			EqConstraint<ACTION, NODE, FUNCTION> conjunct1,
			EqConstraint<ACTION, NODE, FUNCTION> conjunct2) {
		final List<EqConstraint<ACTION, NODE, FUNCTION>> conjuncts = new ArrayList<>();
		conjuncts.add(conjunct1);
		conjuncts.add(conjunct2);
		return conjoin(conjuncts);
	}

	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> conjoin(
			List<EqConstraint<ACTION, NODE, FUNCTION>> conjuncts) {
		
		EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> result = 
				getDisjunctiveConstraint(Collections.singleton(getEmptyConstraint()));
		
		for (EqConstraint<ACTION, NODE, FUNCTION> conjunct : conjuncts) {
			
			for (Entry<NODE, NODE> eq : conjunct.getSupportingElementEqualities().entrySet()) {
				result = addEqualityFlat(eq.getKey(), eq.getValue(), result);
			}
			
			for (VPDomainSymmetricPair<NODE> deq : conjunct.getElementDisequalities()) {
				result = addDisequalityFlat(deq.getFirst(), deq.getSecond(), result);
			}
			
			for (Entry<FUNCTION, FUNCTION> aEq : conjunct.getSupportingFunctionEqualities()) {
				result = addFunctionEqualityFlat(aEq.getKey(), aEq.getValue(), result);
			}
			
			for (VPDomainSymmetricPair<FUNCTION> aDeq : conjunct.getFunctionDisequalites()) {
				result = addFunctionDisequalityFlat(aDeq.getFirst(), aDeq.getSecond(), result);
			}
		}
		return result;
	}
	
	public EqConstraint<ACTION, NODE, FUNCTION> conjoinFlat(
			EqConstraint<ACTION, NODE, FUNCTION> constraint1,
			EqConstraint<ACTION, NODE, FUNCTION> constraint2) {
		return conjoin(constraint1, constraint2).flatten();
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
	
	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> addFunctionDisequalityFlat(FUNCTION f1, FUNCTION f2,
				EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> inputConstraint) {
			if (f1 == f2 || f1.equals(f2)) {
				return inputConstraint;
			}
			final EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> result = getDisjunctiveConstraint(
					inputConstraint.getConstraints().stream()
						.map(cons -> addFunctionDisequalityFlat(f1, f2, cons))
						.collect(Collectors.toSet()));
			return result;
	}

	public EqConstraint<ACTION, NODE, FUNCTION> addFunctionDisequalityFlat(FUNCTION func1, FUNCTION func2,
			EqConstraint<ACTION, NODE, FUNCTION> originalState) {
		if (originalState.isBottom()) {
//			factory.getBenchmark().stop(VPSFO.addEqualityClock);
			return originalState;
		}

		if (func1 == func2 || func1.equals(func2)) {
//			factory.getBenchmark().stop(VPSFO.addEqualityClock);
			return originalState;
		}
		
		if (originalState.areUnequal(func1, func2)) {
			// the given identifiers are already equal in the originalState
			return originalState;
		}
		
		if (originalState.areEqual(func1, func2)) {
			return getBottomConstraint();
		}
		
		final EqConstraint<ACTION, NODE, FUNCTION> funct1Added = addFunctionFlat(func1, originalState);
		final EqConstraint<ACTION, NODE, FUNCTION> funct2Added = addFunctionFlat(func2, funct1Added);	
		
		final EqConstraint<ACTION, NODE, FUNCTION> newConstraint = unfreeze(funct2Added);
		newConstraint.addFunctionDisequality(func1, func2);
		
		// TODO propagations
		
		newConstraint.freeze();
		return newConstraint;
	}

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
	
	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> addFunctionEqualityFlat(FUNCTION f1, FUNCTION f2,
				EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> inputConstraint) {
			if (f1 == f2 || f1.equals(f2)) {
				return inputConstraint;
			}
			final EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> result = getDisjunctiveConstraint(
					inputConstraint.getConstraints().stream()
						.map(cons -> addFunctionEqualityFlat(f1, f2, cons))
						.collect(Collectors.toSet()));
			return result;
	}

	public EqConstraint<ACTION, NODE, FUNCTION> addFunctionEqualityFlat(FUNCTION func1, FUNCTION func2,
			EqConstraint<ACTION, NODE, FUNCTION> originalState) {
		if (originalState.isBottom()) {
//			factory.getBenchmark().stop(VPSFO.addEqualityClock);
			return originalState;
		}

		if (func1 == func2 || func1.equals(func2)) {
//			factory.getBenchmark().stop(VPSFO.addEqualityClock);
			return originalState;
		}
		
		if (originalState.areEqual(func1, func2)) {
			// the given identifiers are already equal in the originalState
			return originalState;
		}
		
		if (originalState.areUnequal(func1, func2)) {
			return getBottomConstraint();
		}
		
		final EqConstraint<ACTION, NODE, FUNCTION> funct1Added = addFunctionFlat(func1, originalState);
		final EqConstraint<ACTION, NODE, FUNCTION> funct2Added = addFunctionFlat(func2, funct1Added);	
		
		final EqConstraint<ACTION, NODE, FUNCTION> newConstraint = unfreeze(funct2Added);
		newConstraint.addFunctionEqualityRaw(func1, func2);
		newConstraint.freeze();
		
		// TODO propagations
		EqConstraint<ACTION, NODE, FUNCTION> newConstraintWithPropagations = newConstraint;
		
		
		final Set<NODE> chosenNodes = new HashSet<>();
		chosenNodes.addAll(newConstraintWithPropagations.getAllNodes()); // TODO: chose by correct sort
		// also choose some subterms
		chosenNodes.addAll(newConstraintWithPropagations.getAllNodes().stream()
			.filter(node -> node.isFunction())
			.map(node -> node.getArgs().get(0)).collect(Collectors.toSet())); // TODO deal with multidim arrays

		
		/*
		 * for each node t (that we chose before), we add the equality "func1(t) = func2(t)"
		 */
		final ManagedScript mgdScript = mEqNodeAndFunctionFactory.getScript();
		mgdScript.lock(this);
		for (NODE cn : chosenNodes) {
			final Term func1AtIndexTerm = mgdScript.term(this, "select", func1.getTerm(), cn.getTerm());
			final NODE func1AtIndex = (NODE) mEqNodeAndFunctionFactory.getOrConstructEqNode(func1AtIndexTerm);
			final Term func2AtIndexTerm = mgdScript.term(this, "select", func2.getTerm(), cn.getTerm());
			final NODE func2AtIndex = (NODE) mEqNodeAndFunctionFactory.getOrConstructEqNode(func2AtIndexTerm);
			newConstraintWithPropagations = addEqualityFlat(func1AtIndex, func2AtIndex, newConstraintWithPropagations);
		}
		mgdScript.unlock(this);
		
//		// TODO: which nodes to take here??
//		final Set<NODE> nodesWithFunc1 = newConstraint.getAllNodes().stream()
//			.filter(node -> ((node instanceof EqFunctionNode) && ((NODE) node).getFunction().equals(func1)))
//			.collect(Collectors.toSet());
//		final Set<NODE> nodesWithFunc2 = newConstraint.getAllNodes().stream()
//			.filter(node -> ((node instanceof EqFunctionNode) && ((NODE) node).getFunction().equals(func2)))
//			.collect(Collectors.toSet());
//		
//		/*
//		 * 
//		 *  <li> for each node func1(t), we add the equality "func1(t) = func2(t)" and vice versa
//		 *  <li> furthermore, if func1 has the form (store a i x), and the constraint says t != i, we add 
//		 *     "a(t) = func2(t)" (??) EDIT: don't do that here, instead add (store a i x)[j] = a[j] in constraints where
//		 *      i != j holds. (triggers: addFunction(store) and addDisequality 
//		 */
//		final ManagedScript mgdScript = mEqNodeAndFunctionFactory.getScript();
//		mgdScript.lock(this);
//		for (NODE func1Node : nodesWithFunc1) {
//			final EqFunctionNode efn = (EqFunctionNode) func1Node;
//			final ApplicationTerm at = (ApplicationTerm) efn.getTerm();
//			assert "select".equals(at.getFunction().getName());
//			final Term func2AtIndexTerm = mgdScript.term(this, "select", func2.getTerm(), at.getParameters()[1]);
//			final NODE func2AtIndex = (NODE) mEqNodeAndFunctionFactory.getOrConstructEqNode(func2AtIndexTerm);
//			newConstraintWithPropagations = addEqualityFlat(func1Node, func2AtIndex, newConstraintWithPropagations);
//		}
//		for (NODE func2Node : nodesWithFunc2) {
//			final EqFunctionNode efn = (EqFunctionNode) func2Node;
//			final ApplicationTerm at = (ApplicationTerm) efn.getTerm();
//			assert "select".equals(at.getFunction().getName());
//			final Term func1AtIndexTerm = mgdScript.term(this, "select", func1.getTerm(), at.getParameters()[1]);
//			final NODE func1AtIndex = (NODE) mEqNodeAndFunctionFactory.getOrConstructEqNode(func1AtIndexTerm);
//			newConstraintWithPropagations = addEqualityFlat(func2Node, func1AtIndex, newConstraintWithPropagations);
//		}
//		mgdScript.unlock(this);
	
		return newConstraintWithPropagations;
	}

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
	 * Disjoin two (conjunctive) EqConstraints without creating an EqDisjunctiveConstraint -- this operation may loose
	 * information.
	 * 
	 * Essentially, we only keep constraints that are present in both input constraints.
	 * 
	 * @param constraint
	 * @param constraint2
	 * @return
	 */
	public EqConstraint<ACTION, NODE, FUNCTION> disjoinFlat(
			EqConstraint<ACTION, NODE, FUNCTION> constraint1, 
			EqConstraint<ACTION, NODE, FUNCTION> constraint2) {
		final List<EqConstraint<ACTION, NODE, FUNCTION>> disjuncts = new ArrayList<>();
		disjuncts.add(constraint1);
		disjuncts.add(constraint2);
		return getDisjunctiveConstraint(disjuncts).flatten();
	}
	
	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> addEqualityFlat(NODE node1, NODE node2,
				EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> inputConstraint) {
			if (node1 == node2 || node1.equals(node2)) {
				return inputConstraint;
			}
			final EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> result = getDisjunctiveConstraint(
					inputConstraint.getConstraints().stream()
						.map(cons -> addEqualityFlat(node1, node2, cons))
						.collect(Collectors.toSet()));
			return result;
	}

	public EqConstraint<ACTION, NODE, FUNCTION> addEqualityFlat(NODE node1, NODE node2,
			EqConstraint<ACTION, NODE, FUNCTION> originalState) {
		
//		factory.getBenchmark().unpause(VPSFO.addEqualityClock);
//		if (factory.isDebugMode()) {
//			factory.getLogger().debug("VPFactoryHelpers: addEquality(" + node1 + ", " + node2 + ", " + "..." + ")");
//		}
		if (originalState.isBottom()) {
//			factory.getBenchmark().stop(VPSFO.addEqualityClock);
			return originalState;
		}

		if (node1 == node2 || node1.equals(node2)) {
//			factory.getBenchmark().stop(VPSFO.addEqualityClock);
			return originalState;
		}
		
		if (originalState.areEqual(node1, node2)) {
			// the given identifiers are already equal in the originalState
			return originalState;
		}
		
		if (originalState.areUnequal(node1, node2)) {
			return getBottomConstraint();
		}

		
		EqConstraint<ACTION, NODE, FUNCTION> nodesAdded = addNodeFlat(node1, originalState);
		nodesAdded = addNodeFlat(node2, nodesAdded);

		final EqConstraint<ACTION, NODE, FUNCTION> constraintAfterMerge = unfreeze(nodesAdded);
		
		final HashRelation<NODE, NODE> mergeHistory = constraintAfterMerge.merge(node1, node2);
		constraintAfterMerge.freeze();
		final boolean contradiction = constraintAfterMerge.checkForContradiction();
		if (contradiction) {
			return getBottomConstraint();
		}

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
		EqConstraint<ACTION, NODE, FUNCTION> resultConstraint = constraintAfterMerge;
		for (Entry<NODE, NODE> pair : mergeHistory.entrySet()) {
			
			for (final NODE other : constraintAfterMerge.getDisequalities(pair.getKey())) {
				//			factory.getBenchmark().stop(VPSFO.addEqualityClock);
				resultConstraint = propagateDisequalitesFlat(resultConstraint, pair.getKey(), other);
			}
			for (final NODE other : constraintAfterMerge.getDisequalities(pair.getValue())) {
				//			factory.getBenchmark().stop(VPSFO.addEqualityClock);
				resultConstraint = propagateDisequalitesFlat(resultConstraint, pair.getValue(), other);
			}
		}
//		factory.getBenchmark().stop(VPSFO.addEqualityClock);
		return resultConstraint;
	}
	
	

//	private EqConstraint<ACTION, NODE, FUNCTION> propagateDisequalitesFlat(
//				EqConstraint<ACTION, NODE, FUNCTION> resultState, NODE key, NODE other) {
//			// TODO Auto-generated method stub
//			return null;
//		}

	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> addDisequality(
			NODE node1, NODE node2, EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> inputConstraint) {
//		final EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> result = getDisjunctiveConstraint(Collections.emptySet());
//		if (factory.isDebugMode()) {
//			factory.getLogger().debug("VPFactoryHelpers: addDisEquality(..)");
//		}
		
		EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> result = getDisjunctiveConstraint(Collections.emptySet());

		for (EqConstraint<ACTION, NODE, FUNCTION> inputDisjunct : inputConstraint.getConstraints()) {
			result = disjoinDisjunctiveConstraints(result, addDisequality(node1, node2, inputDisjunct));
		}

		return result;
	}
	
	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> addDisequality(
			final NODE node1, final NODE node2, final EqConstraint<ACTION, NODE, FUNCTION> inputConstraint) {
//		if (factory.isDebugMode()) {
//			factory.getLogger().debug("VPFactoryHelpers: addDisEquality(..)");
//		}
		if (inputConstraint.isBottom()) {
			return getDisjunctiveConstraint(Collections.singleton(inputConstraint));
		}

		/*
		 * check if the disequality introduces a contradiction, return bottom in that case
		 */
		if (inputConstraint.areEqual(node1, node2)) {
			return getDisjunctiveConstraint(Collections.singleton(getBottomConstraint()));
		}

		/*
		 * no contradiction --> introduce disequality
		 */
		EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> nodesAdded = addNode(node1, inputConstraint);
		nodesAdded = addNode(node2, nodesAdded);
		
		EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> result = getDisjunctiveConstraint(Collections.emptySet());
		for (EqConstraint<ACTION, NODE, FUNCTION> constraint : nodesAdded.getConstraints()) {
			EqConstraint<ACTION, NODE, FUNCTION> unfrozen = unfreeze(constraint);
			unfrozen.addRawDisequality(node1, node2);
			unfrozen.freeze();

			/*
			 * propagate disequality to children
			 */
			EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> resultForCurrentConstraint = 
					propagateDisequalites(unfrozen, node1, node2);
			
			result = disjoinDisjunctiveConstraints(result, resultForCurrentConstraint);
		}

		return result;
	}

	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> addDisequalityFlat(NODE node1, NODE node2,
				EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> inputConstraint) {
			if (node1 == node2 || node1.equals(node2)) {
				return inputConstraint;
			}
			final EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> result = getDisjunctiveConstraint(
					inputConstraint.getConstraints().stream()
						.map(cons -> addDisequalityFlat(node1, node2, cons))
						.collect(Collectors.toSet()));
			return result;
	}


	
	public EqConstraint<ACTION, NODE, FUNCTION> addDisequalityFlat(final NODE node1, final NODE node2, 
			final EqConstraint<ACTION, NODE, FUNCTION> originalState) {
//		if (factory.isDebugMode()) {
//			factory.getLogger().debug("VPFactoryHelpers: addDisEquality(..)");
//		}
		if (originalState.isBottom()) {
			return originalState;
		}
		
		if (originalState.areUnequal(node1, node2)) {
			return originalState;
		}

		/*
		 * check if the disequality introduces a contradiction, return bottom in that case
		 */
		if (originalState.areEqual(node1, node2)) {
			return getBottomConstraint();
		}

		/*
		 * no contradiction --> introduce disequality
		 */
		EqConstraint<ACTION, NODE, FUNCTION> nodesAdded = addNodeFlat(node1, originalState);
		nodesAdded = addNodeFlat(node2, nodesAdded);
		EqConstraint<ACTION, NODE, FUNCTION> unfrozen = unfreeze(nodesAdded);
		unfrozen.addRawDisequality(node1, node2);
		unfrozen.freeze();

		/*
		 * propagate disequality to children
		 */
		final EqConstraint<ACTION, NODE, FUNCTION> newConstraintWithBackwardCongruence = 
				propagateDisequalitesFlat(unfrozen, node1, node2);
		
		/*
		 * adding a disequality may trigger the read-over-write axiom
		 */
		EqConstraint<ACTION, NODE, FUNCTION> newConstraintWithPropagations = newConstraintWithBackwardCongruence;
		// TOOD: would getAllStoreFunctions be better?
		for (FUNCTION func : newConstraintWithPropagations.getAllFunctions()) { 
			newConstraintWithPropagations = propagateRowDeq(func, newConstraintWithPropagations);
		}

//		result.freeze();
		return newConstraintWithPropagations;
	}
	
	
	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> addNode(NODE nodeToAdd, 
			EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> constraint) {

		final Set<EqConstraint<ACTION, NODE, FUNCTION>> newConstraints = new HashSet<>();

		for (EqConstraint<ACTION, NODE, FUNCTION> cons : constraint.getConstraints()) {
			newConstraints.add(addNodeFlat(nodeToAdd, cons));
		}
		
		return getDisjunctiveConstraint(newConstraints);
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
	@Deprecated
	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> addNode(NODE nodeToAdd, 
			EqConstraint<ACTION, NODE, FUNCTION> constraint) {
		return getDisjunctiveConstraint(Collections.singleton(addNodeFlat(nodeToAdd,constraint)));
		
	}
	
	public EqConstraint<ACTION, NODE, FUNCTION> addNodeFlat(NODE nodeToAdd, 
			EqConstraint<ACTION, NODE, FUNCTION> constraint) {
		if (constraint.getAllNodes().contains(nodeToAdd)) {
			return constraint;
		}
		
		final EqConstraint<ACTION, NODE, FUNCTION> unf = unfreeze(constraint);
		unf.addNodeRaw(nodeToAdd);
		unf.freeze();
		
		// introduce disequalities if we have a literal TODO: disequality treatment might need reworking
		EqConstraint<ACTION, NODE, FUNCTION> newConstraintWithPropagations = unf;
		if (nodeToAdd.isLiteral()) {
			for (NODE otherNode : newConstraintWithPropagations.getAllNodes()) {
				if (otherNode.equals(nodeToAdd) || !otherNode.isLiteral()) {
					continue;
				}
				newConstraintWithPropagations = addDisequalityFlat(nodeToAdd, otherNode, newConstraintWithPropagations);
			}
		}
		
		return newConstraintWithPropagations;
//		return unf;
	}
	
	
	private EqConstraint<ACTION, NODE, FUNCTION> addFunctionFlat(FUNCTION func,
			EqConstraint<ACTION, NODE, FUNCTION> constraint) {
		EqConstraint<ACTION, NODE, FUNCTION> newConstraint = unfreeze(constraint);
		newConstraint.addFunctionRaw(func);
		newConstraint.freeze();
		// TODO propagations
		EqConstraint<ACTION, NODE, FUNCTION> newConstraintWithPropagations = newConstraint;

		/*
		 *  propagate read-over-write (both cases)
		 */
		newConstraintWithPropagations = propagateIdx(func, newConstraintWithPropagations);
		
		newConstraintWithPropagations = propagateRowDeq(func, newConstraintWithPropagations);
		
		return newConstraintWithPropagations;
	}

	private EqConstraint<ACTION, NODE, FUNCTION> propagateIdx(FUNCTION func, EqConstraint<ACTION, NODE, FUNCTION> orig) {
		if (!(func.isStore())) {
			return orig;
		}
		// idx axiom: ( a[i:=v][i] == v )
//		EqStoreFunction store = (EqStoreFunction) func1;
	
	
		assert func.getStoreIndices().size() == 1 : "TODO: deal with multidimensional case";
		assert !func.getFunction().isStore() : "TODO: deal with nested stores";

		final ManagedScript mgdScript = mEqNodeAndFunctionFactory.getScript();
		mgdScript.lock(this);
		Term selectTerm = mgdScript.term(this, 
				"select", 
				func.getTerm(), 
				func.getStoreIndices().iterator().next().getTerm());
		mgdScript.unlock(this);
	
		final NODE selectIdxNode = (NODE) mEqNodeAndFunctionFactory.getOrConstructEqNode(selectTerm);
		final NODE storeValueNode = 
				(NODE) mEqNodeAndFunctionFactory.getOrConstructEqNode(func.getValue().getTerm());
	
		return addEqualityFlat(selectIdxNode, storeValueNode, orig);
	}

	private EqConstraint<ACTION, NODE, FUNCTION> propagateRowDeq(FUNCTION func,
			EqConstraint<ACTION, NODE, FUNCTION> inputConstraint) {
		if (!func.isStore()) {
			return inputConstraint;
		}
		EqConstraint<ACTION, NODE, FUNCTION> newConstraint = inputConstraint;

		assert func.getStoreIndices().size() == 1 : "TODO: deal with multidimensional case";
		assert !func.getFunction().isStore() : "TODO: deal with nested stores";
		NODE storeIndex = func.getStoreIndices().iterator().next();
		for (NODE nodeUnequalToStoreIndex : inputConstraint.getDisequalities(storeIndex)) {
			final ManagedScript mgdScript = mEqNodeAndFunctionFactory.getScript();
			mgdScript.lock(this);
			Term selectOverStoreTerm = mgdScript.term(this, 
					"select", 
					func.getTerm(), 
					nodeUnequalToStoreIndex.getTerm());
			Term selectInsideStoreTerm = mgdScript.term(this, 
					"select", 
					func.getFunction().getTerm(), 
					nodeUnequalToStoreIndex.getTerm());
			mgdScript.unlock(this);
			final NODE selectOverStoreNode = (NODE) mEqNodeAndFunctionFactory
					.getOrConstructEqNode(selectOverStoreTerm);
			final NODE selectInsideStoreNode = (NODE) mEqNodeAndFunctionFactory
					.getOrConstructEqNode(selectInsideStoreTerm);
			newConstraint = addEqualityFlat(selectOverStoreNode, selectInsideStoreNode, newConstraint);
		}
		
		return newConstraint;
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
	private EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> propagateDisequalites(
			final EqConstraint<ACTION, NODE, FUNCTION> inputState, 
			final NODE representative1,
			final NODE representative2) {
		return propagateDisEqualites(inputState, representative1, representative2, true);
	}

	private EqConstraint<ACTION, NODE, FUNCTION> propagateDisequalitesFlat(
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

	public EqStateFactory<ACTION> getEqStateFactory() {
		return mEqStateFactory;
	}

	public void setEqStateFactory(EqStateFactory<ACTION> eqStateFactory) {
		mEqStateFactory = eqStateFactory;
	}

	public EqNodeAndFunctionFactory getEqNodeAndFunctionFactory() {
		return mEqNodeAndFunctionFactory;
	}
}
