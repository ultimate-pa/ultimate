package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.CongruenceClosure;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class WeqCongruenceClosure<ACTION extends IIcfgTransition<IcfgLocation>, NODE extends IEqNodeIdentifier<NODE>>
		extends CongruenceClosure<NODE> {

	private final WeakEquivalenceGraph<ACTION, NODE> mWeakEquivalenceGraph;
	private final EqConstraintFactory<ACTION, NODE> mFactory;

	private final LiteralManager<NODE> mLiteralManager;
	private final Collection<NODE> mAllLiterals;

	private final HashRelation<Object, NODE> mNodeToDependents;

	/**
	 * Create an empty ("True"/unconstrained) WeqCC.
	 *
	 * @param factory
	 */
	public WeqCongruenceClosure(final EqConstraintFactory<ACTION, NODE> factory) {
		super();
		assert factory != null;
		mWeakEquivalenceGraph = new WeakEquivalenceGraph<>(this, factory);
		mFactory = factory;
		mLiteralManager = mFactory.getLiteralManager();
		mAllLiterals = new HashSet<>();
		mNodeToDependents = new HashRelation<>();
	}

	/**
	 * Create an inconsistent ("False") WeqCC.
	 *
	 * @param isInconsistent
	 */
	public WeqCongruenceClosure(final boolean isInconsistent) {
		super(true);
		if (!isInconsistent) {
			throw new IllegalArgumentException("use other constructor!");
		}
		mWeakEquivalenceGraph = null;
		mFactory = null;
		mLiteralManager = null;
		mAllLiterals = null;
		mNodeToDependents = null;
	}


	/**
	 * Create a WeqCC using the given CongruenceClosure as ground partial arrangement (gpa) and an empty
	 * WeakEquivalenceGraph.
	 *
	 * @param original
	 * @param factory
	 */
	public WeqCongruenceClosure(final CongruenceClosure<NODE> original,
			final EqConstraintFactory<ACTION, NODE> factory) {
		super(original);
		assert factory != null;
		mWeakEquivalenceGraph = new WeakEquivalenceGraph<>(this, factory);
		mFactory = factory;
		mLiteralManager = mFactory.getLiteralManager();
		mAllLiterals = original.getAllElementRepresentatives().stream()
				.filter(elem -> mLiteralManager.isLiteral(elem))
				.collect(Collectors.toCollection(HashSet::new));

		mNodeToDependents = new HashRelation<>();
		initializeNodeToDependents(original);
	}

	/**
	 * Create a WeqCC using the given CongruenceClosure as ground partial arrangement (gpa) and the given
	 * WeakEquivalenceGraph.
	 *
	 * @param original
	 */
	public WeqCongruenceClosure(final CongruenceClosure<NODE> original,
			final WeakEquivalenceGraph<ACTION, NODE> weqGraph,
			final EqConstraintFactory<ACTION, NODE> factory) {
		super(original);
		assert factory != null;
		if (original.isInconsistent()) {
			throw new IllegalArgumentException("use other constructor!");
		}
		// we need a fresh instance here, because we cannot set the link in the weq graph to the right cc instance..
		mWeakEquivalenceGraph = new WeakEquivalenceGraph<>(this, weqGraph);
		mFactory = factory;
		mLiteralManager = mFactory.getLiteralManager();
		mAllLiterals = original.getAllElementRepresentatives().stream()
				.filter(elem -> mLiteralManager.isLiteral(elem))
				.collect(Collectors.toCollection(HashSet::new));
		mNodeToDependents = new HashRelation<>();
		initializeNodeToDependents(original);
	}


	/**
	 * copy constructor
	 *
	 * @param original
	 */
	public WeqCongruenceClosure(final WeqCongruenceClosure<ACTION, NODE> original) {
		super(original);
		assert original.mFactory != null;
		mFactory = original.mFactory;
		mLiteralManager = mFactory.getLiteralManager();
		mWeakEquivalenceGraph = new WeakEquivalenceGraph<>(this, original.mWeakEquivalenceGraph);
		mAllLiterals = new HashSet<>(original.mAllLiterals);
		mNodeToDependents = new HashRelation<>(original.mNodeToDependents);
	}


	private void initializeNodeToDependents(final CongruenceClosure<NODE> original) {
		for (final NODE e : original.getAllElements()) {
			if (!e.isDependent()) {
				continue;
			}
			for (final NODE supp : e.getSupportingNodes()) {
				mNodeToDependents.addPair(supp, e);
			}
		}
	}

	public Term getTerm(final Script script) {
		final List<Term> allConjuncts =  new ArrayList<>();
		allConjuncts.addAll(EqConstraint.partialArrangementToCube(script, this));

		final List<Term> weakEqConstraints = mWeakEquivalenceGraph.getWeakEquivalenceConstraintsAsTerms(script);
		allConjuncts.addAll(weakEqConstraints);

		final Term result= SmtUtils.and(script, allConjuncts.toArray(new Term[allConjuncts.size()]));
		return result;
	}

	@Override
	protected boolean addElement(final NODE elem) {
		final boolean elemIsNew = super.addElement(elem);
		if (!elemIsNew) {
			return false;
		}

		if (mLiteralManager.isLiteral(elem)) {
			for (final NODE other : mLiteralManager.getDisequalities(elem, getAllLiteralElements())) {
				reportDisequality(elem, other);
			}
			mAllLiterals.add(elem);
		}
		return true;
	}

	private Collection<NODE> getAllLiteralElements() {
		return mAllLiterals;
	}

	@Override
	protected CongruenceClosure<NODE> alignElementsAndFunctions(
			final CongruenceClosure<NODE> otherCC) {
		if (!(otherCC instanceof WeqCongruenceClosure)) {
			return super.alignElementsAndFunctions(otherCC);
		}
		final WeqCongruenceClosure<ACTION, NODE> other =
				(WeqCongruenceClosure<ACTION, NODE>) otherCC;

		final WeqCongruenceClosure<ACTION, NODE> result = new WeqCongruenceClosure<>(this);
		assert result.sanityCheck();

		other.getAllElements().stream().forEach(elem -> result.addElement(elem));
//		other.getAllFunctions().stream().forEach(func -> result.addFunction(func));

		assert result.sanityCheck();
		return result;
	}

	public void renameVariables(final Map<Term, Term> substitutionMapping) {
		transformElementsAndFunctions(
				node -> node.renameVariables(substitutionMapping));//,
//				function -> function.renameVariables(substitutionMapping));
		mWeakEquivalenceGraph.renameVariables(substitutionMapping);
	}

//	public void reportWeakEquivalence(final NODE array1, final NODE array2, final List<NODE> storeIndex) {
	public void reportWeakEquivalence(final NODE array1, final NODE array2, final NODE storeIndex) {
		assert array1.isFunction() && array2.isFunction();
//		for (final NODE storeIndexNode : storeIndex) {
//			getRepresentativeAndAddElementIfNeeded(storeIndexNode);
//		}
		getRepresentativeAndAddElementIfNeeded(storeIndex);

//		addFunction(array1);
//		addFunction(array2);
		addElement(array1);
		addElement(array2);

		mWeakEquivalenceGraph.reportWeakEquivalence(array1, array2, storeIndex);
		reportAllArrayEqualitiesFromWeqGraph();
	}


	private void addWeakEquivalence(final Doubleton<NODE> key,
				final WeakEquivalenceGraph<ACTION, NODE>.WeakEquivalenceEdgeLabel value) {
		mWeakEquivalenceGraph.reportWeakEquivalence(key, value);
		reportAllArrayEqualitiesFromWeqGraph();
	}

	@Override
	public boolean reportEquality(final NODE node1, final NODE node2) {
		assert node1.hasSameTypeAs(node2);
		boolean madeChanges = false;

//		final NestedMap2<NODE, NODE, Set<List<NODE>>> oldCcChild =
//				ccchildDeepCopy(mFunctionToRepresentativeToCcChildren);
		final NODE oldRep1 = mElementTVER.getRepresentative(node1);
		final NODE oldRep2 = mElementTVER.getRepresentative(node2);

		madeChanges |= super.reportEquality(node1, node2);
		assert sanityCheck();

		if (!madeChanges) {
			return false;
		}

		/*
		 *  there are three types of propagations related to weak equivalences, corresponding to the rules
		 *   ext, roweq and roweq-1
		 */

		/*
		 * propagations according to the roweq rule:
		 */
//		final HashRelation<NODE, NODE> propagatedEqualitiesFromWeqEdges =
//		mWeakEquivalenceGraph.applyRoweqPropagationsOnReportEquality(node1, node2);
//		reportAllArrayEqualitiesFromWeqGraph();
//		for (final Entry<NODE, NODE> eq : propagatedEqualitiesFromWeqEdges.entrySet()) {
//			this.reportEquality(eq.getKey(), eq.getValue());
//		}
		assert sanityCheck();

		/*
		 * propagations according to the ext rule:
		 */
		reportGpaChangeToWeqGraphAndPropagateArrayEqualities(
				(final CongruenceClosure<NODE> cc) -> cc.reportEquality(node1, node2));

		/*
		 * propagations according to the roweq-1 rule:
		 *
		 *  extensionality-related propagation:
 		 *  We view an equality a[i] = b[i] as a weak equivalence a --q!=i-- b --> update the corresponding weq edge
		 *  accordingly, or introduce one.
		 */
//		for (final Entry<NODE, NODE> funcPair : getPairsWithMatchingType(mAllFunctions, false, true)) {
//			assert funcPair.getKey().getSort().equals(funcPair.getValue().getSort());
//
//			final Set<List<NODE>> ccchildren1 = getCcChildren(funcPair.getKey(), oldRep1, oldCcChild, true);
//			final Set<List<NODE>> ccchildren2 = getCcChildren(funcPair.getValue(), oldRep2, oldCcChild, true);
//
//			for (final List<NODE> ccc1 : ccchildren1) {
//				for (final List<NODE> ccc2 : ccchildren2) {
//					if (vectorsAreCongruent(ccc1, ccc2)) {
//						/*
//						 * That the arguments are congruent will always be the case when this reportEqualityRec-call
//						 * came from a congruence propagation, but we need to check it here, because the equality may
//						 * have been added directly.
//						 */
//						mWeakEquivalenceGraph.strengthenEdgeWithExceptedPoint(funcPair.getKey(), funcPair.getValue(),
//								ccc1);
//					}
//				}
//			}
//		}
//		reportAllArrayEqualitiesFromWeqGraph();

		return true;
	}

//	@Override
//	protected Set<Entry<NODE, NODE>> getFunctionPairsWithMatchingType() {
//		return CrossProducts.binarySelectiveCrossProduct(getAllFunctions(), false, true).entrySet().stream()
//			.filter(en -> en.getKey().getTerm().getSort().equals(en.getValue().getTerm().getSort()))
//			.collect(Collectors.toSet());
//	}

	private void reportAllArrayEqualitiesFromWeqGraph() {
		while (mWeakEquivalenceGraph.hasArrayEqualities()) {
			final Entry<NODE, NODE> aeq = mWeakEquivalenceGraph.pollArrayEquality();
			reportEquality(aeq.getKey(), aeq.getValue());
			if (isInconsistent()) {
				return;
			}
		}
	}



	@Override
	public boolean reportDisequality(final NODE elem1, final NODE elem2) {
		boolean madeChanges = false;

		madeChanges |= super.reportDisequality(elem1, elem2);
		assert sanityCheck();

		if (!madeChanges) {
			return false;
		}

		if (isInconsistent()) {
			// no need for further propagations
			return true;
		}

		reportGpaChangeToWeqGraphAndPropagateArrayEqualities(
				(final CongruenceClosure<NODE> cc) -> cc.reportDisequality(elem1, elem2));

		return true;
	}


//	@Override
//	protected boolean reportDisequality(final NODE elem1, final NODE elem2,
//			final NestedMap2<NODE, NODE, Set<List<NODE>>> oldCcChild) {
//		boolean madeChanges = false;
//
//		madeChanges |= super.reportDisequalityRec(elem1, elem2, oldCcChild);
//
//		if (!madeChanges) {
//			return false;
//		}
//
//		if (isInconsistent()) {
//			return true;
//		}
//
//		// TODO might be optimized perhaps, because reportDisequality does the following call, too..
//		reportGpaChangeToWeqGraphAndPropagateArrayEqualities(
//				(final CongruenceClosure<NODE> cc) -> cc.reportDisequality(elem1, elem2));
//
//		return true;
//	}

//	@Override
//	public boolean reportFunctionEquality(final FUNCTION func1, final FUNCTION func2) {
//		boolean madeChanges = false;
//
//		madeChanges |= super.reportFunctionEquality(func1, func2);
//		assert sanityCheck();
//
//		if (!madeChanges) {
//			return false;
//		}
//
//		if (isInconsistent()) {
//			// no need for further propagations
//			return true;
//		}
//
//		reportGpaChangeToWeqGraphAndPropagateArrayEqualities(
//				(final CongruenceClosure<NODE> cc) -> cc.reportFunctionEquality(func1, func2));
//		return true;
//	}

//	@Override
//	public boolean reportFunctionDisequality(final FUNCTION func1, final FUNCTION func2) {
//		boolean madeChanges = false;
//
//		madeChanges |= super.reportFunctionDisequality(func1, func2);
//		assert sanityCheck();
//
//		if (!madeChanges) {
//			return false;
//		}
//
//		if (isInconsistent()) {
//			// no need for further propagations
//			return true;
//		}
//
//		reportGpaChangeToWeqGraphAndPropagateArrayEqualities(
//				(final CongruenceClosure<NODE> cc) -> cc.reportFunctionDisequality(func1, func2));
//		return true;
//	}

	/**
	 * Updates the weq-graph wrt. a change in the ground partial arrangement.
	 * Immediately propagates array equalities if some have occurred.
	 *
	 * @param reporter
	 * @return
	 */
	private boolean reportGpaChangeToWeqGraphAndPropagateArrayEqualities(
			final Predicate<CongruenceClosure<NODE>> reporter) {
		boolean madeChanges = false;
		assert !mWeakEquivalenceGraph.hasArrayEqualities();
		madeChanges |= mWeakEquivalenceGraph.reportChangeInGroundPartialArrangement(reporter);
		reportAllArrayEqualitiesFromWeqGraph();
		assert sanityCheck();
		return madeChanges;
	}

	@Override
	public boolean isTautological() {
		return super.isTautological() && mWeakEquivalenceGraph.isEmpty();
	}



	@Override
	public boolean isStrongerThan(final CongruenceClosure<NODE> other) {
		if (!(other instanceof WeqCongruenceClosure<?, ?>)) {
			throw new IllegalArgumentException();
		}
		if (!super.isStrongerThan(other)) {
			return false;
		}

		final WeqCongruenceClosure<ACTION, NODE> otherWeqCc =
				(WeqCongruenceClosure<ACTION, NODE>) other;

		if (!mWeakEquivalenceGraph.isStrongerThan(otherWeqCc.mWeakEquivalenceGraph)) {
			return false;
		}
		return true;
	}



//	@Override
//	public boolean removeFunction(final FUNCTION func) {
//		if (!hasFunction(func)) {
//			return false;
//		}
//
//		/*
//		 * When removing this function we will also remove all function nodes that depend on it. In this first step
//		 * we attempt to conserve information about those nodes if possible by adding nodes with other functions but the
//		 * same arguments.
//		 *
//		 * Conditions to add a node b[i1, ..., in]:
//		 *  (a is the function we are about to remove)
//		 * <li> a[i1, ..., in] is present in this weqCc and is part of a non-tautological constraint
//		 * <li> the current weqCc allows us to conclude a[i1, .., in] = b[i1, ..,in]
//		 *  <p>
//		 *   that is the case if one of the following conditions holds
//		 * <li> the strong equivalence a = b is implied by this weqCc (it is enough to propagate for one other function
//		 *   in the equivalence class of a)
//		 * <li> there is a weak equivalence edge between a and b, and it allows weak congruence propagation of the above
//		 *  equality
//		 */
//		final Set<NODE> constrainedFuncAppNodes = mFunctionToFuncApps.getImage(func).stream()
//				.filter(this::isConstrained).collect(Collectors.toSet());
//
//		// is func equal to some other function?
//		final Optional<FUNCTION> equalFuncOpt = mFunctionTVER.getEquivalenceClass(func).stream()
//				.filter(f -> !f.equals(func)).findAny();
//		final FUNCTION equalFunc = equalFuncOpt.isPresent() ? equalFuncOpt.get() : null;
//
//		for (final NODE fan : constrainedFuncAppNodes) {
//			if (equalFunc != null) {
//				final NODE nodeWithEqualFunc = mFactory.getEqNodeAndFunctionFactory()
//						.getFuncAppElement(equalFunc, fan.getArguments());
//				addElement(nodeWithEqualFunc);
//			}
//
//			for (final Entry<FUNCTION, WeakEquivalenceGraph<ACTION, NODE>.WeakEquivalenceEdgeLabel> weqEdge
//					:
//						mWeakEquivalenceGraph.getAdjacentWeqEdges(func).entrySet()) {
//				if (weqEdge.getValue().impliesEqualityOnThatPosition(fan.getArguments())) {
//					final NODE nodeWithWequalFunc = mFactory.getEqNodeAndFunctionFactory()
//						.getFuncAppElement(weqEdge.getKey(), fan.getArguments());
//					addElement(nodeWithWequalFunc);
//				}
//			}
//		}
//
//
//		/*
//		 * Project func from the weak equivalence graph.
//		 * We need to make a copy of the ground partial arrangement, because ..
//		 */
//		final CongruenceClosure<NODE,FUNCTION> copy = new CongruenceClosure<>(this);
//		copy.removeFunction(func);
//		mWeakEquivalenceGraph.projectFunction(func, copy);
//		assert projectedFunctionIsGoneFromWeqGraph(func, mWeakEquivalenceGraph);
//
//		/*
//		 * the following code is c/p'ed from super.removeFunction, with one marked exception (see below)
//		 */
//
//		// remove all elements that depend on the function
//		final Set<NODE> funcAppsWithFuncCopy = new HashSet<>(mFunctionToFuncApps.getImage(func));
//		for (final NODE funcApp : funcAppsWithFuncCopy) {
//			// change from original: (added second argument)
//			removeElement(funcApp, copy);
//			assert projectedFunctionIsGoneFromWeqGraph(func, mWeakEquivalenceGraph);
//		}
//		for (final NODE dependent : new HashSet<>(mNodeToDependents.getImage(func))) {
//			removeElement(dependent, copy);
//		}
//		mNodeToDependents.removeDomainElement(func);
//
//
//		// remove from the function equivalence relation
//		mFunctionTVER.removeElement(func);
//
//		mFunctionToRepresentativeToCcPars.remove(func);
//		mFunctionToRepresentativeToCcChildren.remove(func);
//		mFunctionToFuncApps.removeDomainElement(func);
//		assert projectedFunctionIsGoneFromWeqGraph(func, mWeakEquivalenceGraph);
//		assert sanityCheck();
//		return true;
//	}




	@Override
	public boolean removeElement(final NODE elem) {
		if (!hasElement(elem) && mNodeToDependents.getImage(elem).isEmpty()) {
			return false;
		}
		final CongruenceClosure<NODE> copy = new CongruenceClosure<>(this);
		copy.removeElement(elem);
		return removeElement(elem, copy);
	}

	private boolean projectedFunctionIsGoneFromWeqGraph(final NODE func,
			final WeakEquivalenceGraph<ACTION, NODE> weakEquivalenceGraph) {
		for (final Entry<Doubleton<NODE>,
				WeakEquivalenceGraph<ACTION, NODE>.WeakEquivalenceEdgeLabel> edge :
					weakEquivalenceGraph.getEdges().entrySet()) {
//			if (edge.getValue().getAppearingFunctions().contains(func)) {
			if (edge.getValue().getAppearingNodes().contains(func)) {
				assert false;
				return false;
			}
		}
		return true;
	}

	private boolean removeElement(final NODE elem, final CongruenceClosure<NODE> copy) {
		if (hasElement(elem)) {
//			mWeakEquivalenceGraph.projectElement(elem, copy);

			final boolean elemWasRepresentative = mElementTVER.isRepresentative(elem);
			final NODE newRep = mElementTVER.removeElement(elem);
			mAuxData.removeElement(elem, elemWasRepresentative, newRep);

			for (final NODE parent : elem.getParents()) {
				removeElement(parent);
			}


			final Collection <NODE> nodesToAdd = collectNodesToAddAtFunctionRemoval(elem, newRep);
			for (final NODE node : nodesToAdd) {
				addElement(node);
			}

			/*
			 * Project func from the weak equivalence graph.
			 * We need to make a copy of the ground partial arrangement, because ..
			 */
			//				final CongruenceClosure<NODE> copy = new CongruenceClosure<>(this);
			//				copy.removeFunction(func);
			mWeakEquivalenceGraph.projectFunction(elem, copy);
			assert projectedFunctionIsGoneFromWeqGraph(elem, mWeakEquivalenceGraph);

			for (final NODE dependent : new HashSet<>(mNodeToDependents.getImage(elem))) {
				removeElement(dependent, copy);
			}
			mNodeToDependents.removeDomainElement(elem);


			assert projectedFunctionIsGoneFromWeqGraph(elem, mWeakEquivalenceGraph);

			mAllLiterals.remove(elem);
		}

		for (final NODE dependent : new HashSet<>(mNodeToDependents.getImage(elem))) {
			removeElement(dependent, copy);
		}
		mNodeToDependents.removeDomainElement(elem);
		mNodeToDependents.removeRangeElement(elem);


		assert elementIsFullyRemoved(elem);
		return true;
	}

	/**
	 * When removing a function we will also remove all function nodes that depend on it. In this first
	 * step we attempt to conserve information about those nodes if possible by adding nodes with other
	 * functions but the same arguments.
	 *
	 * Conditions to add a node b[i1, ..., in]:
	 *  (a is the function we are about to remove)
	 * <li> a[i1, ..., in] is present in this weqCc and is part of a non-tautological constraint
	 * <li> the current weqCc allows us to conclude a[i1, .., in] = b[i1, ..,in]
	 *  <p>
	 *   that is the case if one of the following conditions holds
	 * <li> the strong equivalence a = b is implied by this weqCc (it is enough to propagate for one other
	 * 	function in the equivalence class of a)
	 * <li> there is a weak equivalence edge between a and b, and it allows weak congruence propagation of
	 *	 the above equality
	 * @param newRep
	 */
	private Collection<NODE> collectNodesToAddAtFunctionRemoval(final NODE elem, final NODE newRep) {
		final Collection<NODE> nodesToAdd = new ArrayList<>();

		final Set<NODE> constrainedFuncAppNodes = mAuxData.getAfCcPars(elem).stream()
				.filter(this::isConstrained)
				.collect(Collectors.toSet());

		final NODE equalFunc = newRep;

		for (final NODE fan : constrainedFuncAppNodes) {
			if (equalFunc != null) {
				final NODE nodeWithEqualFunc = mFactory.getEqNodeAndFunctionFactory()
						.getFuncAppElement(equalFunc, fan.getArgument());
//						.getFuncAppElementDetermineIsFunctionYourself(equalFunc, fan.getArguments());
//				addElement(nodeWithEqualFunc);
				nodesToAdd.add(nodeWithEqualFunc);
			}

			for (final Entry<NODE, WeakEquivalenceGraph<ACTION, NODE>.WeakEquivalenceEdgeLabel> weqEdge
					:
						mWeakEquivalenceGraph.getAdjacentWeqEdges(elem).entrySet()) {
				if (weqEdge.getValue().impliesEqualityOnThatPosition(Collections.singletonList(fan.getArgument()))) {
					final NODE nodeWithWequalFunc = mFactory.getEqNodeAndFunctionFactory()
							.getFuncAppElement(weqEdge.getKey(), fan.getArgument());
//					addElement(nodeWithWequalFunc);
					nodesToAdd.add(nodeWithWequalFunc);
				}
			}
		}
		return nodesToAdd;
	}

	@Override
	public boolean isConstrained(final NODE elem) {
		if (super.isConstrained(elem)) {
			return true;
		}
		if (mWeakEquivalenceGraph.isConstrained(elem)) {
			return true;
		}
		return false;
	}

	@Override
	protected void registerNewElement(final NODE elem) {
		super.registerNewElement(elem);

		if (elem.isDependent()) {
			for (final NODE supp : elem.getSupportingNodes()) {
				mNodeToDependents.addPair(supp, elem);
			}
		}

		if (!elem.isFunctionApplication()) {
			// nothing to do
			return;
		}

		/*
		 * As the new element is a function application, we might be able to infer equalities for it through weak
		 * equivalence.
		 */
//		for (final Entry<NODE, WeakEquivalenceGraph<ACTION, NODE>.WeakEquivalenceEdgeLabel> edge :
//				mWeakEquivalenceGraph.getAdjacentWeqEdges(elem.getAppliedFunction()).entrySet()) {
//			Set<NODE> candidateSet = null;
//
//			/*
//			 * obtain "candidate elements", i.e, elements that might be equivalent to elem insofar their arguments are
//			 * equal and their applied function is weakly equivalent to elem's applied function
//			 */
//			for (int i = 0; i < elem.getArguments().size(); i++) {
//				final NODE argRep = mElementTVER.getRepresentative(elem.getArguments().get(i));
//				final Set<NODE> newCandidates = getCcParsForArgumentPosition(edge.getKey(), argRep, i);
//				if (candidateSet == null) {
//					candidateSet = new HashSet<>(newCandidates);
//				} else {
//					candidateSet.retainAll(newCandidates);
//				}
//			}
//
//			for (final NODE c : candidateSet) {
//				if (c == elem) {
//					continue;
//				}
//
//				/*
//				 * check if the weak equivalence is strong enough to allow propagation of elem = c
//				 * (elem and c have the form  a[...], b[...], where we have a weak equivalence edge (current edge)
//				 *  between a and c)
//				 */
//				if (edge.getValue().impliesEqualityOnThatPosition(elem.getArguments())) {
//					reportEquality(elem, c);
//				}
//			}
//		}
	}


	@Override
	public void transformElementsAndFunctions(final Function<NODE, NODE> elemTransformer) {
//			final Function<NODE, NODE> functionTransformer) {
//		super.transformElementsAndFunctions(elemTransformer, functionTransformer);
		super.transformElementsAndFunctions(elemTransformer);
//		final CongruenceClosure<NODE> ccResult = super.transformElementsAndFunctions(elemTransformer);

		for (final Entry<Object, NODE> en : new HashRelation<>(mNodeToDependents).entrySet()) {
			mNodeToDependents.removePair(en.getKey(), en.getValue());
			if (en.getKey() instanceof IEqNodeIdentifier<?>) {
				mNodeToDependents.addPair(elemTransformer.apply((NODE) en.getKey()),
						elemTransformer.apply(en.getValue()));
			} else {
				throw new AssertionError();
			}
		}
	}

	@Override
	protected boolean elementIsFullyRemoved(final NODE elem) {
		for (final Entry<Object, NODE> en : mNodeToDependents.entrySet()) {
			if (en.getKey().equals(elem) || en.getValue().equals(elem)) {
				assert false;
				return false;
			}
		}
		return super.elementIsFullyRemoved(elem);
	}

	@Override
	public WeqCongruenceClosure<ACTION, NODE> join(final CongruenceClosure<NODE> otherCC) {
		if (!(otherCC instanceof WeqCongruenceClosure)) {
			throw new IllegalArgumentException();
		}
		final WeqCongruenceClosure<ACTION, NODE> other =
				(WeqCongruenceClosure<ACTION, NODE>) otherCC;

		return new WeqCongruenceClosure<>(super.join(other), mWeakEquivalenceGraph.join(other.mWeakEquivalenceGraph),
				mFactory);
	}

	@Override
	public WeqCongruenceClosure<ACTION, NODE> meet(final CongruenceClosure<NODE> other) {
		if (!(other instanceof WeqCongruenceClosure)) {
			throw new IllegalArgumentException();
		}

		final CongruenceClosure<NODE> gPaMeet = super.meet(other);
		if (gPaMeet.isInconsistent()) {
				return new WeqCongruenceClosure<>(true);
		}

		assert !this.mWeakEquivalenceGraph.hasArrayEqualities();
		/*
		 * strategy: conjoin all weq edges of otherCC to a copy of this's weq graph
		 */

		final WeqCongruenceClosure<ACTION, NODE> newWeqCc =
				(WeqCongruenceClosure<ACTION, NODE>) gPaMeet;

		final WeqCongruenceClosure<ACTION, NODE> otherWeqCc =
				(WeqCongruenceClosure<ACTION, NODE>) other;

		// report all weq edges from other
		for (final Entry<Doubleton<NODE>, WeakEquivalenceGraph<ACTION, NODE>.WeakEquivalenceEdgeLabel> edge
				:
					otherWeqCc.mWeakEquivalenceGraph.getEdges().entrySet()) {
			newWeqCc.addWeakEquivalence(edge.getKey(), edge.getValue());
		}

		newWeqCc.mWeakEquivalenceGraph.close();
		newWeqCc.reportAllArrayEqualitiesFromWeqGraph();

		if (newWeqCc.isInconsistent()) {
			return new WeqCongruenceClosure<>(true);
		}
		return newWeqCc;
	}

	@Override
	public boolean sanityCheck() {
		boolean res = super.sanityCheck();
		if (mWeakEquivalenceGraph != null) {
			res &= mWeakEquivalenceGraph.sanityCheck();
		}
		return res;
	}

//	@Override
//	protected boolean haveSameType(final NODE e1, final NODE e2) {
//		if (!e1.getTerm().getSort().equals(e2.getTerm().getSort())) {
//			return false;
//		}
//		return super.haveSameType(e1, e2);
//	}

	@Override public String toString() {
		if (isTautological()) {
			return "True";
		}
		if (isInconsistent()) {
			return "False";
		}
		final StringBuilder sb = new StringBuilder();
		sb.append("Partial arrangement:\n");
		sb.append(super.toString());
		sb.append("\n");
		sb.append("Weak equivalences:\n");
		sb.append(mWeakEquivalenceGraph.toString());
		return sb.toString();
	}

//	public Map<NODE, Set<NODE>> getCcParsForNode(NODE node1) {
	/**
	 * TODO: this could be optimized, through extra maps perhaps
	 * @param node1
	 * @return ccpar -> functions
	 */
//	public HashRelation<NODE, NODE> getCcParsForNode(NODE node1) {
//	public Set<NODE> getCcParsForNode(final NODE node1) {
//		final Set<NODE> result = new HashSet<>();
//		for (final NODE key1 : mFunctionToRepresentativeToCcPars.keySet()) {
//			for (final NODE key2 : mFunctionToRepresentativeToCcPars.get(key1).keySet()) {
//				result.addAll(mFunctionToRepresentativeToCcPars.get(key1, key2));
//			}
//		}
//		return result;
////		HashRelation<NODE, NODE> result = new HashRelation<>();
////
////		for (funcTo)
////
////		return result;
//	}
}