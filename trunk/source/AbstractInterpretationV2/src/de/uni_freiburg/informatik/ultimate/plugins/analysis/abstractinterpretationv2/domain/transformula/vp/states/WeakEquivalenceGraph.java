package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSort;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.IEqFunctionIdentifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.CongruenceClosure;
import de.uni_freiburg.informatik.ultimate.util.datastructures.CrossProducts;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ICongruenceClosureElement;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * (short: weq graph)
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class WeakEquivalenceGraph<ACTION extends IIcfgTransition<IcfgLocation>,
			NODE extends IEqNodeIdentifier<NODE, FUNCTION>,
			FUNCTION extends IEqFunctionIdentifier<NODE, FUNCTION>> {

	CCManager<NODE, FUNCTION> mCcManager = new CCManager<>();

	EqConstraintFactory<ACTION, NODE, FUNCTION> mFactory;

	private Map<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> mWeakEquivalenceEdges;

	private final HashRelation<FUNCTION, FUNCTION> mArrayEqualities;

	/**
	 * The WeqCongruenceClosure that this weq graph is part of. This may be null, if we use this weq graph as an
	 * intermediate, for example during a join or meet operation.
	 */
	private WeqCongruenceClosure<ACTION, NODE, FUNCTION> mPartialArrangement;

	/**
	 * Constructs an empty WeakEquivalenceGraph
	 * @param factory
	 */
	public WeakEquivalenceGraph(final WeqCongruenceClosure<ACTION, NODE, FUNCTION> pArr,
			final EqConstraintFactory<ACTION, NODE, FUNCTION> factory) {
		mPartialArrangement = pArr;
		mWeakEquivalenceEdges = new HashMap<>();
		mArrayEqualities = new HashRelation<>();
		assert factory != null;
		mFactory = factory;
		assert sanityCheck();
	}

	/**
	 *
	 * @param weakEquivalenceEdges caller needs to make sure that no one else has a reference to this map -- we are
	 * 		not making a copy here.
	 * @param arrayEqualities for the special case of an intermediate weq graph during the meet operation where an
	 *      edge label became "bottom"
	 * @param factory
	 */
	private WeakEquivalenceGraph(
			final WeqCongruenceClosure<ACTION, NODE, FUNCTION> pArr,
			final Map<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> weakEquivalenceEdges,
			final HashRelation<FUNCTION, FUNCTION> arrayEqualities,
			final EqConstraintFactory<ACTION, NODE, FUNCTION> factory) {
		mWeakEquivalenceEdges = weakEquivalenceEdges;
		mArrayEqualities = arrayEqualities;
		assert factory != null;
		mFactory = factory;
		assert sanityCheck();
	}

	/**
	 * Copy constructor
	 * @param weakEquivalenceGraph
	 * @param factory
	 */
	public WeakEquivalenceGraph(//final EqConstraint<ACTION, NODE, FUNCTION> eqConstraint,
			final WeqCongruenceClosure<ACTION, NODE, FUNCTION> pArr,
			final WeakEquivalenceGraph<ACTION, NODE, FUNCTION> weakEquivalenceGraph) {
		this(pArr, weakEquivalenceGraph, true);
		assert weakEquivalenceGraph.mArrayEqualities.isEmpty();
		assert sanityCheck();
	}

	WeakEquivalenceGraph(
			final WeqCongruenceClosure<ACTION, NODE, FUNCTION> pArr,
			final WeakEquivalenceGraph<ACTION, NODE, FUNCTION> weqMeet,
			final boolean forgetArrayEqualities) {
		mPartialArrangement = pArr;
		mArrayEqualities = forgetArrayEqualities ?
				new HashRelation<>() :
					new HashRelation<>(weqMeet.mArrayEqualities);
		mWeakEquivalenceEdges = new HashMap<>();
		for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> weqEdge
				: weqMeet.mWeakEquivalenceEdges.entrySet()) {
			mWeakEquivalenceEdges.put(weqEdge.getKey(), new WeakEquivalenceEdgeLabel(weqEdge.getValue()));
		}
		mFactory = weqMeet.mFactory;
		assert sanityCheck();
	}

	/**
	 * Called when an equality "node1 = node2" has just been reported.
	 * Checks if there is a weak equivalence edge that allows a propagation because of that equality.
	 * Analogous to the standard forward congruence propagation that is done in CongruenceClosure when an element
	 * equality has been added.
	 *
	 * @param node1
	 * @param node2
	 * @return set of equalities that can be propagated (design decision: let modifications of the ground partial
	 * 		arrangement be done "outside", in the WeqCongruenceClosure instance)
	 */
	public  Set<Doubleton<NODE>> getWeakCongruencePropagations(final NODE node1, final NODE node2) {
		final Set<Doubleton<NODE>> equalitiesToBePropagated = new HashSet<>();

		for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> edge : mWeakEquivalenceEdges.entrySet()) {

			final FUNCTION func1 = edge.getKey().getOneElement();
			final FUNCTION func2 = edge.getKey().getOtherElement();

			equalitiesToBePropagated.addAll(
					congruencePropagationHelper(func1, func2, node1, node2, edge.getValue(), mPartialArrangement));
			equalitiesToBePropagated.addAll(
					congruencePropagationHelper(func2, func1, node1, node2, edge.getValue(), mPartialArrangement));
		}
		return equalitiesToBePropagated;
	}

	private Set<Doubleton<NODE>> congruencePropagationHelper(final FUNCTION func1, final FUNCTION func2,
			final NODE node1, final NODE node2, final WeakEquivalenceEdgeLabel label,
			final CongruenceClosure<NODE, FUNCTION> pa) {
		final Set<Doubleton<NODE>> newEqualitiesToBePropagated = new HashSet<>();

		final Set<NODE> e1CcParsA = pa.getCcPars(func1, mPartialArrangement.getRepresentativeElement(node1));
		final Set<NODE> e2CcParsA = pa.getCcPars(func2, mPartialArrangement.getRepresentativeElement(node2));

		if (e1CcParsA == null || e2CcParsA == null) {
			// nothing to do
			return Collections.emptySet();
		}

		final Set<NODE> e1CcParsCopy = new HashSet<>(e1CcParsA);
		final Set<NODE> e2CcParsCopy = new HashSet<>(e2CcParsA);
		for (final NODE ccpar1 : e1CcParsCopy) {
			assert ccpar1.isFunctionApplication();
			for (final NODE ccpar2 : e2CcParsCopy) {
				assert ccpar2.isFunctionApplication();

				if (!pa.argumentsAreCongruent(ccpar1, ccpar2, false)) {
					// no propagation because the arguments are not congruent
					continue;
				}
				if (!label.impliesEqualityOnThatPosition(ccpar1.getArguments())) {
					/*
					 *  no propagation because the exceptions on array equality denoted by the weq edge's label contain
					 *  the current arguments (i.e. the label, together with the gpa, does not contradict
					 *  q = ccpar1.getArguments(), where  q is the vector of weq variables)
					 */
					continue;
				}
				newEqualitiesToBePropagated.add(new Doubleton<>(ccpar1, ccpar2));
			}
		}
		return newEqualitiesToBePropagated;
	}

	public  Entry<FUNCTION, FUNCTION> pollArrayEquality() {
		if (!hasArrayEqualities()) {
			throw new IllegalStateException("check hasArrayEqualities before calling this method");
		}
		final Entry<FUNCTION, FUNCTION> en = mArrayEqualities.iterator().next();
		mArrayEqualities.removePair(en.getKey(), en.getValue());
		return en;
	}

	public boolean reportChangeInGroundPartialArrangement(final Predicate<CongruenceClosure<NODE, FUNCTION>> action) {
		assert this.sanityCheck();
		assert mPartialArrangement.sanityCheck();
		boolean madeChanges = false;
		final Map<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> weqCopy = new HashMap<>(mWeakEquivalenceEdges);
		for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> edge : weqCopy.entrySet())  {
			final WeakEquivalenceEdgeLabel newLabel = edge.getValue().reportChangeInGroundPartialArrangement(action);
			if (newLabel.isInconsistent()) {
				// edge label became inconsistent --> remove the weq edge, add a strong equivalence instead
				mWeakEquivalenceEdges.remove(edge.getKey());
				mArrayEqualities.addPair(edge.getKey().getOneElement(), edge.getKey().getOtherElement());
				madeChanges = true;
			} else {
				mWeakEquivalenceEdges.put(edge.getKey(), newLabel);
				// TODO is the madeChanges flag worth this effort?.. should we just always say "true"?..
				madeChanges |= !newLabel.isStrongerThan(edge.getValue()) || !edge.getValue().isStrongerThan(newLabel);
			}
			assert mPartialArrangement.sanityCheck();
		}
		assert sanityCheck();
		return madeChanges;
	}

	/**
	 * Project the given function (array) from this weq graph.
	 * <li> remove edges that are adjacent to the given function
	 * <li> project the function from all the labels of the remaining edges
	 * <li> additionally, at the first step try to carry over information via weak congruence to other arrays by
	 * 		introducing fresh terms
	 *
	 * @param func function (array) to be projected
	 * @param groundPartialArrangement the gpa that should be assumed for the projection (might be different from
	 * 		mPartialArrangement, or mPartialArrangement might be null..)
	 */
	public void projectFunction(final FUNCTION func, final CongruenceClosure<NODE, FUNCTION> groundPartialArrangement) {
		final Map<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> edgesCopy = new HashMap<>(mWeakEquivalenceEdges);
		for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> en : edgesCopy.entrySet()) {
			if (en.getKey().getOneElement().equals(func) || en.getKey().getOtherElement().equals(func)) {
				mWeakEquivalenceEdges.remove(en.getKey());
			} else {
				en.getValue().projectFunction(func, groundPartialArrangement);
			}
		}
		assert projectedFunctionIsFullyGone(func);
		assert sanityCheck();
	}

	private boolean projectedFunctionIsFullyGone(final FUNCTION func) {
		for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> edge : mWeakEquivalenceEdges.entrySet()) {
			if (edge.getKey().getOneElement().equals(func) || edge.getKey().getOtherElement().equals(func)) {
				assert false;
				return false;
			}
			if (edge.getValue().getAppearingFunctions().contains(func)) {
				assert false;
				return false;
			}
		}
		return true;
	}



	/**
	 * Project the given element from all weak equivalence edges.
	 * We aim to keep information about the projected element from the ground partial arrangement. We take the
	 * following steps to compute the new edge labels.
	 *  <li> compute the meet with the ground partial arrangement
	 *  <li> project out the variable to be projected elem
	 *  <li> project out all constraints that do not contain a weq-variable
	 *
	 * @param elem
	 * @param groundPartialArrangement
	 */
	public void projectElement(final NODE elem, final CongruenceClosure<NODE, FUNCTION> groundPartialArrangement) {
		for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> en : mWeakEquivalenceEdges.entrySet()) {
			en.getValue().projectElement(elem, groundPartialArrangement);
		}
		assert sanityCheck();
	}

	public void renameVariables(final Map<Term, Term> substitutionMapping) {
		final HashMap<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> weqEdgesCopy =
				new HashMap<>(mWeakEquivalenceEdges);
		for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> en : weqEdgesCopy.entrySet()) {
			mWeakEquivalenceEdges.remove(en.getKey());

			final Doubleton<FUNCTION> newDton = new Doubleton<>(
					en.getKey().getOneElement().renameVariables(substitutionMapping),
					en.getKey().getOtherElement().renameVariables(substitutionMapping));
			en.getValue().renameVariables(substitutionMapping);
			mWeakEquivalenceEdges.put(newDton, en.getValue());
		}
		assert sanityCheck();
	}

	/**
	 *
	 * @param other
	 * @param newPartialArrangement the joined partialArrangement, we need this because the edges of the the new
	 * 		weq graph have to be between the new equivalence representatives TODO
	 * @return
	 */
	WeakEquivalenceGraph<ACTION, NODE, FUNCTION> join(final WeakEquivalenceGraph<ACTION, NODE, FUNCTION> other) {
		final Map<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> newWeakEquivalenceEdges = new HashMap<>();
		for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> thisWeqEdge
				: this.mWeakEquivalenceEdges.entrySet()) {
			final WeakEquivalenceEdgeLabel correspondingWeqEdgeInOther =
					other.mWeakEquivalenceEdges.get(thisWeqEdge.getKey());
			if (correspondingWeqEdgeInOther == null) {
				continue;
			}
			newWeakEquivalenceEdges.put(thisWeqEdge.getKey(),
					thisWeqEdge.getValue().union(correspondingWeqEdgeInOther));

		}
		final WeakEquivalenceGraph<ACTION, NODE, FUNCTION> result = new WeakEquivalenceGraph<>(null,
				newWeakEquivalenceEdges, new HashRelation<>(), mFactory);
		assert result.sanityCheck();
		return result;
	}

	boolean hasArrayEqualities() {
		return !mArrayEqualities.isEmpty();
	}

	/**
	 *
	 * @return true iff this operation performed any changes on this weq graph
	 */
	boolean close() {
		if (mWeakEquivalenceEdges.isEmpty()) {
			return false;
		}
		final FloydWarshall<FUNCTION, WeakEquivalenceEdgeLabel> fw =
				new FloydWarshall<>(WeakEquivalenceEdgeLabel::isStrongerThan,
						WeakEquivalenceEdgeLabel::union,
						WeakEquivalenceEdgeLabel::meet,
						new WeakEquivalenceEdgeLabel(),
						mWeakEquivalenceEdges,
						WeakEquivalenceEdgeLabel::new);
		if (!fw.performedChanges()) {
			return false;
		}

		mWeakEquivalenceEdges = new HashMap<>();
		for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> edge : fw.getResult().entrySet()) {
			if (edge.getValue().isInconsistent()) {
				mArrayEqualities.addPair(edge.getKey().getOneElement(), edge.getKey().getOtherElement());
				continue;
			}
			assert edge.getValue().sanityCheck();
			mWeakEquivalenceEdges.put(edge.getKey(), edge.getValue());
		}
		return true;
	}

	/**
	 *
	 * @return true if this graph has no constraints/is tautological
	 */
	public boolean isEmpty() {
		return mWeakEquivalenceEdges.isEmpty() && !hasArrayEqualities();
	}

	public boolean isStrongerThan(final WeakEquivalenceGraph<ACTION, NODE, FUNCTION> other) {
		for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> otherWeqEdgeAndLabel
				: other.mWeakEquivalenceEdges.entrySet()) {
			final WeakEquivalenceEdgeLabel correspondingWeqEdgeInThis =
					this.mWeakEquivalenceEdges.get(otherWeqEdgeAndLabel.getKey());
			if (correspondingWeqEdgeInThis == null) {
				// "other" has an edge that "this" does not -- this cannot be stronger
				return false;
			}
			// if the this-edge is strictly weaker than the other-edge, we have a counterexample
			if (!correspondingWeqEdgeInThis.isStrongerThan(otherWeqEdgeAndLabel.getValue())) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Computes an implicitly conjunctive list of weak equivalence constraints. Each element in the list is the
	 * constrained induced by one weak equivalence edge in this weq graph.
	 *
	 * @param script
	 * @return
	 */
	public List<Term> getWeakEquivalenceConstraintsAsTerms(final Script script) {
		assert mArrayEqualities == null || mArrayEqualities.isEmpty();
		final List<Term> result = new ArrayList<>();
		for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> edge : mWeakEquivalenceEdges.entrySet()) {
			final List<Term> dnfAsCubeList = new ArrayList<>();
			dnfAsCubeList.addAll(edge.getValue().toDNF(script));

			final Term arrayEquation = computeArrayEquation(script, edge.getKey().getOneElement(),
					edge.getKey().getOtherElement());
			dnfAsCubeList.add(arrayEquation);

			final Term edgeFormula = SmtUtils.quantifier(script, QuantifiedFormula.FORALL,
					computeWeqIndicesForArray(edge.getKey().getOneElement()), SmtUtils.or(script, dnfAsCubeList));
			result.add(edgeFormula);
		}
		return result;
	}

	/**
	 * For the two given arrays a, b, this computes an equation a[q1, .., qn] = b[q1, ..,qn] where qi are the
	 * implicitly quantified variables of our weak equivalences (managed by getWeqVariables for dimension).
	 * Uses the array's multidimensional sort to get the right variables.
	 *
	 * @param script
	 * @param array1
	 * @param array2
	 * @return
	 */
	private Term computeArrayEquation(final Script script, final FUNCTION array1, final FUNCTION array2) {
		assert array1.getTerm().getSort().equals(array2.getTerm().getSort());
		final List<Term> indexEntries = computeWeqIndicesForArray(array1).stream().map(tv -> (Term) tv)
				.collect(Collectors.toList());
		final ArrayIndex index = new ArrayIndex(indexEntries);

		final Term select1 = SmtUtils.multiDimensionalSelect(script, array1.getTerm(), index);
		final Term select2 = SmtUtils.multiDimensionalSelect(script, array2.getTerm(), index);

		return SmtUtils.binaryEquality(script, select1, select2);
	}

	private List<TermVariable> computeWeqIndicesForArray(final FUNCTION array1) {
		final MultiDimensionalSort mdSort = new MultiDimensionalSort(array1.getTerm().getSort());

		final List<TermVariable> indexEntries = new ArrayList<>();
		for (int i = 0; i < array1.getArity(); i++) {
			indexEntries.add(mFactory.getWeqVariableForDimension(i, mdSort.getIndexSorts().get(i)));
		}
		return indexEntries;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();

		for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceGraph<ACTION, NODE, FUNCTION>.WeakEquivalenceEdgeLabel> weq :
			mWeakEquivalenceEdges.entrySet()) {
			sb.append(weq.getKey());
			sb.append("\n");
			sb.append(weq.getValue());
			sb.append("\n");
		}

		return sb.toString();
	}

	boolean sanityCheck() {
		assert mFactory != null : "factory is needed for the sanity check..";

		/*
		 * check that no weak equivalence edge contains an ELEM or FUNCTION that is not known to mPartialArrangement
		 * or is one of the special quantified variables from getVariableForDimension(..).
		 */
		if (mPartialArrangement != null) {
			for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> edge :
				mWeakEquivalenceEdges.entrySet()) {
				if (!mPartialArrangement.hasFunction(edge.getKey().getOneElement())
						|| !mPartialArrangement.hasFunction(edge.getKey().getOtherElement())) {
					assert false;
					return false;
				}
				if (!mPartialArrangement.getAllElements().containsAll(
						edge.getValue().getAppearingNodes().stream()
						.filter(node -> !mFactory.getAllWeqNodes().contains(node)).collect(Collectors.toSet()))) {
					assert false;
					return false;
				}
				if (!mPartialArrangement.getAllFunctions().containsAll(edge.getValue().getAppearingFunctions())) {
					assert false;
					return false;
				}
			}
		}

		/*
		 * Check that all the edges are between equivalence classes of mPartialArrangement
		 */

		/*
		 * Check that none of the edges has the same source and target (is a self-loop).
		 */
		for (final Doubleton<FUNCTION> dton : mWeakEquivalenceEdges.keySet()) {
			if (dton.getOneElement().equals(dton.getOtherElement())) {
				assert false;
				return false;
			}
		}

		/*
		 * check completeness of the graph ("triangle inequality")
		 */


		/*
		 * check that there are no inconsistent edge labels -- the plan is to replace them by array equalities as they
		 * occur..
		 */
		for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> edge : mWeakEquivalenceEdges.entrySet()) {
			if (edge.getValue().isInconsistent()) {
				assert false;
				return false;
			}
		}


		// is closed/triangle inequation holds
		//			if (mPartialArrangement != null) {
		//				if (close()) {
		//					assert false;
		//					return false;
		//				}
		//			}

		return true;
	}

	public  Map<FUNCTION, WeakEquivalenceEdgeLabel> getAdjacentWeqEdges(final FUNCTION appliedFunction) {
		final Map<FUNCTION, WeakEquivalenceEdgeLabel> result = new HashMap<>();
		for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> en : mWeakEquivalenceEdges.entrySet()) {
			if (en.getKey().getOneElement().equals(appliedFunction)) {
				result.put(en.getKey().getOtherElement(), en.getValue());
			}
			if (en.getKey().getOtherElement().equals(appliedFunction)) {
				result.put(en.getKey().getOneElement(), en.getValue());
			}
		}
		return result;
	}

	public  Map<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> getEdges() {
		return Collections.unmodifiableMap(mWeakEquivalenceEdges);
	}

	/**
	 *
	 * @param func1
	 * @param func2
	 * @return true iff this WeakEquivalenceGraph has an edge between func1 and func2.
	 */
	public boolean hasWeqEdgeForFunctions(final FUNCTION func1, final FUNCTION func2) {
		return mWeakEquivalenceEdges.keySet().contains(new Doubleton<FUNCTION>(func1, func2));
	}



	/**
	 * Given an edge (given through two functions) and an argument point vector_i (a list of nodes), we strengthen
	 * the edge by the disequality vector_q != vector_i (the disequality between the vector elements is a disjunction)
	 *
	 * If no edge exists between those arrays, we introduce a fresh one.
	 *
	 * @param func1 source of the edge to be strengthened
	 * @param func2 target of the edge to be strengthened
	 * @param arguments the point that is to be excepted
	 */
	public void strengthenEdgeWithExceptedPoint(final FUNCTION func1, final FUNCTION func2,
			final List<NODE> arguments) {
		final Doubleton<FUNCTION> sourceAndTarget = new Doubleton<>(func1, func2);

		final List<CongruenceClosure<NODE, FUNCTION>> paList = new ArrayList<>();
		for (int dim = 0; dim < arguments.size(); dim++) {
			final NODE currentArg = arguments.get(dim);
			final CongruenceClosure<NODE, FUNCTION> eqCC = mCcManager.getSingleDisequalityCc(
					mFactory.getWeqVariableNodeForDimension(dim, currentArg.getTerm().getSort()),
					currentArg);
			paList.add(eqCC);
		}

		strengthenEdgeLabelAndPropagateIfPossible(sourceAndTarget, paList);
	}



	private void strengthenEdgeLabelAndPropagateIfPossible(final Doubleton<FUNCTION> sourceAndTarget,
			final List<CongruenceClosure<NODE, FUNCTION>> paList) {
		assert !sourceAndTarget.getOneElement().equals(sourceAndTarget.getOtherElement());
		WeakEquivalenceEdgeLabel oldLabel = mWeakEquivalenceEdges.get(sourceAndTarget);
		if (oldLabel == null) {
			oldLabel = new WeakEquivalenceEdgeLabel();
		}
		final WeakEquivalenceEdgeLabel strengthenedEdgeLabel = oldLabel.meet(paList);

		// inconsistency check
		if (strengthenedEdgeLabel.isInconsistent()) {
			mWeakEquivalenceEdges.remove(sourceAndTarget);
			mArrayEqualities.addPair(sourceAndTarget.getOneElement(), sourceAndTarget.getOtherElement());
			return;
		}

		// replace the edge label by the strengthened version
		mWeakEquivalenceEdges.put(sourceAndTarget, strengthenedEdgeLabel);
		assert sanityCheck();

		// check for possible congruence propagations
		final Set<Doubleton<NODE>> congruencePropagations = new HashSet<>();
		for (final NODE rep : mPartialArrangement.getAllElementRepresentatives()) {
			congruencePropagations.addAll(congruencePropagationHelper(
					sourceAndTarget.getOneElement(), sourceAndTarget.getOtherElement(), rep, rep, strengthenedEdgeLabel,
					mPartialArrangement));
		}
		// do the congruence propagations we found
		for (final Doubleton<NODE> cp : congruencePropagations) {
			mPartialArrangement.reportEquality(cp.getOneElement(), cp.getOtherElement());
		}
		assert sanityCheck();
	}



	/**
	 * propagation-related checks:
	 * <li> check for congruence-like propagations
	 * <li> check if edge became inconsistent
	 *
	 * @param func1 edge source (edge is symmetric)
	 * @param func2 edge target (edge is symmetric)
	 * @param nodes position where FUNCTIONs may differ
	 */
	public void reportWeakEquivalence(final FUNCTION func1, final FUNCTION func2, final List<NODE> nodes) {
		assert func1.getArity() == func2.getArity();

		final Doubleton<FUNCTION> sourceAndTarget = new Doubleton<>(func1, func2);
		final CongruenceClosure<NODE, FUNCTION> newConstraint = computeWeqConstraintForIndex(nodes);

		strengthenEdgeLabelAndPropagateIfPossible(sourceAndTarget, Collections.singletonList(newConstraint));
	}



	/**
	 *
	 * <li> add constraint to the edge (make one if none exists)
	 * <li> check for congruence-like propagations
	 * <li> check if edge became inconsistent
	 * (the third type, extensionality-like propagations are done at reportEqualityRec/
	 * strengthenEdgeWithExceptedPoint..)
	 *
	 * @param key
	 * @param value
	 */
	public void reportWeakEquivalence(final Doubleton<FUNCTION> key,
			final WeakEquivalenceGraph<ACTION, NODE, FUNCTION>.WeakEquivalenceEdgeLabel value) {
		strengthenEdgeLabelAndPropagateIfPossible(key, value.getLabel());
	}



	/**
	 * Given a (multidimensional) index, compute the corresponding annotation for a weak equivalence edge.
	 *
	 * Example:
	 * for (i1, .., in), this should return (q1 = i1, ..., qn = in) as a list of CongruenceClosures.
	 *  (where qi is the variable returned by getWeqVariableForDimension(i))
	 *
	 * @param nodes
	 * @return
	 */
	private CongruenceClosure<NODE, FUNCTION> computeWeqConstraintForIndex(final List<NODE> nodes) {
		final CongruenceClosure<NODE, FUNCTION> result = new CongruenceClosure<>();
		for (int i = 0; i < nodes.size(); i++) {
			final NODE ithNode = nodes.get(i);
			result.reportEquality(mFactory.getWeqVariableNodeForDimension(i, ithNode.getTerm().getSort()), ithNode);
		}
		return result;
	}

	private static <NODE extends ICongruenceClosureElement<NODE, FUNCTION>, FUNCTION>
		List<CongruenceClosure<NODE, FUNCTION>> simplifyPaDisjunction(
			final List<CongruenceClosure<NODE, FUNCTION>> newLabelContents) {
		// make a copy of the list, filter out false disjuncts
		List<CongruenceClosure<NODE, FUNCTION>> newLabel = new ArrayList<>(newLabelContents).stream()
				.filter(pa -> !pa.isInconsistent()).collect(Collectors.toList());

		// if there is any true disjunct, it will annihilate all the others
		if (newLabel.stream().anyMatch(pa -> pa.isTautological())) {
			newLabel = Collections.singletonList(new CongruenceClosure<>());
		}

		return newLabel;
	}

	public boolean isConstrained(final NODE elem) {
		for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> edge : mWeakEquivalenceEdges.entrySet()) {
			if (edge.getValue().isConstrained(elem)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Represents an edge label in the weak equivalence graph.
	 * An edge label connects two arrays of the same arity(dimensionality) #a.
	 * An edge label is a tuple of length #a.
	 * Each tuple element is a set of partial arrangements. The free variables in the partial arrangements are the
	 * variables of the EqConstraint together with #a special variables that are implicitly universally quantified
	 * and range over the array positions.
	 *
	 */
	class WeakEquivalenceEdgeLabel {

		private final List<CongruenceClosure<NODE, FUNCTION>> mLabel;
		//			private final List<CongruenceClosure<NODE, FUNCTION>> mLabelWithGroundPa;

		/**
		 * Constructs an empty edge. (labeled "true")
		 */
		public WeakEquivalenceEdgeLabel() {
			mLabel = new ArrayList<>();
			mLabel.add(new CongruenceClosure<>());
			assert sanityCheck();
		}

		public boolean isConstrained(final NODE elem) {
			return mLabel.stream().anyMatch(l -> l.isConstrained(elem));
		}

		/**
		 * Copy constructor.
		 *
		 * @param original
		 */
		public WeakEquivalenceEdgeLabel(final WeakEquivalenceEdgeLabel original) {
			mLabel = new ArrayList<>(original.getLabel().size());
			for (int i = 0; i < original.getLabel().size(); i++) {
				assert !original.getLabel().get(i).isInconsistent();
				assert !original.getLabel().get(i).isTautological() || original.getLabel().size() == 1;
				mLabel.add(new CongruenceClosure<>(original.getLabel().get(i)));
			}
			assert sanityCheck();
		}

		/**
		 * Construct a weak equivalence edge from a list of label contents.
		 *
		 * Does some simplifications.
		 *
		 * @param newLabelContents
		 */
		public WeakEquivalenceEdgeLabel(final List<CongruenceClosure<NODE, FUNCTION>> newLabelContents) {
			mLabel = simplifyPaDisjunction(newLabelContents);
			assert sanityCheck();
		}

		public List<CongruenceClosure<NODE, FUNCTION>> getLabel() {
			return Collections.unmodifiableList(mLabel);
		}

		public boolean isInconsistent() {
			for (final CongruenceClosure<NODE, FUNCTION> pa : getLabel()) {
				if (!pa.isInconsistent()) {
					// we found one consistent disjunct --> this label is consistent
					return false;
				} else {
					// current cc is inconsistent
					assert getLabel().size() == 1 : "we are filtering out all but one 'bottoms', right?";
				}
			}
			return true;
		}

		public boolean impliesEqualityOnThatPosition(final List<NODE> arguments) {
			for (int i = 0; i < getLabel().size(); i++) {
				final CongruenceClosure<NODE, FUNCTION> copy = mCcManager.makeCopy(
						mCcManager.getMeet(getLabel().get(i), mPartialArrangement));
				for (int j = 0; j < arguments.size(); j++) {
					if (copy.isInconsistent()) {
						break;
					}
					final NODE argJ = arguments.get(j);
					final NODE weqVar = WeakEquivalenceGraph.this.mFactory.getWeqVariableNodeForDimension(j, argJ.getTerm().getSort());
					copy.reportEquality(weqVar, argJ);
				}

				if (copy.isInconsistent()) {
					// go on;
				} else {
					/*
					 * label did not become inconsistent when adding the equalities q1 = arg1, ... qn = argn
					 *  --> the weak equivalence is not strong enough to imply a[arg1, ..,argn] = b[arg1, .., argn]
					 *     (where a, b are the source and target of the weq edge)
					 */
					return false;
				}
			}
			return true;
		}

		/**
		 * Called when the ground partial arrangement (gpa) has changed.
		 * Checks if any entry of a weq label became inconsistent through the change, removes that entry, propagates
		 * an array equality if the whole edge became inconsistent
		 *
		 *  --> does edge inconsistency based propagations (weak equivalences becoming strong ones)
		 *  --> does not do congruence style weq propagations, those are done separately when an equality is added
		 *   to the gpa
		 *
		 * @param reportX lambda, applying one of the CongruenceClosure.report functions to some nodes for a given
		 *   CongruenceClosure object
		 * @return a fresh, updated WeqLabel, null if the label became inconsistent
		 */
		public WeakEquivalenceEdgeLabel reportChangeInGroundPartialArrangement(
				final Predicate<CongruenceClosure<NODE, FUNCTION>> reportX) {
			assert WeakEquivalenceGraph.this.sanityCheck();
			assert mPartialArrangement.sanityCheck();


			final List<CongruenceClosure<NODE, FUNCTION>> newLabel = new ArrayList<>();

			for (int i = 0; i < getLabel().size(); i++) {
				assert mPartialArrangement.sanityCheck();
				final CongruenceClosure<NODE, FUNCTION> currentPaWgpa = mCcManager.getMeet(getLabel().get(i),
						mPartialArrangement);

				if (currentPaWgpa.isInconsistent()) {
					// label element became inconsistent, don't add it to the new label
					continue;
				}

				final boolean change = reportX.test(currentPaWgpa);

				if (!change) {
					/*
					 *  no change in mLabelWgpa[i] meet gpa -- this can happen, because labelWgpa might imply an
					 *  equality that is not present in gpa..
					 *
					 *  no checks need to be made here, anyway
					 */
					newLabel.add(getLabel().get(i));
					assert !currentPaWgpa.isInconsistent();
					continue;
				}

				// add the strengthened version as the new label element
				newLabel.add(currentPaWgpa.projectToElements(mFactory.getAllWeqNodes()));

				assert mPartialArrangement.sanityCheck();
				assert WeakEquivalenceGraph.this.sanityCheck();
			}
			return new WeakEquivalenceEdgeLabel(newLabel);
		}

		/**
		 * Computes a DNF from this label as a List of conjunctive Terms.
		 *    The disjunction has the form \/_i pa_i
		 *
		 * @param script
		 * @return a DNF as a List of conjunctive Terms.
		 */
		public List<Term> toDNF(final Script script) {
			final List<Term> result = new ArrayList<>();
			for (final CongruenceClosure<NODE, FUNCTION> cc : mLabel) {
				final List<Term> cube = EqConstraint.partialArrangementToCube(script, cc);
				final Term cubeTerm = SmtUtils.and(script, cube);
				result.add(cubeTerm);
			}
			return result;
		}

		public void renameVariables(final Map<Term, Term> substitutionMapping) {
			for (int i = 0; i < getLabel().size(); i++) {
				getLabel().get(i).transformElementsAndFunctions(node -> node.renameVariables(substitutionMapping),
						func -> func.renameVariables(substitutionMapping));
			}
			assert sanityCheck();
		}

		/**
		 * Returns all NODEs that are used in this WeqEdgeLabel.
		 * Not including the special quantified variable's nodes.
		 * @return
		 */
		public Set<NODE> getAppearingNodes() {
			final Set<NODE> res = new HashSet<>();
			getLabel().forEach(pa -> res.addAll(pa.getAllElements()));
			return res;
		}

		public Set<FUNCTION> getAppearingFunctions() {
			final Set<FUNCTION> res = new HashSet<>();
			getLabel().forEach(pa -> res.addAll(pa.getAllFunctions()));
			return res;
		}

		public WeakEquivalenceEdgeLabel meet(final WeakEquivalenceEdgeLabel otherLabel) {
			assert sanityCheck();
			return meet(otherLabel.getLabel());
		}

		private WeakEquivalenceEdgeLabel meet(final List<CongruenceClosure<NODE, FUNCTION>> paList) {
			final List<CongruenceClosure<NODE, FUNCTION>> newLabelContent = new ArrayList<>();

			final List<List<CongruenceClosure<NODE, FUNCTION>>> li = new ArrayList<>(2);
			li.add(getLabel());
			li.add(paList);
			final List<List<CongruenceClosure<NODE, FUNCTION>>> cp = CrossProducts.crossProduct(li);

			for (final List<CongruenceClosure<NODE, FUNCTION>> pair : cp) {
				assert pair.size() == 2;
				newLabelContent.add(pair.get(0).meet(pair.get(1)));
			}

			final List<CongruenceClosure<NODE, FUNCTION>> newLabel = simplifyPaDisjunction(newLabelContent);

			final WeakEquivalenceEdgeLabel result =
					new WeakEquivalenceEdgeLabel(newLabel);
			assert result.sanityCheck();
			return result;
		}

		/**
		 * rule:  A isStrongerThan B
		 *     iff
		 *   forall ai exists bi. ai subseteq bi
		 * @param value
		 * @return
		 */
		public boolean isStrongerThan(final WeakEquivalenceEdgeLabel other) {
			for (final CongruenceClosure<NODE, FUNCTION> paThis : getLabel()) {
				boolean existsWeaker = false;
				for (final CongruenceClosure<NODE, FUNCTION> paOther : other.getLabel()) {
					if (paThis.isStrongerThan(paOther)) {
						existsWeaker = true;
						break;
					}
				}
				if (!existsWeaker) {
					return false;
				}
			}
			return true;
		}

		/**
		 * Computes a constraint which, for every dimension, has the union of the disjuncts of both input labels
		 *  (this and other).
		 * @param correspondingWeqEdgeInOther
		 * @return
		 */
		public WeakEquivalenceEdgeLabel union(final WeakEquivalenceEdgeLabel other) {
			final List<CongruenceClosure<NODE, FUNCTION>> unionList = new ArrayList<>(
					mLabel.size() + other.getLabel().size());
			unionList.addAll(mLabel);
			unionList.addAll(other.getLabel());

			return new WeakEquivalenceEdgeLabel(unionList);
		}


		/**
		 *  <li> compute the meet with the ground partial arrangement
		 *  <li> project out the variable to be projected elem
		 *  <li> project out all constraints that do not contain a weq-variable
		 *
		 * @param elem
		 * @param groundPartialArrangement
		 */
		public void projectElement(final NODE elem,
				final CongruenceClosure<NODE, FUNCTION> groundPartialArrangement) {
			projectHelper(cc -> cc.removeElement(elem), groundPartialArrangement);
			assert sanityCheckAfterProject(elem, groundPartialArrangement);
		}

		public void projectFunction(final FUNCTION func,
				final CongruenceClosure<NODE, FUNCTION> groundPartialArrangement) {
			projectHelper(cc -> cc.removeFunction(func), groundPartialArrangement);
			assert sanityCheckAfterProject(func, groundPartialArrangement);
		}


		/**
		 * proceeds in three steps for each label element of this weq label :
		 *  <li> constructs the meet of the element with the ground partial arrangement (gpa)
		 *  <li> applies the given removal method on that meet
		 *  <li> projects away the constraints in the resulting element that do not contain one of the weq-variables
		 *
		 * @param remove
		 * @param groundPartialArrangement
		 */
		private void projectHelper(final Consumer<CongruenceClosure<NODE, FUNCTION>> remove,
				final CongruenceClosure<NODE, FUNCTION> groundPartialArrangement) {
			final List<CongruenceClosure<NODE, FUNCTION>> newLabelContents = new ArrayList<>();
			for (int i = 0; i < getLabel().size(); i++) {
				final CongruenceClosure<NODE, FUNCTION>	meet = mCcManager.getMeet(mLabel.get(i), groundPartialArrangement);
				if (meet.isInconsistent()) {
					/* label element is inconsistent with the current gpa
					 * --> omit it from the new label
					 */
					continue;
				}
				if (meet.isTautological()) {
					// we have one "true" disjunct --> the whole disjunction is tautological
					mLabel.clear();
					mLabel.add(new CongruenceClosure<>());
					return;
				}
				remove.accept(meet);
				final CongruenceClosure<NODE, FUNCTION> newPa = meet.projectToElements(mFactory.getAllWeqNodes());
				newLabelContents.add(newPa);
			}
			mLabel.clear();
			mLabel.addAll(newLabelContents);
		}

		private boolean isTautological() {
			for (final CongruenceClosure<NODE, FUNCTION> l : getLabel()) {
				if (l.isTautological()) {
					return true;
				}
			}
			return false;
		}


		@Override
		public String toString() {
			return mLabel.toString();
		}

		private boolean sanityCheck() {
			return sanityCheck(mPartialArrangement);
		}

		private boolean sanityCheck(final CongruenceClosure<NODE, FUNCTION> groundPartialArrangement) {

			if (mLabel.stream().anyMatch(pa -> pa.isTautological()) && mLabel.size() != 1) {
				assert false : "missing normalization: if there is one 'true' disjunct, we can drop"
						+ "all other disjuncts";
			return false;
			}

			if (mLabel.stream().anyMatch(pa -> pa.isInconsistent())) {
				assert false : "missing normalization: contains 'false' disjuncts";
			return false;
			}

			return true;
		}

		private boolean sanityCheckAfterProject(final FUNCTION func,
				final CongruenceClosure<NODE, FUNCTION> groundPartialArrangement) {

			final CongruenceClosure<NODE, FUNCTION> copy = new CongruenceClosure<>(groundPartialArrangement);
			copy.removeFunction(func);
			return sanityCheck(copy);

		}

		/**
		 * special sanity check where we check as normal except that we are checkin wrt another gpa, not mPartial..
		 * but mPartial.. where elem has been projected out (as this will be done after the project in the weq
		 * labels)
		 *
		 * @param elem
		 * @param groundPartialArrangement
		 * @return
		 */
		private boolean sanityCheckAfterProject(final NODE elem,
				final CongruenceClosure<NODE, FUNCTION> groundPartialArrangement) {
			final CongruenceClosure<NODE, FUNCTION> copy = new CongruenceClosure<>(groundPartialArrangement);
			copy.removeElement(elem);
			return sanityCheck(copy);
		}
	}
}



class CCManager<NODE extends IEqNodeIdentifier<NODE, FUNCTION>,
FUNCTION extends IEqFunctionIdentifier<NODE, FUNCTION>> {
	CongruenceClosure<NODE, FUNCTION> getMeet(final CongruenceClosure<NODE, FUNCTION> cc1,
			final CongruenceClosure<NODE, FUNCTION> cc2) {
		/*
		 *  TODO: something smarter
		 *   ideas:
		 *    - caching
		 *    - updating meets alongside inputs (something that updates the cache on a report equality on the ground pa)
		 *
		 */
		final CongruenceClosure<NODE, FUNCTION> result = cc1.meet(cc2);
		return result;
	}

	public CongruenceClosure<NODE, FUNCTION> getSingleDisequalityCc(final NODE elem1, final NODE elem2) {
		final CongruenceClosure<NODE, FUNCTION> newCC = new CongruenceClosure<>();
		newCC.reportDisequality(elem1, elem2);
		return newCC;
	}

	public CongruenceClosure<NODE, FUNCTION> makeCopy(final CongruenceClosure<NODE, FUNCTION> meet) {
		if (meet.isInconsistent()) {
			return meet;
		}
		return new CongruenceClosure<>(meet);
	}

	public CongruenceClosure<NODE, FUNCTION> getSingleEqualityCc(final NODE elem1,
			final NODE  elem2) {
		final CongruenceClosure<NODE, FUNCTION> newCC = new CongruenceClosure<>();
		newCC.reportEquality(elem1, elem2);
		return newCC;
	}
}

