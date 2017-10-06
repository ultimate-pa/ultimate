package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.Set;
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
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.AbstractNodeAndFunctionFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.CongruenceClosure;
import de.uni_freiburg.informatik.ultimate.util.datastructures.CrossProducts;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.EqualityStatus;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ICongruenceClosureElement;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * (short: weq graph)
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class WeakEquivalenceGraph<ACTION extends IIcfgTransition<IcfgLocation>,
			NODE extends IEqNodeIdentifier<NODE>> {

	private final CCManager<NODE> mCcManager;

	private final EqConstraintFactory<ACTION, NODE> mFactory;
	private final AbstractNodeAndFunctionFactory<NODE, Term> mNodeAndFunctionFactory;

	private final Map<Doubleton<NODE>, WeakEquivalenceEdgeLabel> mWeakEquivalenceEdges;

	private final HashRelation<NODE, NODE> mArrayEqualities;

	/**
	 * The WeqCongruenceClosure that this weq graph is part of. This may be null, if we use this weq graph as an
	 * intermediate, for example during a join or meet operation.
	 */
	private final WeqCongruenceClosure<ACTION, NODE> mPartialArrangement;


	/**
	 * Constructs an empty WeakEquivalenceGraph
	 * @param factory
	 */
	public WeakEquivalenceGraph(final WeqCongruenceClosure<ACTION, NODE> pArr,
			final EqConstraintFactory<ACTION, NODE> factory) {
		mPartialArrangement = pArr;
		mWeakEquivalenceEdges = new HashMap<>();
		mArrayEqualities = new HashRelation<>();
		assert factory != null;
		mFactory = factory;
		mNodeAndFunctionFactory = mFactory.getEqNodeAndFunctionFactory();
		mCcManager = factory.getCcManager();
		assert sanityCheck();
	}

	/**
	 * special constructor for use in join, where we need a weq graph without a partial arrangement as an intermediate
	 *
	 * @param weakEquivalenceEdges caller needs to make sure that no one else has a reference to this map -- we are
	 * 		not making a copy here.
	 * @param arrayEqualities for the special case of an intermediate weq graph during the meet operation where an
	 *      edge label became "bottom"
	 * @param factory
	 */
	private WeakEquivalenceGraph(
//			final WeqCongruenceClosure<ACTION, NODE> pArr,
			final Map<Doubleton<NODE>, WeakEquivalenceEdgeLabel> weakEquivalenceEdges,
			final HashRelation<NODE, NODE> arrayEqualities,
			final EqConstraintFactory<ACTION, NODE> factory) {
		mPartialArrangement = null;
		mWeakEquivalenceEdges = weakEquivalenceEdges;
		mArrayEqualities = arrayEqualities;
		assert factory != null;
		mFactory = factory;
		mNodeAndFunctionFactory = mFactory.getEqNodeAndFunctionFactory();
		mCcManager = factory.getCcManager();
		assert sanityCheck();
	}

	/**
	 * Copy constructor
	 * @param weakEquivalenceGraph
	 * @param factory
	 */
	public WeakEquivalenceGraph(final WeqCongruenceClosure<ACTION, NODE> pArr,
			final WeakEquivalenceGraph<ACTION, NODE> weakEquivalenceGraph) {

		mPartialArrangement = pArr;

		assert weakEquivalenceGraph.mArrayEqualities.isEmpty();
		mArrayEqualities = new HashRelation<>();
		mWeakEquivalenceEdges = new HashMap<>();
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel> weqEdge
				: weakEquivalenceGraph.mWeakEquivalenceEdges.entrySet()) {

			// make sure that the representatives in pArr and in our new weq edges are compatible
			final Doubleton<NODE> newSoureceAndTarget = new Doubleton<>(
					pArr.getRepresentativeElement(weqEdge.getKey().getOneElement()),
					pArr.getRepresentativeElement(weqEdge.getKey().getOtherElement()));

			mWeakEquivalenceEdges.put(newSoureceAndTarget, new WeakEquivalenceEdgeLabel(weqEdge.getValue()));
		}
		mFactory = weakEquivalenceGraph.mFactory;
		mNodeAndFunctionFactory = mFactory.getEqNodeAndFunctionFactory();
		mCcManager = mFactory.getCcManager();
		assert sanityCheck();
	}

	public  Entry<NODE, NODE> pollArrayEquality() {
		if (!hasArrayEqualities()) {
			throw new IllegalStateException("check hasArrayEqualities before calling this method");
		}
		final Entry<NODE, NODE> en = mArrayEqualities.iterator().next();
		mArrayEqualities.removePair(en.getKey(), en.getValue());
		// (this is new:, at 20.09.17)
		mWeakEquivalenceEdges.remove(new Doubleton<>(en.getKey(), en.getValue()));
		return en;
	}

	public boolean reportChangeInGroundPartialArrangement(final Predicate<CongruenceClosure<NODE>> action) {
//		assert this.sanityCheck();
//		assert mPartialArrangement.sanityCheck();
		boolean madeChanges = false;
		final Map<Doubleton<NODE>, WeakEquivalenceEdgeLabel> weqCopy = new HashMap<>(mWeakEquivalenceEdges);
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel> edge : weqCopy.entrySet())  {
			final WeakEquivalenceEdgeLabel newLabel = edge.getValue().reportChangeInGroundPartialArrangement(action);
			if (newLabel.isInconsistent()) {
				/*
				 *  edge label became inconsistent
				 *   <li> report a strong equivalence
				 *   <li> keep the edge for now, as we may still want to do propagations based on it, it will be removed
				 *     later
				 */
				mArrayEqualities.addPair(edge.getKey().getOneElement(), edge.getKey().getOtherElement());
				madeChanges = true;
			}
			mWeakEquivalenceEdges.put(edge.getKey(), newLabel);
			// TODO is the madeChanges flag worth this effort?.. should we just always say "true"?..
			madeChanges |= !newLabel.isStrongerThan(edge.getValue()) || !edge.getValue().isStrongerThan(newLabel);
//			assert mPartialArrangement.sanityCheck();
//			assert mPartialArrangement.sanityCheckOnlyCc();
		}
//		assert sanityCheck();
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
	 * @param newRep the representative of func's equivalence class after removal
	 * @param groundPartialArrangement the gpa that should be assumed for the projection (might be different from
	 * 		mPartialArrangement, or mPartialArrangement might be null..)
	 */
	public void projectFunction(final NODE func,// final NODE newRep,
			final CongruenceClosure<NODE> groundPartialArrangement,
			final Map<NODE, NODE> removedElemsToNewReps) {
//			final Set<NODE> afParents) {
		final Map<Doubleton<NODE>, WeakEquivalenceEdgeLabel> edgesCopy = new HashMap<>(mWeakEquivalenceEdges);

		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel> en : edgesCopy.entrySet()) {

			final NODE source = en.getKey().getOneElement();
			final NODE target = en.getKey().getOtherElement();

//			if (source.equals(func)) {
			if (removedElemsToNewReps.containsKey(source)) {
				final WeakEquivalenceGraph<ACTION, NODE>.WeakEquivalenceEdgeLabel label =
						mWeakEquivalenceEdges.remove(en.getKey());
				final NODE newRep = removedElemsToNewReps.get(source);
				if (newRep != null) {
//					label.projectElement(func, newRep, groundPartialArrangement);
					label.projectElement(func, groundPartialArrangement);
					mWeakEquivalenceEdges.put(new Doubleton<NODE>(newRep, target), label);
				}
			} else if (removedElemsToNewReps.containsKey(target)) {
				final WeakEquivalenceGraph<ACTION, NODE>.WeakEquivalenceEdgeLabel label =
						mWeakEquivalenceEdges.remove(en.getKey());
				final NODE newRep = removedElemsToNewReps.get(target);
				if (newRep != null) {
//					label.projectElement(func, newRep, groundPartialArrangement);
					label.projectElement(func, groundPartialArrangement);
					mWeakEquivalenceEdges.put(new Doubleton<NODE>(source, newRep), label);
				}
			} else {
//				en.getValue().projectElement(func, newRep, groundPartialArrangement);
				en.getValue().projectElement(func, groundPartialArrangement);
			}
		}
		assert projectedFunctionIsFullyGone(func);
		assert sanityCheck();
	}

	private boolean projectedFunctionIsFullyGone(final NODE func) {
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel> edge : mWeakEquivalenceEdges.entrySet()) {
			if (edge.getKey().getOneElement().equals(func) || edge.getKey().getOtherElement().equals(func)) {
				assert false;
				return false;
			}

			if (edge.getValue().getAppearingNodes().contains(func)) {
				assert false;
				return false;
			}
		}
		return true;
	}

	public void renameVariables(final Map<Term, Term> substitutionMapping) {
		final HashMap<Doubleton<NODE>, WeakEquivalenceEdgeLabel> weqEdgesCopy =
				new HashMap<>(mWeakEquivalenceEdges);
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel> en : weqEdgesCopy.entrySet()) {
			mWeakEquivalenceEdges.remove(en.getKey());

			final Doubleton<NODE> newDton = new Doubleton<>(
					en.getKey().getOneElement().renameVariables(substitutionMapping),
					en.getKey().getOtherElement().renameVariables(substitutionMapping));
			en.getValue().renameVariables(substitutionMapping);
			mWeakEquivalenceEdges.put(newDton, en.getValue());
		}
		assert sanityCheck();
	}

	/**
	 * Compute join of the weak equivalence graphs.
	 *
	 * Algorithm overview:
	 * For every two nodes a, b that appear in both graphs:
	 * <li> If none, or only one graph, has a weak equivalence between a and b, there no edge between a and b  in the
	 *   new graph.
	 * <li> If both have a weak equivalence between a and b, then the new weak equivalence between a and b is labeled
	 *   with the union of those weak equivalence's labels
	 * <li> If one graph has a strong equivalence between a and b, and the other one a weak equivalence, we take over
	 *   the weak equivalence. (This makes it necessary to take into account the ground partial arrangements of the
	 *    weq graphs!)
	 *
	 * @param other
	 * @param newPartialArrangement the joined partialArrangement, we need this because the edges of the the new
	 * 		weq graph have to be between the new equivalence representatives TODO
	 * @return
	 */
	WeakEquivalenceGraph<ACTION, NODE> join(final WeakEquivalenceGraph<ACTION, NODE> other) {
		assert mPartialArrangement != null && other.mPartialArrangement != null : "we need the partial for the join"
				+ "of the weq graphs, because strong equalities influence the weak ones..";

		final Map<Doubleton<NODE>, WeakEquivalenceEdgeLabel> newWeakEquivalenceEdges = new HashMap<>();
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel> thisWeqEdge
				: this.mWeakEquivalenceEdges.entrySet()) {
			final WeakEquivalenceEdgeLabel correspondingWeqEdgeLabelInOther =
					other.mWeakEquivalenceEdges.get(thisWeqEdge.getKey());

			final NODE source = thisWeqEdge.getKey().getOneElement();
			final NODE target = thisWeqEdge.getKey().getOtherElement();

			/*
			 * if the other weq graph's partial arrangement has a strong equivalence for the current edge, we can
			 * keep the current edge.
			 */
			if (other.mPartialArrangement.hasElements(source, target)
					&& other.mPartialArrangement.getEqualityStatus(source, target) == EqualityStatus.EQUAL) {
				// case "weak equivalence in this, strong equivalence in other"

				final WeakEquivalenceGraph<ACTION, NODE>.WeakEquivalenceEdgeLabel newEdgeLabel = thisWeqEdge.getValue()
						.meet(Collections.singletonList(this.mPartialArrangement))
						.projectToElements(mFactory.getAllWeqNodes());

				newWeakEquivalenceEdges.put(thisWeqEdge.getKey(), newEdgeLabel);
				assert correspondingWeqEdgeLabelInOther == null;
				continue;
			}

			if (correspondingWeqEdgeLabelInOther == null) {
				continue;
			}

			final WeakEquivalenceGraph<ACTION, NODE>.WeakEquivalenceEdgeLabel thisNewEdgeLabel = thisWeqEdge.getValue()
						.meet(Collections.singletonList(this.mPartialArrangement))
						.projectToElements(mFactory.getAllWeqNodes());
			final WeakEquivalenceGraph<ACTION, NODE>.WeakEquivalenceEdgeLabel otherNewEdgeLabel =
					correspondingWeqEdgeLabelInOther
						.meet(Collections.singletonList(other.mPartialArrangement))
						.projectToElements(mFactory.getAllWeqNodes());


			newWeakEquivalenceEdges.put(thisWeqEdge.getKey(),
					thisNewEdgeLabel.union(otherNewEdgeLabel));
//					thisWeqEdge.getValue().union(correspondingWeqEdgeLabelInOther));
		}

		/*
		 * for the case strong equivalence in this, weak equivalence in other, we iterate other's weak equivalence edges
		 */
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel> otherWeqEdge
				: other.mWeakEquivalenceEdges.entrySet()) {
			final NODE source = otherWeqEdge.getKey().getOneElement();
			final NODE target = otherWeqEdge.getKey().getOtherElement();

			if (this.mPartialArrangement.hasElements(source, target)
					&& this.mPartialArrangement.getEqualityStatus(source, target) == EqualityStatus.EQUAL) {
				final WeakEquivalenceGraph<ACTION, NODE>.WeakEquivalenceEdgeLabel newEdgeLabel = otherWeqEdge.getValue()
						.meet(Collections.singletonList(other.mPartialArrangement))
						.projectToElements(mFactory.getAllWeqNodes());

				newWeakEquivalenceEdges.put(otherWeqEdge.getKey(), newEdgeLabel);
				continue;
			}
		}

		final WeakEquivalenceGraph<ACTION, NODE> result = new WeakEquivalenceGraph<>(newWeakEquivalenceEdges,
				new HashRelation<>(), mFactory);
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
	Map<Doubleton<NODE>, WeakEquivalenceGraph<ACTION, NODE>.WeakEquivalenceEdgeLabel> close() {
		if (mWeakEquivalenceEdges.isEmpty()) {
			return Collections.emptyMap();
		}
		final FloydWarshall<NODE, WeakEquivalenceEdgeLabel> fw =
				new FloydWarshall<>(WeakEquivalenceEdgeLabel::isStrongerThan,
						WeakEquivalenceEdgeLabel::union,
						WeakEquivalenceEdgeLabel::meet,
						new WeakEquivalenceEdgeLabel(),
						mWeakEquivalenceEdges,
						WeakEquivalenceEdgeLabel::new);
		if (!fw.performedChanges()) {
			return Collections.emptyMap();
		}
		return fw.getResult();
	}

	/**
	 *
	 * @return true if this graph has no constraints/is tautological
	 */
	public boolean isEmpty() {
		for (final Entry<Doubleton<NODE>, WeakEquivalenceGraph<ACTION, NODE>.WeakEquivalenceEdgeLabel> edge
				: mWeakEquivalenceEdges.entrySet()) {
			if (!edge.getValue().isTautological()) {
				return false;
			}
		}
		return true;
	}

	public boolean isStrongerThan(final WeakEquivalenceGraph<ACTION, NODE> other) {
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel> otherWeqEdgeAndLabel
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
//		assert mArrayEqualities == null || mArrayEqualities.isEmpty();
		final List<Term> result = new ArrayList<>();
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel> edge : mWeakEquivalenceEdges.entrySet()) {
//			if (mArrayEqualities.containsPair(edge.getKey().getOneElement(), edge.getKey().getOtherElement())
//					&& mArrayEqualities.containsPair(edge.getKey().getOtherElement(), edge.getKey().getOneElement())) {
//				// case where the edge is inconsistent --> we could just add a ground equality instead of the whole
//  			// edge..
//				result.add(e)
//				continue;
//			}
			final List<Term> dnfAsCubeList = new ArrayList<>();
			dnfAsCubeList.addAll(edge.getValue().toDNF(script));

			final NODE source = edge.getKey().getOneElement();
			final NODE target = edge.getKey().getOtherElement();
			assert source.hasSameTypeAs(target);

			final Term arrayEquation = computeArrayEquation(script, source, target);

			dnfAsCubeList.add(arrayEquation);

			final Term edgeFormula = SmtUtils.quantifier(script, QuantifiedFormula.FORALL,
					new HashSet<TermVariable>(computeWeqIndicesForArray(edge.getKey().getOneElement())), SmtUtils.or(script, dnfAsCubeList));
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
	private Term computeArrayEquation(final Script script, final NODE array1, final NODE array2) {
		assert array1.getTerm().getSort().equals(array2.getTerm().getSort());
		final List<Term> indexEntries = computeWeqIndicesForArray(array1).stream().map(tv -> (Term) tv)
				.collect(Collectors.toList());
		final ArrayIndex index = new ArrayIndex(indexEntries);

		final Term select1 = array1.getSort().isArraySort() ?
				SmtUtils.multiDimensionalSelect(script, array1.getTerm(), index) :
					array1.getTerm();
		final Term select2 = array2.getSort().isArraySort() ?
				SmtUtils.multiDimensionalSelect(script, array2.getTerm(), index) :
					array2.getTerm();

		return SmtUtils.binaryEquality(script, select1, select2);
	}

	private List<TermVariable> computeWeqIndicesForArray(final NODE array1) {
		final MultiDimensionalSort mdSort = new MultiDimensionalSort(array1.getTerm().getSort());

		final List<TermVariable> indexEntries = new ArrayList<>();
		for (int i = 0; i < mdSort.getDimension(); i++) {
			indexEntries.add(mFactory.getWeqVariableForDimension(i, mdSort.getIndexSorts().get(i)));
		}
		return indexEntries;
	}

	public  Map<NODE, WeakEquivalenceEdgeLabel> getAdjacentWeqEdges(final NODE appliedFunction) {
		final Map<NODE, WeakEquivalenceEdgeLabel> result = new HashMap<>();
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel> en : mWeakEquivalenceEdges.entrySet()) {
			if (en.getKey().getOneElement().equals(appliedFunction)) {
				result.put(en.getKey().getOtherElement(), en.getValue());
			}
			if (en.getKey().getOtherElement().equals(appliedFunction)) {
				result.put(en.getKey().getOneElement(), en.getValue());
			}
		}
		return result;
	}

	public  Map<Doubleton<NODE>, WeakEquivalenceEdgeLabel> getEdges() {
		return Collections.unmodifiableMap(mWeakEquivalenceEdges);
	}

	/**
	 *
	 * @param sourceAndTarget
	 * @param paList
	 * @return true iff label became strictly stronger
	 */
	private boolean strengthenEdgeLabel(final Doubleton<NODE> sourceAndTarget,
			final List<CongruenceClosure<NODE>> paList) {
		assert mPartialArrangement.isRepresentative(sourceAndTarget.getOneElement())
			&& mPartialArrangement.isRepresentative(sourceAndTarget.getOtherElement());
		assert !sourceAndTarget.getOneElement().equals(sourceAndTarget.getOtherElement());

		WeakEquivalenceEdgeLabel oldLabel = mWeakEquivalenceEdges.get(sourceAndTarget);
		if (oldLabel == null) {
			oldLabel = new WeakEquivalenceEdgeLabel();
		}

		final WeakEquivalenceEdgeLabel labelToStrengthenWith = new WeakEquivalenceEdgeLabel(paList);
		if (oldLabel.isStrongerThan(labelToStrengthenWith)) {
			// nothing to do
			return false;
		}

		WeakEquivalenceEdgeLabel strengthenedEdgeLabel = oldLabel.meet(labelToStrengthenWith);

		// meet with gpa and project afterwards
		strengthenedEdgeLabel = strengthenedEdgeLabel.meet(Collections.singletonList(mPartialArrangement));
		strengthenedEdgeLabel = strengthenedEdgeLabel.projectToElements(mFactory.getAllWeqNodes());

		// inconsistency check
		if (strengthenedEdgeLabel.isInconsistent()) {
			mArrayEqualities.addPair(sourceAndTarget.getOneElement(), sourceAndTarget.getOtherElement());
		}

		// replace the edge label by the strengthened version
		mWeakEquivalenceEdges.put(sourceAndTarget, strengthenedEdgeLabel);
//		assert sanityCheck();
		return true;
	}

	/**
	 *
	 * <li> add constraint to the edge (make one if none exists)
	 * <li> check for congruence-like propagations
	 * <li> check if edge became inconsistent
	 * (the third type, extensionality-like propagations are done at reportEqualityRec/
	 * strengthenEdgeWithExceptedPoint..)
	 *
	 * @param sourceAndTarget
	 * @param value
	 */
	private boolean reportWeakEquivalence(final Doubleton<NODE> sourceAndTarget,
			final WeakEquivalenceGraph<ACTION, NODE>.WeakEquivalenceEdgeLabel value) {
		assert mPartialArrangement.isRepresentative(sourceAndTarget.getOneElement())
			&& mPartialArrangement.isRepresentative(sourceAndTarget.getOtherElement());
		assert sourceAndTarget.getOneElement().getTerm().getSort().equals(sourceAndTarget.getOtherElement().getTerm().getSort());

		return strengthenEdgeLabel(sourceAndTarget, value.getLabelContents());
	}

	public boolean reportWeakEquivalence(final NODE array1, final NODE array2,
			final List<CongruenceClosure<NODE>> edgeLabelContents) {
		assert mPartialArrangement.isRepresentative(array1) && mPartialArrangement.isRepresentative(array2);

		return reportWeakEquivalence(new Doubleton<NODE>(array1, array2),
				new WeakEquivalenceEdgeLabel(edgeLabelContents));
	}

	public boolean isConstrained(final NODE elem) {
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel> edge : mWeakEquivalenceEdges.entrySet()) {
			if (edge.getValue().isConstrained(elem)) {
				return true;
			}
		}
		return false;
	}

	public List<CongruenceClosure<NODE>> getEdgeLabelContents(final NODE array1, final NODE array2) {
		final WeakEquivalenceGraph<ACTION, NODE>.WeakEquivalenceEdgeLabel edge =
				mWeakEquivalenceEdges.get(new Doubleton<>(array1, array2));
		if (edge != null) {
			return edge.getLabelContents();
		}
		return Collections.singletonList(new CongruenceClosure<>());
	}

	/**
	 * used for roweq rule
	 *
	 *   project_q(Phi /\ q = i), then decrease the weqvar indices in the resulting formula by dim
	 *
	 * @param originalEdgeLabel
	 * @param prefix1
	 * @param weqVarsForThisEdge list of weqVarNodes that may appear in the given label contents (not all must appear),
	 *     is computed from the source or target of the edge the label contents belong to
	 * @return
	 */
	public List<CongruenceClosure<NODE>> projectEdgeLabelToPoint(
			final List<CongruenceClosure<NODE>> labelContents, final NODE value,
			final List<NODE> weqVarsForThisEdge) {

		final WeakEquivalenceGraph<ACTION, NODE>.WeakEquivalenceEdgeLabel originalEdgeLabel =
				new WeakEquivalenceEdgeLabel(labelContents);
//		final List<NODE> prefix1 = Collections.singletonList(value);

		// TODO: this dimension stuff is a relic (dimension is always 1) --> get rid of it some time..
//		final int dim = prefix1.size();

//		final List<NODE> firstDimWeqVarNodes = new ArrayList<>(dim);
//		for (int i = 0; i < dim; i++) {
//			firstDimWeqVarNodes.add(mFactory.getWeqVariableNodeForDimension(i, prefix1.get(i).getSort()));
//		}
		final NODE firstDimWeqVarNode = weqVarsForThisEdge.get(0);

		final CongruenceClosure<NODE> qEqualsI = new CongruenceClosure<>();
//		for (int i = 0; i < dim; i++) {
			qEqualsI.reportEquality(firstDimWeqVarNode, value);
//			qEqualsI.reportEquality(firstDimWeqVarNodes.get(i), prefix1.get(i));
//		}

		final WeakEquivalenceGraph<ACTION, NODE>.WeakEquivalenceEdgeLabel copy =
				new WeakEquivalenceEdgeLabel(originalEdgeLabel);
		final WeakEquivalenceGraph<ACTION, NODE>.WeakEquivalenceEdgeLabel meet =
				copy.meetRec(Collections.singletonList(qEqualsI));

//		for (int i = 0; i < dim; i++) {
//			meet.projectElement(firstDimWeqVarNodes.get(i), null, mPartialArrangement);
//			meet.projectElement(firstDimWeqVarNodes.get(i), mPartialArrangement);
//		}
		meet.projectElement(firstDimWeqVarNode, mPartialArrangement);

//		meet.inOrDecreaseWeqVarIndices(-dim, weqVarsForThisEdge);
		meet.inOrDecreaseWeqVarIndices(-1, weqVarsForThisEdge);
		assert !meet.getAppearingNodes().contains(weqVarsForThisEdge.get(weqVarsForThisEdge.size() - 1)) : "double "
				+ "check the condition if this assertion fails, but as we decreased all weq vars, the last one should "
				+ "not be present in the result, right?..";

		return meet.getLabelContents();
	}

	/**
	 * used for roweq-1 rule
	 *
	 * @param labelContents
	 * @param argument
	 * @param weqVarsForResolventEdge
	 * @return
	 */
	public List<CongruenceClosure<NODE>> shiftLabelAndAddException(
			final List<CongruenceClosure<NODE>> labelContents, final NODE argument,
			final List<NODE> weqVarsForResolventEdge) {
		assert !weqVarsForResolventEdge.isEmpty() : "because the array in the resolvent must have a dimension >= 1";

		final WeakEquivalenceGraph<ACTION, NODE>.WeakEquivalenceEdgeLabel labelToShiftAndAdd =
				new WeakEquivalenceEdgeLabel(labelContents);

		// project away the highest weq var before shifting
		labelToShiftAndAdd.projectElement(weqVarsForResolventEdge.get(weqVarsForResolventEdge.size() -1),
				mPartialArrangement);

		labelToShiftAndAdd.inOrDecreaseWeqVarIndices(1, weqVarsForResolventEdge);

		final NODE firstWeqVar = weqVarsForResolventEdge.get(0);
		assert !labelToShiftAndAdd.getAppearingNodes().contains(firstWeqVar);

		final CongruenceClosure<NODE> firstWeqVarUnequalArgument = new CongruenceClosure<>();
		firstWeqVarUnequalArgument.reportDisequality(firstWeqVar, argument);

		final List<CongruenceClosure<NODE>> shiftedLabelContents =
				new ArrayList<>(labelToShiftAndAdd.getLabelContents());

		shiftedLabelContents.add(firstWeqVarUnequalArgument);

		return shiftedLabelContents;
	}

	boolean sanityCheck() {
			assert mFactory != null : "factory is needed for the sanity check..";

			/*
			 * check that no weak equivalence edge contains a NODE that is not known to mPartialArrangement
			 * or is one of the special quantified variables from getVariableForDimension(..).
			 */
			if (mPartialArrangement != null) {
				for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel> edge : mWeakEquivalenceEdges.entrySet()) {
					final Set<NODE> nodesOnEdgeLabelWithoutWeqNodes = edge.getValue().getAppearingNodes().stream()
							.filter(node -> !CongruenceClosure.hasSubElement(node, mFactory.getAllWeqNodes()))
							.collect(Collectors.toSet());
					if (!mPartialArrangement.getAllElements().containsAll(nodesOnEdgeLabelWithoutWeqNodes)) {
						final Set<NODE> difference = DataStructureUtils.difference(nodesOnEdgeLabelWithoutWeqNodes,
								mPartialArrangement.getAllElements());
						assert false : "weq edge contains node(s) that has been removed: " + difference;
						return false;
					}
				}
			}

			/*
			 * check that the edges only connect compatible arrays
			 *  compatible means having the same Sort, in particular: dimensionality
			 */
			for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel> edge : mWeakEquivalenceEdges.entrySet()) {
				final NODE source = edge.getKey().getOneElement();
				final NODE target = edge.getKey().getOtherElement();
				if (!source.hasSameTypeAs(target)) {
						assert false;
						return false;
				}
			}

			/*
			 * Check that all the edges are between equivalence representatives of mPartialArrangement
			 */
			if (mPartialArrangement != null) {
				for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel> edge : mWeakEquivalenceEdges.entrySet()) {
					final NODE source = edge.getKey().getOneElement();
					final NODE target = edge.getKey().getOtherElement();
					if (!mPartialArrangement.hasElement(source)) {
						assert false : "weq edge source is not known to partial arrangement";
						return false;
					}
					if (!mPartialArrangement.hasElement(target)) {
						assert false : "weq edge target is not known to partial arrangement";
						return false;
					}
					if (!mPartialArrangement.isRepresentative(source)) {
						assert false : "weq edge source is not a representative";
						return false;
					}
					if (!mPartialArrangement.isRepresentative(target)) {
						assert false : "weq edge target is not a representative";
						return false;
					}
				}
			}

			/*
			 * Check that none of the edges has the same source and target (is a self-loop).
			 */
			for (final Doubleton<NODE> dton : mWeakEquivalenceEdges.keySet()) {
				if (dton.getOneElement().equals(dton.getOtherElement())) {
					assert false : "self loop in weq graph";
					return false;
				}
			}

			/*
			 * check completeness of the graph ("triangle inequality")
			 */


			/*
			 * check that we have remembered every inconsistent edge label in mArrayEqualities (for later cleanup)
			 */
			for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel> edge : mWeakEquivalenceEdges.entrySet()) {
				final NODE source = edge.getKey().getOneElement();
				final NODE target = edge.getKey().getOtherElement();
				if (edge.getValue().isInconsistent()
						&& !mArrayEqualities.containsPair(source, target)
						&& !mArrayEqualities.containsPair(target, source)) {
					assert false : "lost track of an inconsistent weq edge";
					return false;
				}
			}
			return true;
		}

	private static <NODE extends ICongruenceClosureElement<NODE>> List<CongruenceClosure<NODE>> simplifyPaDisjunction(
			final List<CongruenceClosure<NODE>> newLabelContents) {
		// make a copy of the list, filter out false disjuncts
		List<CongruenceClosure<NODE>> newLabel = new ArrayList<>(newLabelContents).stream()
				.filter(pa -> !pa.isInconsistent()).collect(Collectors.toList());

		// if there is any true disjunct, it will annihilate all the others
		if (newLabel.stream().anyMatch(pa -> pa.isTautological())) {
			newLabel = Collections.singletonList(new CongruenceClosure<>());
		}

		return newLabel;
	}

	/**
	 * when we merge two equivalence classes that had a weak equivalence edge, these nodes must be collapsed into one
	 * in the weq graph (the edge removed)
	 *
	 * (could also be called "removeEdge"..)
	 *
	 * @param node1OldRep
	 * @param node2OldRep
	 * @param newRep
	 */
	public void collapseEdgeAtMerge(final NODE node1OldRep, final NODE node2OldRep) {
		mWeakEquivalenceEdges.remove(new Doubleton<>(node1OldRep, node2OldRep));
	}

	/**
	 * Called after a merge
	 *  <li> some element is no representative anymore
	 *  <li> an eventual edge between the merged nodes representative has already been removed
	 *  <li> but there may be edges where source or target is not a representative anymore..
	 *  replace the edge source/target with the new representative
	 */
	public void updateForNewRep(final NODE node1OldRep, final NODE node2OldRep, final NODE newRep) {
		assert mPartialArrangement.getRepresentativeElement(node1OldRep) == newRep;
		assert mPartialArrangement.getRepresentativeElement(node2OldRep) == newRep;

		if (node1OldRep == newRep) {
			// node2OldRep is not representative anymore
			for (final Entry<NODE, WeakEquivalenceGraph<ACTION, NODE>.WeakEquivalenceEdgeLabel> edge
					: getAdjacentWeqEdges(node2OldRep).entrySet()) {
				mWeakEquivalenceEdges.remove(new Doubleton<>(node2OldRep, edge.getKey()));
				mWeakEquivalenceEdges.put(new Doubleton<>(newRep, edge.getKey()), edge.getValue());
			}
		} else {
			// node1OldRep is not representative anymore
			for (final Entry<NODE, WeakEquivalenceGraph<ACTION, NODE>.WeakEquivalenceEdgeLabel> edge
					: getAdjacentWeqEdges(node1OldRep).entrySet()) {
				mWeakEquivalenceEdges.remove(new Doubleton<>(node1OldRep, edge.getKey()));
				mWeakEquivalenceEdges.put(new Doubleton<>(newRep, edge.getKey()), edge.getValue());
			}
		}
	}

	public Integer getNumberOfEdgesStatistic() {
		return mWeakEquivalenceEdges.size();
	}

	public Integer getMaxSizeOfEdgeLabelStatistic() {
		final Optional<Integer> opt = mWeakEquivalenceEdges.values().stream()
				.map(weqlabel -> weqlabel.mLabel.size()).reduce(Math::max);
		if (opt.isPresent()) {
			return opt.get();
		}
		return 0;
	}

	Map<String, Integer> summarize() {
		final Map<String, Integer> result = new HashMap<>();

		result.put("#Edges", mWeakEquivalenceEdges.size());

		final int noEdgeLabelDisjuncts = mWeakEquivalenceEdges.values().stream()
				.map(weqEdge -> weqEdge.getLabelContents().size())
				.reduce((i1, i2) -> i1 + i2)
				.get();
		result.put("#EdgeLabelDisjuncts", noEdgeLabelDisjuncts);

		result.put("Average#EdgeLabelDisjuncts", mWeakEquivalenceEdges.size()/noEdgeLabelDisjuncts);

		return result;
	}

	@Override
	public String toString() {
		if (isEmpty()) {
			return "Empty";
		}
		if (mWeakEquivalenceEdges.size() < 4) {
			return toLogString();
		}

		final StringBuilder sb = new StringBuilder();
		sb.append("summary:\n");
		for (final Entry<String, Integer> en : summarize().entrySet()) {
			sb.append(String.format("%s : %d\n", en.getKey(), en.getValue()));
		}
		sb.append("graph shape:\n");
		for (final Entry<Doubleton<NODE>, WeakEquivalenceGraph<ACTION, NODE>.WeakEquivalenceEdgeLabel> weq :
			mWeakEquivalenceEdges.entrySet()) {
			sb.append(weq.getKey());
			sb.append("\n");
		}
		return sb.toString();
	}

	public String toLogString() {
		final StringBuilder sb = new StringBuilder();

		for (final Entry<Doubleton<NODE>, WeakEquivalenceGraph<ACTION, NODE>.WeakEquivalenceEdgeLabel> weq :
			mWeakEquivalenceEdges.entrySet()) {
			sb.append(weq.getKey());
			sb.append("\n");
			sb.append(weq.getValue().toLogString());
			sb.append("\n");
		}

		return sb.toString();
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

			private final List<CongruenceClosure<NODE>> mLabel;

			/**
			 * Constructs an empty edge. (labeled "true")
			 */
			public WeakEquivalenceEdgeLabel() {
				mLabel = new ArrayList<>();
				mLabel.add(new CongruenceClosure<>());
				assert sanityCheck();
			}

			public WeakEquivalenceEdgeLabel projectToElements(final Set<NODE> allWeqNodes) {
				if (isInconsistent()) {
					return this;
				}
				final List<CongruenceClosure<NODE>> newLabelContents = new ArrayList<>();
				for (final CongruenceClosure<NODE> item : mLabel) {
					newLabelContents.add(item.projectToElements(allWeqNodes));
				}
				return new WeakEquivalenceEdgeLabel(newLabelContents);
			}

			/**
			 *
			 *
			 * @param inOrDecrease how much to shift (negative value for decrease)
			 * @param weqVarsForThisEdge this edgeLabel does not know the function signature of its source and target;
			 *     thus we pass a list of weqVars that belongs to that signature (those are the ones to be shifted..)
			 *     they must be in correct order of dimensions according to source/target
			 */
			public void inOrDecreaseWeqVarIndices(final int inOrDecrease, final List<NODE> weqVarsForThisEdge) {
				assert inOrDecrease == 1 || inOrDecrease == -1 : "we don't expect any other cases";
				assert inOrDecrease != 1 || !this.getAppearingNodes()
						.contains(weqVarsForThisEdge.get(weqVarsForThisEdge.size() - 1)) : "project the highest weqvar "
								+ "before increasing!";
				assert inOrDecrease != -1 || !this.getAppearingNodes()
						.contains(weqVarsForThisEdge.get(0)) : "project the lowest weqvar before decreasing!";

				final Map<Term, Term> substitutionMapping = new HashMap<>();
				for (int i = 0; i < weqVarsForThisEdge.size(); i++) {
					final NODE nodeI = weqVarsForThisEdge.get(i);
					final int newDim = i + inOrDecrease;
					// the others (newDim <0) should have been projected out of the formula before.. (in the calling method)
					if (newDim >= 0 && newDim < weqVarsForThisEdge.size()) {
						substitutionMapping.put(nodeI.getTerm(),
								mFactory.getWeqVariableForDimension(newDim, nodeI.getSort()));
					}
				}
				this.renameVariables(substitutionMapping);
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
				mLabel = new ArrayList<>(original.getLabelContents().size());
				for (int i = 0; i < original.getLabelContents().size(); i++) {
					assert !original.getLabelContents().get(i).isInconsistent();
					assert !original.getLabelContents().get(i).isTautological() || original.getLabelContents().size() == 1;
					mLabel.add(new CongruenceClosure<>(original.getLabelContents().get(i)));
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
			public WeakEquivalenceEdgeLabel(final List<CongruenceClosure<NODE>> newLabelContents) {
				mLabel = simplifyPaDisjunction(newLabelContents);
				assert sanityCheck();
			}

			public List<CongruenceClosure<NODE>> getLabelContents() {
				return Collections.unmodifiableList(mLabel);
			}

			public boolean isInconsistent() {
				for (final CongruenceClosure<NODE> pa : getLabelContents()) {
					if (!pa.isInconsistent()) {
						// we found one consistent disjunct --> this label is consistent
						return false;
					} else {
						// current cc is inconsistent
						assert getLabelContents().size() == 1 : "we are filtering out all but one 'bottoms', right?";
					}
				}
				return true;
			}

			public boolean impliesEqualityOnThatPosition(final List<NODE> arguments) {
				for (int i = 0; i < getLabelContents().size(); i++) {
					final CongruenceClosure<NODE> copy = mCcManager.makeCopy(
							// making a copy of mPartialArrangement's congruence closure here to avoid some sanity checks..
							mCcManager.getMeet(getLabelContents().get(i), new CongruenceClosure<>(mPartialArrangement)));
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
					final Predicate<CongruenceClosure<NODE>> reportX) {
	//			assert WeakEquivalenceGraph.this.sanityCheck();
	//			assert mPartialArrangement.sanityCheck();


				final List<CongruenceClosure<NODE>> newLabel = new ArrayList<>();

				for (int i = 0; i < getLabelContents().size(); i++) {
	//				assert mPartialArrangement.sanityCheck();
					final CongruenceClosure<NODE> currentPaWgpa = mCcManager.getMeet(getLabelContents().get(i),
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
						newLabel.add(getLabelContents().get(i));
						assert !currentPaWgpa.isInconsistent();
						continue;
					}

					// add the strengthened version as the new label element
					newLabel.add(currentPaWgpa.projectToElements(mFactory.getAllWeqNodes()));

	//				assert mPartialArrangement.sanityCheck();
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
				for (final CongruenceClosure<NODE> cc : mLabel) {
					final List<Term> cube = EqConstraint.partialArrangementToCube(script, cc);
					final Term cubeTerm = SmtUtils.and(script, cube);
					result.add(cubeTerm);
				}
				return result;
			}

			public void renameVariables(final Map<Term, Term> substitutionMapping) {
				for (int i = 0; i < getLabelContents().size(); i++) {
					getLabelContents().get(i).transformElementsAndFunctions(node -> node.renameVariables(substitutionMapping));
	//						func -> func.renameVariables(substitutionMapping));
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
				getLabelContents().forEach(pa -> res.addAll(pa.getAllElements()));
				return res;
			}

			public WeakEquivalenceEdgeLabel meet(final WeakEquivalenceEdgeLabel otherLabel) {
				return meet(otherLabel.getLabelContents());
			}

			private WeakEquivalenceEdgeLabel meet(final List<CongruenceClosure<NODE>> paList) {
				assert sanityCheck();
				return meetRec(paList);
			}

			private WeakEquivalenceEdgeLabel meetRec(final List<CongruenceClosure<NODE>> paList) {

				final List<List<CongruenceClosure<NODE>>> li = new ArrayList<>(2);
				li.add(getLabelContents());
				li.add(paList);
				final List<List<CongruenceClosure<NODE>>> cp = CrossProducts.crossProduct(li);

				final List<CongruenceClosure<NODE>> newLabelContent = new ArrayList<>();
				for (final List<CongruenceClosure<NODE>> pair : cp) {
					assert pair.size() == 2;
					newLabelContent.add(pair.get(0).meetRec(pair.get(1)));
				}
	//			newLabelContent = mCcManager.filterRedundantCcs(newLabelContent);

	//			final List<CongruenceClosure<NODE>> newLabel = simplifyPaDisjunction(newLabelContent);
				final List<CongruenceClosure<NODE>> newLabel = mCcManager.filterRedundantCcs(newLabelContent);

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
				for (final CongruenceClosure<NODE> paThis : getLabelContents()) {
					boolean existsWeaker = false;
					for (final CongruenceClosure<NODE> paOther : other.getLabelContents()) {
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
	//			assert this.mLabel.size() < 10 && other.mLabel.size() < 10;
				final List<CongruenceClosure<NODE>> unionList = new ArrayList<>(
						mLabel.size() + other.getLabelContents().size());
				unionList.addAll(mLabel);
				unionList.addAll(other.getLabelContents());

				final List<CongruenceClosure<NODE>> filtered = mCcManager.filterRedundantCcs(unionList);

				return new WeakEquivalenceEdgeLabel(filtered);
			}


			/**
			 *  <li> compute the meet with the ground partial arrangement
			 *  <li> project out the variable to be projected elem
			 *  <li> project out all constraints that do not contain a weq-variable
			 *
			 *  (formerly projecthelper:)
			 * proceeds in three steps for each label element of this weq label :
			 *  <li> constructs the meet of the element with the ground partial arrangement (gpa)
			 *  <li> applies the given removal method on that meet
			 *  <li> projects away the constraints in the resulting element that do not contain one of the weq-variables
			 *
			 * @param elem
			 * @param groundPartialArrangement the gpa that is like mPartialArrangement but elem has been removed already
			 *    (if we used mPartialArrangement, we would put elem back in via the meet..)
			 */
			public void projectElement(final NODE elem,// final NODE newRep,
					final CongruenceClosure<NODE> groundPartialArrangement) {

				final List<CongruenceClosure<NODE>> newLabelContents = new ArrayList<>();
				for (int i = 0; i < getLabelContents().size(); i++) {
					if (mLabel.get(i).isTautological()) {
						// we have one "true" disjunct --> the whole disjunction is tautological
						if (mLabel.size() == 1) {
							return;
						}
						mLabel.clear();
						mLabel.add(new CongruenceClosure<>());
						return;
					}
					final CongruenceClosure<NODE>	meet = mCcManager.getMeet(mLabel.get(i), groundPartialArrangement);
	//				final CongruenceClosure<NODE>	meet = mCcManager.getMeet(mLabel.get(i), mPartialArrangement);
					if (meet.isInconsistent()) {
						/* label element is inconsistent with the current gpa
						 * --> omit it from the new label
						 */
						continue;
					}
					if (meet.isTautological()) {
						assert false : "this should never happen because if the meet is tautological then mLabel.get(i)"
								+ "is, too, right?";
						// we have one "true" disjunct --> the whole disjunction is tautological
						mLabel.clear();
						mLabel.add(new CongruenceClosure<>());
						return;
					}

					/*
					 * At this point (in removeSimpleElement) we need to control what
					 *   CongruenceClosure.getOtherEquivalenceClassMember
					 *  returns -- in particular if there is a weqVar in the equivalence class, it must choose it
					 *   otherwise we may loos precision as in the following example:
					 *  <p>
					 * <li>  elem = i
					 *  meet = {q, i, j} -- rep: j,  {a[i] = i}
					 * <li>  then meet.remove(i) will give us
					 *  meet = {q, j} -- rep: j,  {a[j] = i}
					 * <li>  and the second partition block will be removed by meet.projectToElements
					 *  meet = {q, j} -- rep: j
					 * <li>  However, if q was the representative and not j, we would get
					 *  meet = {q, j} -- rep: q,  {a[q] = i}
					 * <li>  and projectToElements would keep both blocks
					 *
					 * EDIT: actually, a fix to projectToElements, removes the necessity for
					 *   removeSimpleElementWithReplacementPreference at this place (--> we keep the constraint
					 *     {a[j] = i} by detecting that j = q)
					 */
//					meet.removeSimpleElementWithReplacementPreference(elem, mFactory.getAllWeqNodes());
					meet.removeSimpleElement(elem);
//					meet.transformElementsAndFunctions(node -> node.replaceSubNode(replacer, replacee));

					final CongruenceClosure<NODE> newPa = meet.projectToElements(mFactory.getAllWeqNodes());
					if (newPa.isTautological()) {
						// we have one "true" disjunct --> the whole disjunction is tautological
						mLabel.clear();
						mLabel.add(new CongruenceClosure<>());
						return;
					}
					newLabelContents.add(newPa);
				}
				assert newLabelContents.size() <= 1 || !newLabelContents.stream().anyMatch(c -> c.isTautological());
				mLabel.clear();
				mLabel.addAll(newLabelContents);

				assert sanityCheckAfterProject(elem, groundPartialArrangement);
			}

			private boolean isTautological() {
				for (final CongruenceClosure<NODE> l : getLabelContents()) {
					if (l.isTautological()) {
						assert getLabelContents().size() == 1;
						return true;
					}
				}
				return false;
			}


			@Override
			public String toString() {
				return "weq edge label, size: " + mLabel.size();
			}

			public String toLogString() {
				final StringBuilder sb = new StringBuilder();

				 mLabel.forEach(l -> sb.append(l.toLogString() + "\n"));
				 return sb.toString();
			}

			private boolean sanityCheck() {
	//			assert mLabel.size() < 10;
				return sanityCheck(mPartialArrangement);
			}

			private boolean sanityCheck(final CongruenceClosure<NODE> groundPartialArrangement) {

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
					final CongruenceClosure<NODE> groundPartialArrangement) {
				final CongruenceClosure<NODE> copy = new CongruenceClosure<>(groundPartialArrangement);
				copy.removeSimpleElement(elem);
				return sanityCheck(copy);
			}

		}
}

