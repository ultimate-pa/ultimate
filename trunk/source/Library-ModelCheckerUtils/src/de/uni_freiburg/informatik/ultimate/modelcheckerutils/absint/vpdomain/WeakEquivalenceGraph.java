/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.vpdomain;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.BiPredicate;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSort;
import de.uni_freiburg.informatik.ultimate.util.datastructures.CongruenceClosure;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.EqualityStatus;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.PartialOrderCache;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * (short: weq graph)
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class WeakEquivalenceGraph<NODE extends IEqNodeIdentifier<NODE>> {

	private final WeqCcManager<NODE> mWeqCcManager;

	private final EqConstraintFactory<NODE> mFactory;

	private final Map<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE>> mWeakEquivalenceEdges;

	private final HashRelation<NODE, NODE> mArrayEqualities;

	/**
	 * The WeqCongruenceClosure that this weq graph is part of. This may be null, if we use this weq graph as an
	 * intermediate, for example during a join or meet operation.
	 */
	final WeqCongruenceClosure<NODE> mPartialArrangement;

//	private boolean mWeqMeetMode;

	/**
	 * Constructs an empty WeakEquivalenceGraph
	 * @param factory
	 */
	public WeakEquivalenceGraph(final WeqCongruenceClosure<NODE> pArr,
			final EqConstraintFactory<NODE> factory) {
		mPartialArrangement = pArr;
		mWeakEquivalenceEdges = new HashMap<>();
		mArrayEqualities = new HashRelation<>();
		assert factory != null;
		mFactory = factory;
		mWeqCcManager = factory.getWeqCcManager();
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
			final Map<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE>> weakEquivalenceEdges,
			final HashRelation<NODE, NODE> arrayEqualities,
			final EqConstraintFactory<NODE> factory) {
		mPartialArrangement = null;
		mWeakEquivalenceEdges = weakEquivalenceEdges;
		mArrayEqualities = arrayEqualities;
		assert factory != null;
		mFactory = factory;
		mWeqCcManager = factory.getWeqCcManager();
		assert sanityCheck();
	}

	/**
	 * Copy constructor
	 *
	 * @param weakEquivalenceGraph
	 * @param factory
	 */
	public WeakEquivalenceGraph(final WeqCongruenceClosure<NODE> pArr,
			final WeakEquivalenceGraph<NODE> weakEquivalenceGraph, final boolean flattenEdges) {

		mPartialArrangement = pArr;

		mArrayEqualities = new HashRelation<>(weakEquivalenceGraph.mArrayEqualities);
		mWeakEquivalenceEdges = new HashMap<>();
		mFactory = weakEquivalenceGraph.mFactory;
		mWeqCcManager = mFactory.getWeqCcManager();

		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE>> weqEdge
				: weakEquivalenceGraph.mWeakEquivalenceEdges.entrySet()) {

			// make sure that the representatives in pArr and in our new weq edges are compatible
			final Doubleton<NODE> newSoureceAndTarget = new Doubleton<>(
					pArr.getRepresentativeElement(weqEdge.getKey().getOneElement()),
					pArr.getRepresentativeElement(weqEdge.getKey().getOtherElement()));

			if (flattenEdges) {
				final WeakEquivalenceEdgeLabel<NODE> flattenedEdgeLabel =
						weqEdge.getValue().flatten(this);
				mWeakEquivalenceEdges.put(newSoureceAndTarget, flattenedEdgeLabel);
			} else {
				mWeakEquivalenceEdges.put(newSoureceAndTarget, new WeakEquivalenceEdgeLabel<NODE>(this,
						weqEdge.getValue()));
			}
		}
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
		final Map<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE>> weqCopy = new HashMap<>(mWeakEquivalenceEdges);
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE>> edge : weqCopy.entrySet())  {
			final WeakEquivalenceEdgeLabel<NODE> newLabel = edge.getValue().reportChangeInGroundPartialArrangement(action);
			if (newLabel.isInconsistent()) {
				/*
				 *  edge label became inconsistent
				 *   <li> report a strong equivalence
				 *   <li> keep the edge for now, as we may still want to do propagations based on it, it will be removed
				 *     later
				 */
//				mArrayEqualities.addPair(edge.getKey().getOneElement(), edge.getKey().getOtherElement());
				addArrayEquality(edge.getKey().getOneElement(), edge.getKey().getOtherElement());
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

	public void updateVerticesOnRemoveElement(final NODE elem, final NODE replacement) {

		final Map<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE>> edgesCopy = new HashMap<>(mWeakEquivalenceEdges);

		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE>> en : edgesCopy.entrySet()) {

			final NODE source = en.getKey().getOneElement();
			final NODE target = en.getKey().getOtherElement();

			if (source.equals(elem)) {
				final WeakEquivalenceEdgeLabel<NODE> label =
						mWeakEquivalenceEdges.remove(en.getKey());
				if (replacement != null) {
					mWeakEquivalenceEdges.put(new Doubleton<NODE>(replacement, target), label);
				}
			} else if (target.equals(elem)) {
				final WeakEquivalenceEdgeLabel<NODE> label =
						mWeakEquivalenceEdges.remove(en.getKey());
				if (replacement != null) {
					mWeakEquivalenceEdges.put(new Doubleton<NODE>(source, replacement), label);
				}
			}
		}
	}

	public Set<NODE> projectSimpleElementInEdgeLabels(final NODE elem, final boolean useWeqGpa) {
		final Set<NODE> nodesToAdd = new HashSet<>();
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE>> en : mWeakEquivalenceEdges.entrySet()) {
			assert !elem.equals(en.getKey().getOneElement());
			assert !elem.equals(en.getKey().getOtherElement());

			nodesToAdd.addAll(en.getValue().projectSimpleElement(elem, useWeqGpa));
		}
		assert elementIsFullyRemoved(elem);
		return nodesToAdd;
	}

	public void transformElementsAndFunctions(final Function<NODE, NODE> transformer) {
		final HashMap<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE>> weqEdgesCopy =
				new HashMap<>(mWeakEquivalenceEdges);
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE>> en : weqEdgesCopy.entrySet()) {
			mWeakEquivalenceEdges.remove(en.getKey());

			final Doubleton<NODE> newDton = new Doubleton<>(
					transformer.apply(en.getKey().getOneElement()),
					transformer.apply(en.getKey().getOtherElement()));
			en.getValue().transformElements(transformer);
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
	WeakEquivalenceGraph<NODE> join(final WeakEquivalenceGraph<NODE> other) {
		assert mPartialArrangement != null && other.mPartialArrangement != null : "we need the partial for the join"
				+ "of the weq graphs, because strong equalities influence the weak ones..";

		final Map<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE>> newWeakEquivalenceEdges = new HashMap<>();
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE>> thisWeqEdge
				: this.mWeakEquivalenceEdges.entrySet()) {
			final WeakEquivalenceEdgeLabel<NODE> correspondingWeqEdgeLabelInOther =
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

				final WeakEquivalenceEdgeLabel<NODE> newEdgeLabel = thisWeqEdge.getValue()
						.meet(Collections.singleton(this.mPartialArrangement.getCongruenceClosure()))
						.projectToElements(mFactory.getAllWeqNodes());

				newWeakEquivalenceEdges.put(thisWeqEdge.getKey(), newEdgeLabel);
				assert correspondingWeqEdgeLabelInOther == null;
				continue;
			}

			if (correspondingWeqEdgeLabelInOther == null) {
				continue;
			}

			final WeakEquivalenceEdgeLabel<NODE> thisNewEdgeLabel = thisWeqEdge.getValue()
						.meet(Collections.singleton(this.mPartialArrangement.getCongruenceClosure()))
						.projectToElements(mFactory.getAllWeqNodes());
			final WeakEquivalenceEdgeLabel<NODE> otherNewEdgeLabel =
					correspondingWeqEdgeLabelInOther
						.meet(Collections.singleton(other.mPartialArrangement.getCongruenceClosure()))
						.projectToElements(mFactory.getAllWeqNodes());

			newWeakEquivalenceEdges.put(thisWeqEdge.getKey(), thisNewEdgeLabel.union(otherNewEdgeLabel));
		}

		/*
		 * for the case strong equivalence in this, weak equivalence in other, we iterate other's weak equivalence edges
		 */
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE>> otherWeqEdge
				: other.mWeakEquivalenceEdges.entrySet()) {
			final NODE source = otherWeqEdge.getKey().getOneElement();
			final NODE target = otherWeqEdge.getKey().getOtherElement();

			if (this.mPartialArrangement.hasElements(source, target)
					&& this.mPartialArrangement.getEqualityStatus(source, target) == EqualityStatus.EQUAL) {
				final WeakEquivalenceEdgeLabel<NODE> newEdgeLabel = otherWeqEdge.getValue()
						.meet(Collections.singleton(other.mPartialArrangement.getCongruenceClosure()))
						.projectToElements(mFactory.getAllWeqNodes());

				newWeakEquivalenceEdges.put(otherWeqEdge.getKey(), newEdgeLabel);
				continue;
			}
		}

		final WeakEquivalenceGraph<NODE> result = new WeakEquivalenceGraph<>(newWeakEquivalenceEdges,
				new HashRelation<>(), mFactory);
		assert result.sanityCheck();
		return result;
	}

	boolean hasArrayEqualities() {
		return !mArrayEqualities.isEmpty();
	}

	Map<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE>> close() {
		if (mWeakEquivalenceEdges.isEmpty()) {
			return Collections.emptyMap();
		}

		final CachingWeqEdgeLabelPoComparator cwelpc = new CachingWeqEdgeLabelPoComparator();

		final BiPredicate<WeakEquivalenceEdgeLabel<NODE>, WeakEquivalenceEdgeLabel<NODE>> smallerThan =
				cwelpc::isStrongerOrEqual;
		final BiFunction<WeakEquivalenceEdgeLabel<NODE>, WeakEquivalenceEdgeLabel<NODE>, WeakEquivalenceEdgeLabel<NODE>> plus
			= cwelpc::union;
		final BiFunction<WeakEquivalenceEdgeLabel<NODE>, WeakEquivalenceEdgeLabel<NODE>, WeakEquivalenceEdgeLabel<NODE>> meet
			= WeakEquivalenceEdgeLabel::meet;
		final WeakEquivalenceEdgeLabel<NODE> nullLabel = new WeakEquivalenceEdgeLabel<>(this);
		final Map<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE>> graph = mWeakEquivalenceEdges;
		final Function<WeakEquivalenceEdgeLabel<NODE>, WeakEquivalenceEdgeLabel<NODE>> labelCloner =
				weqLabel -> new WeakEquivalenceEdgeLabel<NODE>(this, weqLabel);

		final FloydWarshall<NODE, WeakEquivalenceEdgeLabel<NODE>> fw =
				new FloydWarshall<NODE, WeakEquivalenceEdgeLabel<NODE>>(
						smallerThan, plus, meet, nullLabel, graph, labelCloner);
//				new FloydWarshall<>(this,
//						cwelpc::isStrongerOrEqual,
////				new FloydWarshall<>(WeakEquivalenceEdgeLabel::isStrongerThan,
//						cwelpc::union,
////						WeakEquivalenceEdgeLabel::union,
//						WeakEquivalenceEdgeLabel::meet,
//						new WeakEquivalenceEdgeLabel<NODE>(this),
//						mWeakEquivalenceEdges,
//						WeakEquivalenceEdgeLabel<NODE>::new);
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
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE>> edge
				: mWeakEquivalenceEdges.entrySet()) {
			if (!edge.getValue().isTautological()) {
				return false;
			}
		}
		return true;
	}

	public boolean isStrongerThan(final WeakEquivalenceGraph<NODE> other) {
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE>> otherWeqEdgeAndLabel
				: other.mWeakEquivalenceEdges.entrySet()) {
			final WeakEquivalenceEdgeLabel<NODE> correspondingWeqEdgeInThis =
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
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE>> edge : mWeakEquivalenceEdges.entrySet()) {
			final List<Term> dnfAsCubeList = new ArrayList<>();
			dnfAsCubeList.addAll(edge.getValue().toDNF(script));

			final NODE source = edge.getKey().getOneElement();
			final NODE target = edge.getKey().getOtherElement();
			assert source.hasSameTypeAs(target);

			final Term arrayEquation = computeArrayEquation(script, source, target);

			dnfAsCubeList.add(arrayEquation);

			final Term edgeFormula = SmtUtils.quantifier(script, QuantifiedFormula.FORALL,
					new HashSet<TermVariable>(computeWeqIndicesForArray(edge.getKey().getOneElement())),
					SmtUtils.or(script, dnfAsCubeList));
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

	public  Map<NODE, WeakEquivalenceEdgeLabel<NODE>> getAdjacentWeqEdges(final NODE appliedFunction) {
		final Map<NODE, WeakEquivalenceEdgeLabel<NODE>> result = new HashMap<>();
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE>> en : mWeakEquivalenceEdges.entrySet()) {
			if (en.getKey().getOneElement().equals(appliedFunction)) {
				result.put(en.getKey().getOtherElement(), en.getValue());
			}
			if (en.getKey().getOtherElement().equals(appliedFunction)) {
				result.put(en.getKey().getOneElement(), en.getValue());
			}
		}
		return result;
	}

	public  Map<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE>> getEdges() {
		return Collections.unmodifiableMap(mWeakEquivalenceEdges);
	}

	/**
	 *
	 * @param sourceAndTarget
	 * @param paList
	 * @return true iff label became strictly stronger
	 */
	private boolean strengthenEdgeLabel(final Doubleton<NODE> sourceAndTarget,
			final Set<CongruenceClosure<NODE>> paList) {
		assert mPartialArrangement.isRepresentative(sourceAndTarget.getOneElement())
			&& mPartialArrangement.isRepresentative(sourceAndTarget.getOtherElement());
		assert !sourceAndTarget.getOneElement().equals(sourceAndTarget.getOtherElement());
		assert paList.stream().allMatch(l -> l.assertHasOnlyWeqVarConstraints(mFactory.getAllWeqNodes()));
		assert paList.size() != 1 || !paList.iterator().next().isTautological() : "catch this case before?";
		assert sanityCheck();

		final WeakEquivalenceEdgeLabel<NODE> oldLabel = mWeakEquivalenceEdges.get(sourceAndTarget);

		if (paList.isEmpty()) {
			mWeakEquivalenceEdges.put(sourceAndTarget, new WeakEquivalenceEdgeLabel<NODE>(this, paList));
//			mArrayEqualities.addPair(sourceAndTarget.getOneElement(), sourceAndTarget.getOtherElement());
			addArrayEquality(sourceAndTarget.getOneElement(), sourceAndTarget.getOtherElement());
			return oldLabel == null || !oldLabel.isInconsistent();
		}

		if (oldLabel == null || oldLabel.isTautological()) {
			assert paList.size() != 1 || !paList.iterator().next().isTautological();

			final WeakEquivalenceEdgeLabel<NODE> newLabel = new WeakEquivalenceEdgeLabel<NODE>(this, paList);
			newLabel.meetWithCcGpa();
			final WeakEquivalenceEdgeLabel<NODE> newLabelMeetProject =
					newLabel.projectToElements(mFactory.getAllWeqNodes());
			mWeakEquivalenceEdges.put(sourceAndTarget, newLabelMeetProject);

			assert sanityCheck();
			return true;
		}

		final WeakEquivalenceEdgeLabel<NODE> oldLabelCopy = new WeakEquivalenceEdgeLabel<NODE>(this, oldLabel);

		final WeakEquivalenceEdgeLabel<NODE> labelToStrengthenWith = new WeakEquivalenceEdgeLabel<NODE>(this, paList);
		assert labelToStrengthenWith.sanityCheck() : "input label not normalized??";

		labelToStrengthenWith.meetWithCcGpa();
		oldLabelCopy.meetWithCcGpa();
		if (oldLabelCopy.isStrongerThan(labelToStrengthenWith)) {
			// nothing to do
			return false;
		}

		WeakEquivalenceEdgeLabel<NODE> strengthenedEdgeLabel = oldLabelCopy.meet(labelToStrengthenWith);

		// meet with gpa (done before) and project afterwards
		strengthenedEdgeLabel = strengthenedEdgeLabel.projectToElements(mFactory.getAllWeqNodes());

		// inconsistency check
		if (strengthenedEdgeLabel.isInconsistent()) {
//			mArrayEqualities.addPair(sourceAndTarget.getOneElement(), sourceAndTarget.getOtherElement());
			addArrayEquality(sourceAndTarget.getOneElement(), sourceAndTarget.getOtherElement());
		}

		assert strengthenedEdgeLabel.sanityCheck();
		// replace the edge label by the strengthened version
		mWeakEquivalenceEdges.put(sourceAndTarget, strengthenedEdgeLabel);
		assert sanityCheck();
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
			final WeakEquivalenceEdgeLabel<NODE> value) {
		assert mPartialArrangement.isRepresentative(sourceAndTarget.getOneElement())
			&& mPartialArrangement.isRepresentative(sourceAndTarget.getOtherElement());
		assert sourceAndTarget.getOneElement().getTerm().getSort().equals(sourceAndTarget.getOtherElement().getTerm().getSort());

		final boolean result = strengthenEdgeLabel(sourceAndTarget, value.getLabelContents());
		assert sanityCheck();
		return result;
	}

	public boolean reportWeakEquivalence(final NODE array1, final NODE array2,
			final Set<CongruenceClosure<NODE>> edgeLabelContents) {
		assert mPartialArrangement.isRepresentative(array1) && mPartialArrangement.isRepresentative(array2);
		if (edgeLabelContents.size() == 1 && edgeLabelContents.iterator().next().isTautological()) {
			return false;
		}

		final boolean result = reportWeakEquivalence(new Doubleton<NODE>(array1, array2),
				new WeakEquivalenceEdgeLabel<NODE>(this, edgeLabelContents));
		assert sanityCheck();
		return result;
	}

	public boolean isConstrained(final NODE elem) {
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE>> edge : mWeakEquivalenceEdges.entrySet()) {
			if (edge.getValue().isConstrained(elem)) {
				return true;
			}
		}
		return false;
	}

	public Set<CongruenceClosure<NODE>> getEdgeLabelContents(final NODE array1, final NODE array2) {
		final WeakEquivalenceEdgeLabel<NODE> edge =
				mWeakEquivalenceEdges.get(new Doubleton<>(array1, array2));
		if (edge != null) {
			return edge.getLabelContents();
		}
		return Collections.singleton(new CongruenceClosure<>(getLogger()));
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
	public Set<CongruenceClosure<NODE>> projectEdgeLabelToPoint(
			final Set<CongruenceClosure<NODE>> labelContents, final NODE value,
			final List<NODE> weqVarsForThisEdge) {

		final WeakEquivalenceEdgeLabel<NODE> originalEdgeLabel =
				new WeakEquivalenceEdgeLabel<NODE>(this, labelContents);

		final NODE firstDimWeqVarNode = weqVarsForThisEdge.get(0);

		final CongruenceClosure<NODE> qEqualsI = new CongruenceClosure<>(getLogger());

		qEqualsI.reportEquality(firstDimWeqVarNode, value);

		final WeakEquivalenceEdgeLabel<NODE> copy =
				new WeakEquivalenceEdgeLabel<NODE>(this, originalEdgeLabel);

//		copy.meetWithWeqGpa();
		copy.meetWithCcGpa();

		final WeakEquivalenceEdgeLabel<NODE> meet =
				copy.meetRec(Collections.singleton(qEqualsI));

		meet.setExternalRemInfo(mPartialArrangement.getElementCurrentlyBeingRemoved());
		meet.projectWeqVarNode(firstDimWeqVarNode);

		meet.inOrDecreaseWeqVarIndices(-1, weqVarsForThisEdge);
		assert !meet.getAppearingNodes().contains(weqVarsForThisEdge.get(weqVarsForThisEdge.size() - 1)) : "double "
				+ "check the condition if this assertion fails, but as we decreased all weq vars, the last one should "
				+ "not be present in the result, right?..";
		assert !meet.mLabel.stream().anyMatch(l -> l.isInconsistent()) : "label not well-formed";

		assert meet.sanityCheckDontEnforceProjectToWeqVars(mPartialArrangement);

		final WeakEquivalenceEdgeLabel<NODE> result =
				meet.projectToElements(new HashSet<>(weqVarsForThisEdge));

		assert result.assertHasOnlyWeqVarConstraints(new HashSet<>(weqVarsForThisEdge));

		assert result.sanityCheck();
		return result.getLabelContents();
	}

	/**
	 * used for roweq-1 rule
	 *
	 * @param labelContents
	 * @param argument
	 * @param weqVarsForResolventEdge
	 * @return
	 */
	public Set<CongruenceClosure<NODE>> shiftLabelAndAddException(
			final Set<CongruenceClosure<NODE>> labelContents, final NODE argument,
			final List<NODE> weqVarsForResolventEdge) {
		assert !weqVarsForResolventEdge.isEmpty() : "because the array in the resolvent must have a dimension >= 1";

		final WeakEquivalenceEdgeLabel<NODE> meet =
				new WeakEquivalenceEdgeLabel<NODE>(this, labelContents);

//		meet.meetWithWeqGpa();
		meet.meetWithCcGpa();

		meet.setExternalRemInfo(mPartialArrangement.getElementCurrentlyBeingRemoved());
		meet.projectWeqVarNode(weqVarsForResolventEdge.get(weqVarsForResolventEdge.size() - 1));

		final WeakEquivalenceEdgeLabel<NODE> labelToShiftAndAdd =
				meet.projectToElements(new HashSet<>(weqVarsForResolventEdge));

		labelToShiftAndAdd.inOrDecreaseWeqVarIndices(1, weqVarsForResolventEdge);

		final NODE firstWeqVar = weqVarsForResolventEdge.get(0);
		assert !labelToShiftAndAdd.getAppearingNodes().contains(firstWeqVar);

		final Set<CongruenceClosure<NODE>> shiftedLabelContents =
				new HashSet<>(labelToShiftAndAdd.getLabelContents());

		final CongruenceClosure<NODE> firstWeqVarUnequalArgument = new CongruenceClosure<>(getLogger());
		firstWeqVarUnequalArgument.reportDisequality(firstWeqVar, argument);
		shiftedLabelContents.add(firstWeqVarUnequalArgument);
		assert shiftedLabelContents.stream().allMatch(l -> l.sanityCheckOnlyCc());

		final Set<CongruenceClosure<NODE>> normalized = mWeqCcManager
				.filterRedundantCcs(new HashSet<>(shiftedLabelContents));

		assert normalized.stream().allMatch(l -> l.sanityCheckOnlyCc());
		return normalized;
	}

//	private static <NODE extends ICongruenceClosureElement<NODE>> List<CongruenceClosure<NODE>> simplifyPaDisjunction(
//			final List<CongruenceClosure<NODE>> newLabelContents) {
//		// make a copy of the list, filter out false disjuncts
//		List<CongruenceClosure<NODE>> newLabel = new ArrayList<>(newLabelContents).stream()
//				.filter(pa -> !pa.isInconsistent()).collect(Collectors.toList());
//
//		// if there is any true disjunct, it will annihilate all the others
//		if (newLabel.stream().anyMatch(pa -> pa.isTautological())) {
//			newLabel = Collections.singletonList(new CongruenceClosure<>());
//		}
//
//		return newLabel;
//	}

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
			for (final Entry<NODE, WeakEquivalenceEdgeLabel<NODE>> edge
					: getAdjacentWeqEdges(node2OldRep).entrySet()) {
				mWeakEquivalenceEdges.remove(new Doubleton<>(node2OldRep, edge.getKey()));
				mWeakEquivalenceEdges.put(new Doubleton<>(newRep, edge.getKey()), edge.getValue());
			}
		} else {
			// node1OldRep is not representative anymore
			for (final Entry<NODE, WeakEquivalenceEdgeLabel<NODE>> edge
					: getAdjacentWeqEdges(node1OldRep).entrySet()) {
				mWeakEquivalenceEdges.remove(new Doubleton<>(node1OldRep, edge.getKey()));
				mWeakEquivalenceEdges.put(new Doubleton<>(newRep, edge.getKey()), edge.getValue());
			}
		}

		// we can remove array equalities between the nodes that are merged now anyways..
		mArrayEqualities.removePair(node1OldRep, node2OldRep);
		mArrayEqualities.removePair(node2OldRep, node1OldRep);

		if (node1OldRep == newRep) {
			mArrayEqualities.replaceDomainElement(node2OldRep, newRep);
			mArrayEqualities.replaceRangeElement(node2OldRep, newRep);
		} else {
			assert node2OldRep == newRep;
			mArrayEqualities.replaceDomainElement(node1OldRep, newRep);
			mArrayEqualities.replaceRangeElement(node1OldRep, newRep);
		}
		assert !mArrayEqualities.containsPair(node1OldRep, node2OldRep)
			&& !mArrayEqualities.containsPair(node2OldRep, node1OldRep) : "TODO: treat this case";
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

	/**
	 *
	 * @param originalPa a version of the gpa before we started to meet edgeLabels with the gpa (resulting in changed
	 *  edgeLabels in the gpa (mPartialArrangement))
	 */
	public void meetEdgeLabelsWithWeqGpaBeforeRemove(final WeqCongruenceClosure<NODE> originalPa) {
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE>> edgeLabel
				: mWeakEquivalenceEdges.entrySet()) {
			edgeLabel.getValue().meetWithWeqGpa(originalPa);

			if (edgeLabel.getValue().isInconsistent()) {
//				mArrayEqualities.addPair(edgeLabel.getKey().getOneElement(), edgeLabel.getKey().getOtherElement());
				addArrayEquality(edgeLabel.getKey().getOneElement(), edgeLabel.getKey().getOtherElement());
			}
		}
//		mWeqMeetMode = true;
	}

	public void meetEdgeLabelsWithCcGpaBeforeRemove() {
//		for (final WeakEquivalenceEdgeLabel<NODE> edgeLabel : mWeakEquivalenceEdges.values()) {
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE>> edgeLabel
				: mWeakEquivalenceEdges.entrySet()) {
			edgeLabel.getValue().meetWithCcGpa();
			if (edgeLabel.getValue().isInconsistent()) {
//				mArrayEqualities.addPair(edgeLabel.getKey().getOneElement(), edgeLabel.getKey().getOtherElement());
				addArrayEquality(edgeLabel.getKey().getOneElement(), edgeLabel.getKey().getOtherElement());
			}
		}
//		mWeqMeetMode = false;
	}

	private void addArrayEquality(final NODE oneElement, final NODE otherElement) {
		mArrayEqualities.addPair(oneElement, otherElement);
	}

	public boolean elementIsFullyRemoved(final NODE elem) {
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE>> edge
				: mWeakEquivalenceEdges.entrySet()) {
			if (edge.getKey().getOneElement().equals(elem)) {
				assert false;
				return false;
			}
			if (edge.getKey().getOtherElement().equals(elem)) {
				assert false;
				return false;
			}
			if (!edge.getValue().assertElementIsFullyRemoved(elem)) {
				assert false;
				return false;
			}
		}
		return true;
	}

	Map<String, Integer> summarize() {
		final Map<String, Integer> result = new HashMap<>();

		result.put("#Edges", mWeakEquivalenceEdges.size());

		final int noEdgeLabelDisjuncts = mWeakEquivalenceEdges.values().stream()
				.map(weqEdge -> weqEdge.getLabelContents().size())
				.reduce((i1, i2) -> i1 + i2)
				.get();
		result.put("#EdgeLabelDisjuncts", noEdgeLabelDisjuncts);

		result.put("Average#EdgeLabelDisjuncts", noEdgeLabelDisjuncts == 0 ? -1 :
					mWeakEquivalenceEdges.size()/noEdgeLabelDisjuncts);

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
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE>> weq :
			mWeakEquivalenceEdges.entrySet()) {
			sb.append(weq.getKey());
			sb.append("\n");
		}
		return sb.toString();
	}

	public String toLogString() {
		final StringBuilder sb = new StringBuilder();

		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE>> weq :
			mWeakEquivalenceEdges.entrySet()) {
			sb.append(weq.getKey());
			sb.append("\n");
			sb.append(weq.getValue().toLogString());
			sb.append("\n");
		}

		return sb.toString();
	}

	boolean sanityCheck() {
		assert mWeqCcManager != null;

		//		if (mPartialArrangement.mMeetWithGpaCase) {
		//			// TODO sharpen sanity check for this case
		//			return true;
		//		}
		if (mPartialArrangement != null && mPartialArrangement.isInconsistent()) {
			// we will drop this weak equivalence graph anyway
			return true;
		}

		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE>> en
				: mWeakEquivalenceEdges.entrySet()) {
			assert en.getValue().sanityCheck();
		}

		assert sanityAllNodesOnWeqLabelsAreKnownToGpa(null);

		return sanityCheckWithoutNodesComparison();
	}

	boolean sanityCheckWithoutNodesComparison() {
		assert mFactory != null : "factory is needed for the sanity check..";


		/*
		 * check that the edges only connect compatible arrays
		 *  compatible means having the same Sort, in particular: dimensionality
		 */
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE>> edge : mWeakEquivalenceEdges.entrySet()) {
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
			for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE>> edge : mWeakEquivalenceEdges.entrySet()) {
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
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE>> edge : mWeakEquivalenceEdges.entrySet()) {
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

	/**
	 * check that no weak equivalence edge contains a NODE that is not known to mPartialArrangement
	 * or is one of the special quantified variables from getVariableForDimension(..).
	 * @param nodesScheduledForAdding
	 */
	protected boolean sanityAllNodesOnWeqLabelsAreKnownToGpa(final Set<NODE> nodesScheduledForAdding) {
		if (mPartialArrangement != null) {
			for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE>> edge : mWeakEquivalenceEdges.entrySet()) {

				final WeakEquivalenceEdgeLabel<NODE> label = edge.getValue();

				final Set<NODE> nodesOnEdgeLabelWithoutWeqNodes = label.getAppearingNodes().stream()
						.filter(node -> !CongruenceClosure.dependsOnAny(node, mFactory.getAllWeqNodes()))
						.filter(node -> nodesScheduledForAdding == null
							|| !nodesScheduledForAdding.contains(node))
						.collect(Collectors.toSet());

				if (!mPartialArrangement.getAllElements().containsAll(nodesOnEdgeLabelWithoutWeqNodes)) {
					final Set<NODE> difference = DataStructureUtils.difference(nodesOnEdgeLabelWithoutWeqNodes,
							mPartialArrangement.getAllElements());
					assert false : "weq edge contains node(s) that has been removed: " + difference;
					return false;
				}
			}
		}
		return true;
	}

	class CachingWeqEdgeLabelPoComparator {

		private final PartialOrderCache<CongruenceClosure<NODE>> mCcPoCache;

		public CachingWeqEdgeLabelPoComparator() {
			mCcPoCache = new PartialOrderCache<>(mWeqCcManager.getCcComparator());
		}

		boolean isStrongerOrEqual(final WeakEquivalenceEdgeLabel<NODE> label1,
				final WeakEquivalenceEdgeLabel<NODE> label2) {
			return label1.isStrongerThan(label2, mCcPoCache::lowerEqual);
		}

		WeakEquivalenceEdgeLabel<NODE> union(final WeakEquivalenceEdgeLabel<NODE> label1,
				final WeakEquivalenceEdgeLabel<NODE> label2) {
			return label1.union(label2, mCcPoCache);
		}

	}

	public ILogger getLogger() {
		return mPartialArrangement.getLogger();
	}

	public WeqCcManager<NODE> getWeqCcManager() {
		return mWeqCcManager;
	}

	public EqConstraintFactory<NODE> getFactory() {
		return mFactory;
	}

//	public void resetArrayEqualities() {
//		mArrayEqualities.clear();
//	}
}

