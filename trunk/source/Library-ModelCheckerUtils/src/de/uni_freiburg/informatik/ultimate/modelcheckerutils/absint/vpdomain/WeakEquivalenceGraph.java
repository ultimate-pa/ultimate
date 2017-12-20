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
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.EqualityStatus;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.CongruenceClosure;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.ICongruenceClosure;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.PartialOrderCache;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * (short: weq graph)
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class WeakEquivalenceGraph<NODE extends IEqNodeIdentifier<NODE>, DISJUNCT extends ICongruenceClosure<NODE>> {

	private final WeqCcManager<NODE> mWeqCcManager;

	private final Map<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> mWeakEquivalenceEdges;

	private final HashRelation<NODE, NODE> mArrayEqualities;

	/**
	 * The WeqCongruenceClosure that this weq graph is part of. This may be null, if we use this weq graph as an
	 * intermediate, for example during a join or meet operation.
	 */
	final WeqCongruenceClosure<NODE> mPartialArrangement;

	private boolean mIsFrozen;

	/**
	 * true iff currently the labels incorporate the ground information we have
	 */
	private boolean mFat;

//	/**
//	 * true if mFat and the ground information is the whole WeqCc (as opposed to just the Cc)
//	 */
//	boolean mWeqFat;

	/**
	 * Used as a representative of the DISJUNCT type as it is currently instantiated
	 */
	final DISJUNCT mEmptyDisjunct;

	/**
	 * Constructs an empty WeakEquivalenceGraph
	 * @param factory
	 */
	public WeakEquivalenceGraph(final WeqCongruenceClosure<NODE> pArr, final WeqCcManager<NODE> manager,
			final DISJUNCT emptyDisjunct) {
		mPartialArrangement = pArr;
		mWeakEquivalenceEdges = new HashMap<>();
		mArrayEqualities = new HashRelation<>();
		mWeqCcManager = manager;
		mEmptyDisjunct = emptyDisjunct;
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
			final Map<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> weakEquivalenceEdges,
			final HashRelation<NODE, NODE> arrayEqualities,
			final WeqCcManager<NODE> manager,
			final DISJUNCT emptyDisjunct) {
		mPartialArrangement = null;
		mWeakEquivalenceEdges = weakEquivalenceEdges;
		mArrayEqualities = arrayEqualities;
		mWeqCcManager = manager;
		mEmptyDisjunct = emptyDisjunct;
		assert sanityCheck();
	}

	/**
	 * Copy constructor, unfreezes edge label disjuncts
	 *
	 * @param weakEquivalenceGraph
	 * @param factory
	 */
	public WeakEquivalenceGraph(final WeqCongruenceClosure<NODE> pArr,
			final WeakEquivalenceGraph<NODE, DISJUNCT> weakEquivalenceGraph, final boolean flattenEdges) {

		mPartialArrangement = pArr;

		mArrayEqualities = new HashRelation<>(weakEquivalenceGraph.mArrayEqualities);
		mWeakEquivalenceEdges = new HashMap<>();
		mWeqCcManager = weakEquivalenceGraph.getWeqCcManager();
		mEmptyDisjunct = weakEquivalenceGraph.mEmptyDisjunct;

		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> weqEdge
				: weakEquivalenceGraph.mWeakEquivalenceEdges.entrySet()) {

			// make sure that the representatives in pArr and in our new weq edges are compatible
			final Doubleton<NODE> newSoureceAndTarget = new Doubleton<>(
					pArr.getRepresentativeElement(weqEdge.getKey().getOneElement()),
					pArr.getRepresentativeElement(weqEdge.getKey().getOtherElement()));

			if (flattenEdges) {
				final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> flattenedEdgeLabel = weqEdge.getValue().flatten(this);
				putEdgeLabel(newSoureceAndTarget, flattenedEdgeLabel);
			} else {
				putEdgeLabel(newSoureceAndTarget, new WeakEquivalenceEdgeLabel<NODE, DISJUNCT>(this,
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

	@Deprecated
	public boolean reportChangeInGroundPartialArrangement(final Predicate<DISJUNCT> action) {
		assert !mIsFrozen;
		boolean madeChanges = false;
		final Map<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> weqCopy = new HashMap<>(mWeakEquivalenceEdges);
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> edge : weqCopy.entrySet())  {
			final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> newLabel =
					edge.getValue().reportChangeInGroundPartialArrangement(action);
			if (newLabel.isInconsistent()) {
				/*
				 *  edge label became inconsistent
				 *   <li> report a strong equivalence
				 *   <li> keep the edge for now, as we may still want to do propagations based on it, it will be removed
				 *     later
				 */
				addArrayEquality(edge.getKey().getOneElement(), edge.getKey().getOtherElement());
				madeChanges = true;
			}
			putEdgeLabel(edge.getKey(), newLabel);
			// TODO is the madeChanges flag worth this effort?.. should we just always say "true"?..
			madeChanges |= !mWeqCcManager.isEquivalentICc(edge.getValue(), newLabel);
		}
		return madeChanges;
	}

	/**
	 * Replaces each weq edge leading to elem with an edge leading to replacement instead.
	 * (If replacement is null, the edge is just removed.)
	 *
	 * @param elem
	 * @param replacement
	 */
	public void replaceVertex(final NODE elem, final NODE replacement) {

		final Map<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> edgesCopy = new HashMap<>(mWeakEquivalenceEdges);

		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> en : edgesCopy.entrySet()) {

			final NODE source = en.getKey().getOneElement();
			final NODE target = en.getKey().getOtherElement();

			if (source.equals(elem)) {
				final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> label =
						mWeakEquivalenceEdges.remove(en.getKey());
				if (replacement != null) {
					putEdgeLabelDuringRemove(new Doubleton<NODE>(replacement, target), label, replacement);
				}
			} else if (target.equals(elem)) {
				final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> label =
						mWeakEquivalenceEdges.remove(en.getKey());
				if (replacement != null) {
					putEdgeLabelDuringRemove(new Doubleton<NODE>(source, replacement), label, replacement);
				}
			}
		}
	}

	/**
	 * Computes a new WeakEquivalenceGraph whose edges are _thinned_ copies of this's edges.
	 *
	 * @param baseWeqCc
	 * @return
	 */
	public WeakEquivalenceGraph<NODE, CongruenceClosure<NODE>> thinLabels(final WeqCongruenceClosure<NODE> baseWeqCc) {
		assert mFat;

		final WeakEquivalenceGraph<NODE, CongruenceClosure<NODE>> result =
			new WeakEquivalenceGraph<NODE, CongruenceClosure<NODE>>(baseWeqCc, mWeqCcManager,
					mWeqCcManager.getEmptyCc(false));

		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> en : getWeqEdgesEntrySet()) {
			result.reportWeakEquivalence(en.getKey().getOneElement(), en.getKey().getOtherElement(),
					en.getValue().thin(result));
		}
		return result;
	}

	/**
	 * Project away elem and all its dependents in all edge labels of this WeqGraph.
	 *
	 * @param elem
	 * @param useWeqGpa determines whether the meet that is done before projecting away, is done with the full
	 *  WeqCongruenceClosure mPartialArrangement or only with its CongruenceClosure.
	 *
	 * @return a set of nodes that has been added during projecting (and thus will need to be added to
	 *  mPartialArrangement)
	 */
	public Set<NODE> projectAwaySimpleElementInEdgeLabels(final NODE elem, final boolean useWeqGpa) {
		assert !mIsFrozen;
		final Set<NODE> nodesToAdd = new HashSet<>();
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> en : getWeqEdgesEntrySet()) {
			assert !elem.equals(en.getKey().getOneElement());
			assert !elem.equals(en.getKey().getOtherElement());

			nodesToAdd.addAll(en.getValue().projectAwaySimpleElement(elem, useWeqGpa));
		}
		assert assertElementIsFullyRemoved(elem);
		return nodesToAdd;
	}

	public void transformElementsAndFunctions(final Function<NODE, NODE> transformer) {
		final HashMap<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> weqEdgesCopy =
				new HashMap<>(mWeakEquivalenceEdges);
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> en : weqEdgesCopy.entrySet()) {
			mWeakEquivalenceEdges.remove(en.getKey());

			final Doubleton<NODE> newDton = new Doubleton<>(
					transformer.apply(en.getKey().getOneElement()),
					transformer.apply(en.getKey().getOtherElement()));
			en.getValue().transformElements(transformer);
			putEdgeLabel(newDton, en.getValue());
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
	WeakEquivalenceGraph<NODE, DISJUNCT> join(final WeakEquivalenceGraph<NODE, DISJUNCT> other) {
		assert mPartialArrangement != null && other.mPartialArrangement != null : "we need the partial for the join"
				+ "of the weq graphs, because strong equalities influence the weak ones..";

		final Map<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> newWeakEquivalenceEdges = new HashMap<>();
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> thisWeqEdge
				: this.getWeqEdgesEntrySet()) {
			final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> correspondingWeqEdgeLabelInOther =
					other.getEdgeLabel(thisWeqEdge.getKey());

			final NODE source = thisWeqEdge.getKey().getOneElement();
			final NODE target = thisWeqEdge.getKey().getOtherElement();

			/*
			 * if the other weq graph's partial arrangement has a strong equivalence for the current edge, we can
			 * keep the current edge.
			 */
			if (other.mPartialArrangement.hasElements(source, target)
					&& other.mPartialArrangement.getEqualityStatus(source, target) == EqualityStatus.EQUAL) {
				// case 1: x--phi--y in this, x~y in other:

				final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> newEdgeLabel = thisWeqEdge.getValue()
						.meet(Collections.singleton(this.mPartialArrangement.getCongruenceClosure()))
						.projectToElements(mWeqCcManager.getAllWeqNodes());

				putEdgeLabel(thisWeqEdge.getKey(), newEdgeLabel);
				assert correspondingWeqEdgeLabelInOther == null;
				continue;
			}

			if (correspondingWeqEdgeLabelInOther == null) {
				// case 2: x--phi--y in this, no constraint on x, y in other
				continue;
			}

			// case 3: x--phi--y in this, x--phi'--y in other

			// "meetWGpa", projectTo
			final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> thisNewEdgeLabel = thisWeqEdge.getValue()
						.meet(Collections.singleton(this.mPartialArrangement.getCongruenceClosure()))
						.projectToElements(mWeqCcManager.getAllWeqNodes());
			final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> otherNewEdgeLabel =
					correspondingWeqEdgeLabelInOther
						.meet(Collections.singleton(other.mPartialArrangement.getCongruenceClosure()))
						.projectToElements(mWeqCcManager.getAllWeqNodes());

			putEdgeLabel(thisWeqEdge.getKey(), thisNewEdgeLabel.union(otherNewEdgeLabel));
		}

		/*
		 * for the case strong equivalence in this, weak equivalence in other, we iterate other's weak equivalence edges
		 */
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> otherWeqEdge
				: other.getWeqEdgesEntrySet()) {
			final NODE source = otherWeqEdge.getKey().getOneElement();
			final NODE target = otherWeqEdge.getKey().getOtherElement();

			if (this.mPartialArrangement.hasElements(source, target)
					&& this.mPartialArrangement.getEqualityStatus(source, target) == EqualityStatus.EQUAL) {
				// case 4: x~y in this, x--phi--y in other
				final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> newEdgeLabel = otherWeqEdge.getValue()
						.meet(Collections.singleton(other.mPartialArrangement.getCongruenceClosure()))
						.projectToElements(mWeqCcManager.getAllWeqNodes());

				putEdgeLabel(otherWeqEdge.getKey(), newEdgeLabel);
				continue;
			}
		}

		final WeakEquivalenceGraph<NODE> result = new WeakEquivalenceGraph<>(newWeakEquivalenceEdges,
				new HashRelation<>(), mWeqCcManager);
		assert result.sanityCheck();
		return result;
	}

	boolean hasArrayEqualities() {
		return !mArrayEqualities.isEmpty();
	}

	Map<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> propagateViaTriangleRule() {
		if (mWeakEquivalenceEdges.isEmpty()) {
			return Collections.emptyMap();
		}

		//(the following variable are declared just to make their types clear, and detect type errors easier)

		final CachingWeqEdgeLabelPoComparator cwelpc = new CachingWeqEdgeLabelPoComparator();

		final BiPredicate<WeakEquivalenceEdgeLabel<NODE, DISJUNCT>, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> smallerThan =
				cwelpc::isStrongerOrEqual;
		final BiFunction<
				WeakEquivalenceEdgeLabel<NODE, DISJUNCT>,
				WeakEquivalenceEdgeLabel<NODE, DISJUNCT>,
				WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> plus
			= cwelpc::union;
		final BiFunction<
				WeakEquivalenceEdgeLabel<NODE, DISJUNCT>,
				WeakEquivalenceEdgeLabel<NODE, DISJUNCT>,
				WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> meet
			= mWeqCcManager::meetEdgeLabelsNonDestructive;
		final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> nullLabel =
				new WeakEquivalenceEdgeLabel<>(this, mEmptyDisjunct);
		final Map<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> graph = mWeakEquivalenceEdges;
		final Function<WeakEquivalenceEdgeLabel<NODE, DISJUNCT>, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> labelCloner =
				weqLabel -> new WeakEquivalenceEdgeLabel<NODE, DISJUNCT>(this, weqLabel);

		//execute the floyd-warshall algorithm
		final FloydWarshall<NODE, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> fw =
				new FloydWarshall<NODE, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>>(
						smallerThan, plus, meet, nullLabel, graph, labelCloner);

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
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> edge
				: getWeqEdgesEntrySet()) {
			if (!edge.getValue().isTautological()) {
				return false;
			}
		}
		return true;
	}

	boolean isStrongerThan(final WeakEquivalenceGraph<NODE, DISJUNCT> other) {
		assert this.isFrozen() && other.isFrozen();

		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> otherWeqEdgeAndLabel
				: other.getWeqEdgesEntrySet()) {
			final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> correspondingWeqEdgeInThis =
					getEdgeLabel(otherWeqEdgeAndLabel.getKey());
			if (correspondingWeqEdgeInThis == null) {
				// "other" has an edge that "this" does not -- this cannot be stronger
				return false;
			}
			// if the this-edge is strictly weaker than the other-edge, we have a counterexample
			if (!mWeqCcManager.isStrongerThan(correspondingWeqEdgeInThis, otherWeqEdgeAndLabel.getValue())) {
				return false;
			}
		}
		return true;
	}

	boolean isFrozen() {
		return mIsFrozen;
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
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> edge : getWeqEdgesEntrySet()) {
			final List<Term> dnfAsCubeList = new ArrayList<>();
			dnfAsCubeList.addAll(edge.getValue().toDnf(script));

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
			indexEntries.add(mWeqCcManager.getWeqVariableForDimension(i, mdSort.getIndexSorts().get(i)));
		}
		return indexEntries;
	}

	public  Map<NODE, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> getAdjacentWeqEdges(final NODE appliedFunction) {
		final Map<NODE, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> result = new HashMap<>();
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> en : getWeqEdgesEntrySet()) {
			if (en.getKey().getOneElement().equals(appliedFunction)) {
				result.put(en.getKey().getOtherElement(), en.getValue());
			}
			if (en.getKey().getOtherElement().equals(appliedFunction)) {
				result.put(en.getKey().getOneElement(), en.getValue());
			}
		}
		return result;
	}

	public  Map<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> getEdges() {
		return Collections.unmodifiableMap(mWeakEquivalenceEdges);
	}

	private void putEdgeLabel(final Doubleton<NODE> sourceAndTarget, final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> label) {
		assert mPartialArrangement.isRepresentative(sourceAndTarget.getOneElement());
		assert mPartialArrangement.isRepresentative(sourceAndTarget.getOtherElement());
		mWeakEquivalenceEdges.put(sourceAndTarget, label);
	}

	/**
	 * Like putEdgeLabel but with weaker sanity check -- if an element that occurred in mWeakEquivalenceEdges is
	 * removed, we first remove it from the weak equivalence graph and replace it with another one that is not removed.
	 * (This replacement will become the representative of the corresponding equivalence calls after remove.)
	 *
	 * @param sourceAndTarget
	 * @param label
	 * @param replacement
	 */
	private void putEdgeLabelDuringRemove(final Doubleton<NODE> sourceAndTarget,
			final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> label, final NODE replacement) {
		assert sourceAndTarget.getOneElement() == replacement
				|| mPartialArrangement.isRepresentative(sourceAndTarget.getOneElement());
		assert sourceAndTarget.getOtherElement() == replacement
				|| mPartialArrangement.isRepresentative(sourceAndTarget.getOtherElement());
		mWeakEquivalenceEdges.put(sourceAndTarget, label);
	}

	private WeakEquivalenceEdgeLabel<NODE, DISJUNCT> getEdgeLabel(final Doubleton<NODE> sourceAndTarget) {
		return mWeakEquivalenceEdges.get(sourceAndTarget);
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
			final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> value) {
		assert !mIsFrozen;
		assert mPartialArrangement.isRepresentative(sourceAndTarget.getOneElement())
			&& mPartialArrangement.isRepresentative(sourceAndTarget.getOtherElement());
		assert sourceAndTarget.getOneElement().getTerm().getSort().equals(sourceAndTarget.getOtherElement().getTerm().getSort());
		final Set<DISJUNCT> paList = value.getDisjuncts();

				assert !mIsFrozen;
		assert mPartialArrangement.isRepresentative(sourceAndTarget.getOneElement())
			&& mPartialArrangement.isRepresentative(sourceAndTarget.getOtherElement());
		assert !sourceAndTarget.getOneElement().equals(sourceAndTarget.getOtherElement());
//		assert paList.stream().allMatch(l -> l.assertHasOnlyWeqVarConstraints(mWeqCcManager.getAllWeqNodes()));
		assert paList.size() != 1 || !paList.iterator().next().isTautological() : "catch this case before?";
		assert sanityCheck();

		final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> oldLabel = getEdgeLabel(sourceAndTarget);

		if (paList.isEmpty()) {
			putEdgeLabel(sourceAndTarget, new WeakEquivalenceEdgeLabel<NODE, DISJUNCT>(this, paList));
			addArrayEquality(sourceAndTarget.getOneElement(), sourceAndTarget.getOtherElement());
			return oldLabel == null || !oldLabel.isInconsistent();
		}

		if (oldLabel == null || oldLabel.isTautological()) {
			assert paList.size() != 1 || !paList.iterator().next().isTautological();

			final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> newLabel = new WeakEquivalenceEdgeLabel<NODE, DISJUNCT>(this, paList);
			newLabel.meetWithCcGpa();
			final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> newLabelMeetProject =
					newLabel.projectToElements(mWeqCcManager.getAllWeqNodes());
			putEdgeLabel(sourceAndTarget, newLabelMeetProject);

			assert sanityCheck();
			return true;
		}

		final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> oldLabelCopy = new WeakEquivalenceEdgeLabel<NODE, DISJUNCT>(this, oldLabel);

		final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> labelToStrengthenWith = new WeakEquivalenceEdgeLabel<NODE, DISJUNCT>(this, paList);
		assert labelToStrengthenWith.sanityCheck() : "input label not normalized??";

		labelToStrengthenWith.meetWithCcGpa();
		oldLabelCopy.meetWithCcGpa();

		if (mWeqCcManager.isStrongerThan(oldLabelCopy, labelToStrengthenWith)) {
			// nothing to do
			return false;
		}

//		WeakEquivalenceEdgeLabel<NODE, DISJUNCT> strengthenedEdgeLabel = oldLabelCopy.meet(labelToStrengthenWith, inplace);
		WeakEquivalenceEdgeLabel<NODE, DISJUNCT> strengthenedEdgeLabel =
				mWeqCcManager.meetEdgeLabels(oldLabelCopy, labelToStrengthenWith, true);

		// meet with gpa (done before) and project afterwards
		strengthenedEdgeLabel = strengthenedEdgeLabel.projectToElements(mWeqCcManager.getAllWeqNodes());

		// inconsistency check
		if (strengthenedEdgeLabel.isInconsistent()) {
			addArrayEquality(sourceAndTarget.getOneElement(), sourceAndTarget.getOtherElement());
		}

		assert strengthenedEdgeLabel.sanityCheck();
		// replace the edge label by the strengthened version
		putEdgeLabel(sourceAndTarget, strengthenedEdgeLabel);
		assert sanityCheck();
		return true;
	}

	public boolean reportWeakEquivalence(final NODE array1, final NODE array2,
			final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> edgeLabel) {
		assert !mIsFrozen;
		assert mPartialArrangement.isRepresentative(array1) && mPartialArrangement.isRepresentative(array2);
		if (edgeLabel.isTautological()) {
			return false;
		}

		final boolean result = reportWeakEquivalence(new Doubleton<NODE>(array1, array2), edgeLabel);
		assert sanityCheck();
		return result;
	}

	public boolean isConstrained(final NODE elem) {
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> edge : getWeqEdgesEntrySet()) {
			if (edge.getValue().isConstrained(elem)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Retrieve the weak equivalence constraint between the given nodes.
	 * (resolves if the nodes are not representatives, returns a true label if there is no edge in the graph)
	 *
	 * @param array1
	 * @param array2
	 * @return
	 */
	public WeakEquivalenceEdgeLabel<NODE, DISJUNCT> getEdgeLabel(final NODE array1, final NODE array2) {
		if (array1.getSort() != array2.getSort()) {
			throw new IllegalArgumentException("asking for a weak equivalence between of different sorts make no "
					+ "sense");
		}

		final NODE array1Rep = mPartialArrangement.getRepresentativeElement(array1);
		final NODE array2Rep = mPartialArrangement.getRepresentativeElement(array2);
		final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> edge =
				getEdgeLabel(new Doubleton<>(array1Rep, array2Rep));
		if (edge == null) {
			// if there is no edge in the graph between the given vertices, we return a tautological edge
			return new WeakEquivalenceEdgeLabel<>(this);
		}
		return edge;
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
	public WeakEquivalenceEdgeLabel<NODE, DISJUNCT> projectEdgeLabelToPoint(final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> labelContents,
			final NODE value, final List<NODE> weqVarsForThisEdge) {

		final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> originalEdgeLabel =
				new WeakEquivalenceEdgeLabel<NODE, DISJUNCT>(this, labelContents);

		final NODE firstDimWeqVarNode = weqVarsForThisEdge.get(0);

		final CongruenceClosure<NODE> qEqualsICc = mWeqCcManager.getSingleEqualityCc(firstDimWeqVarNode, value, true);
		final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> qEqualsI = mWeqCcManager.getSingletonEdgeLabel(this, qEqualsICc);

		final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> copy =
				new WeakEquivalenceEdgeLabel<NODE, DISJUNCT>(this, originalEdgeLabel);

		copy.meetWithCcGpa();

		final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> meet =
				mWeqCcManager.meetEdgeLabelsNonDestructive(copy, qEqualsI);
//				copy.meetRec(Collections.singleton(qEqualsI));

		meet.setExternalRemInfo(mPartialArrangement.getElementCurrentlyBeingRemoved());
		meet.projectWeqVarNode(firstDimWeqVarNode);

		meet.inOrDecreaseWeqVarIndices(-1, weqVarsForThisEdge);
		assert !meet.getAppearingNodes().contains(weqVarsForThisEdge.get(weqVarsForThisEdge.size() - 1)) : "double "
				+ "check the condition if this assertion fails, but as we decreased all weq vars, the last one should "
				+ "not be present in the result, right?..";
		assert !meet.getDisjuncts().stream().anyMatch(l -> l.isInconsistent()) : "label not well-formed";

		assert meet.sanityCheckDontEnforceProjectToWeqVars(mPartialArrangement);

		final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> result =
				meet.projectToElements(new HashSet<>(weqVarsForThisEdge));

		assert result.assertHasOnlyWeqVarConstraints(new HashSet<>(weqVarsForThisEdge));

		assert result.sanityCheck();
		return result;
	}

	/**
	 * used for roweq-1 rule
	 *
	 * @param labelContents
	 * @param argument
	 * @param weqVarsForResolventEdge
	 * @return
	 */
	public WeakEquivalenceEdgeLabel<NODE, DISJUNCT> shiftLabelAndAddException(final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> labelContents,
			final NODE argument, final List<NODE> weqVarsForResolventEdge) {
		assert !weqVarsForResolventEdge.isEmpty() : "because the array in the resolvent must have a dimension >= 1";

		final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> meet =
				new WeakEquivalenceEdgeLabel<NODE, DISJUNCT>(this, labelContents);

		meet.meetWithCcGpa();

		meet.setExternalRemInfo(mPartialArrangement.getElementCurrentlyBeingRemoved());
		meet.projectWeqVarNode(weqVarsForResolventEdge.get(weqVarsForResolventEdge.size() - 1));

		final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> labelToShiftAndAdd =
				meet.projectToElements(new HashSet<>(weqVarsForResolventEdge));

		labelToShiftAndAdd.inOrDecreaseWeqVarIndices(1, weqVarsForResolventEdge);

		final NODE firstWeqVar = weqVarsForResolventEdge.get(0);
		assert !labelToShiftAndAdd.getAppearingNodes().contains(firstWeqVar);

		final Set<CongruenceClosure<NODE>> shiftedLabelContents =
				new HashSet<>(labelToShiftAndAdd.getDisjuncts());

		final CongruenceClosure<NODE> firstWeqVarUnequalArgument =
				mWeqCcManager.getSingleDisequalityCc(firstWeqVar, argument, true);
		shiftedLabelContents.add(firstWeqVarUnequalArgument);
		assert shiftedLabelContents.stream().allMatch(l -> l.sanityCheckOnlyCc());

		final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> normalized = mWeqCcManager
				.filterRedundantCcs(new WeakEquivalenceEdgeLabel<>(this, shiftedLabelContents));
		assert normalized.getDisjuncts().stream().allMatch(l -> l.sanityCheckOnlyCc());
		return normalized;
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
			for (final Entry<NODE, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> edge
					: getAdjacentWeqEdges(node2OldRep).entrySet()) {
				mWeakEquivalenceEdges.remove(new Doubleton<>(node2OldRep, edge.getKey()));
				putEdgeLabel(new Doubleton<>(newRep, edge.getKey()), edge.getValue());
			}
		} else {
			// node1OldRep is not representative anymore
			for (final Entry<NODE, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> edge
					: getAdjacentWeqEdges(node1OldRep).entrySet()) {
				mWeakEquivalenceEdges.remove(new Doubleton<>(node1OldRep, edge.getKey()));
				putEdgeLabel(new Doubleton<>(newRep, edge.getKey()), edge.getValue());
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
				.map(weqlabel -> weqlabel.getDisjuncts().size()).reduce(Math::max);
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
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> edgeLabel : getWeqEdgesEntrySet()) {
			edgeLabel.getValue().meetWithWeqGpa(originalPa);

			if (edgeLabel.getValue().isInconsistent()) {
				addArrayEquality(edgeLabel.getKey().getOneElement(), edgeLabel.getKey().getOtherElement());
			}
		}
		mFat = true;
		mWeqFat = true;
	}

	/**
	 * Introduced this just to make it easier to see where mWeakEquivalenceEdges is used for what.
	 * @return mWeakEquivalenceEdges.entrySet()
	 */
	private Set<Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>>> getWeqEdgesEntrySet() {
		return mWeakEquivalenceEdges.entrySet();
	}

	public void meetEdgeLabelsWithCcGpaBeforeRemove() {
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> edgeLabel
				: getWeqEdgesEntrySet()) {
			edgeLabel.getValue().meetWithCcGpa();
			if (edgeLabel.getValue().isInconsistent()) {
				addArrayEquality(edgeLabel.getKey().getOneElement(), edgeLabel.getKey().getOtherElement());
			}
		}
		mFat = true;
		mWeqFat = false;
	}

	private void addArrayEquality(final NODE oneElement, final NODE otherElement) {
		mArrayEqualities.addPair(oneElement, otherElement);
	}

	public boolean assertElementIsFullyRemoved(final NODE elem) {
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> edge
				: getWeqEdgesEntrySet()) {
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

	public ILogger getLogger() {
		return mPartialArrangement.getLogger();
	}

	public WeqCcManager<NODE> getWeqCcManager() {
		return mWeqCcManager;
	}

	public void freeze() {
		assert !hasArrayEqualities() : "report array equalities before freezing";

		// TODO: would this be a good place to trigger closure under triangle rule?

		// set the flags
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> edge : getWeqEdgesEntrySet()) {
			edge.getValue().freeze();
		}
		mIsFrozen = true;
	}

	@Override
	public String toString() {
		if (isEmpty()) {
			return "Empty";
		}
		if (mWeakEquivalenceEdges.size() < WeqSettings.MAX_NO_WEQ_EDGES_FOR_VERBOSE_TO_STRING) {
			return toLogString();
		}

		final StringBuilder sb = new StringBuilder();
		sb.append("summary:\n");
		for (final Entry<String, Integer> en : summarize().entrySet()) {
			sb.append(String.format("%s : %d\n", en.getKey(), en.getValue()));
		}
		sb.append("graph shape:\n");
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> weq :
			getWeqEdgesEntrySet()) {
			sb.append(weq.getKey());
			sb.append("\n");
		}
		return sb.toString();
	}

	public String toLogString() {
		final StringBuilder sb = new StringBuilder();

		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> weq :
			getWeqEdgesEntrySet()) {
			sb.append(weq.getKey());
			sb.append("\n");
			sb.append(weq.getValue().toLogString());
			sb.append("\n");
		}

		return sb.toString();
	}

	Map<String, Integer> summarize() {
		final Map<String, Integer> result = new HashMap<>();

		result.put("#Edges", mWeakEquivalenceEdges.size());

		final int noEdgeLabelDisjuncts = mWeakEquivalenceEdges.values().stream()
				.map(weqEdge -> weqEdge.getDisjuncts().size())
				.reduce((i1, i2) -> i1 + i2)
				.get();
		result.put("#EdgeLabelDisjuncts", noEdgeLabelDisjuncts);

		result.put("Average#EdgeLabelDisjuncts", noEdgeLabelDisjuncts == 0 ? -1 :
					mWeakEquivalenceEdges.size()/noEdgeLabelDisjuncts);

		return result;
	}

	public boolean assertLabelsAreUnfrozen() {
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> edge : getWeqEdgesEntrySet()) {
			if (!edge.getValue().assertDisjunctsAreUnfrozen()) {
				assert false;
				return false;
			}
		}
		return true;
	}

	boolean sanityCheck() {
		assert mWeqCcManager != null;

		if (mPartialArrangement != null && mPartialArrangement.isInconsistent()) {
			// we will drop this weak equivalence graph anyway
			return true;
		}

		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> en
				: getWeqEdgesEntrySet()) {
			assert en.getValue().sanityCheck();
		}

		assert sanityAllNodesOnWeqLabelsAreKnownToGpa(null);

		return sanityCheckWithoutNodesComparison();
	}

	boolean sanityCheckWithoutNodesComparison() {
		assert mWeqCcManager != null : "factory is needed for the sanity check..";

		/*
		 * check that the edges only connect compatible arrays
		 *  compatible means having the same Sort, in particular: dimensionality
		 */
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> edge : getWeqEdgesEntrySet()) {
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
			for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> edge : getWeqEdgesEntrySet()) {
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
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> edge : getWeqEdgesEntrySet()) {
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
			for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> edge : getWeqEdgesEntrySet()) {

				final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> label = edge.getValue();

				final Set<NODE> nodesOnEdgeLabelWithoutWeqNodes = label.getAppearingNodes().stream()
						.filter(node -> !CongruenceClosure.dependsOnAny(node, mWeqCcManager.getAllWeqNodes()))
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

			private final PartialOrderCache<DISJUNCT> mCcPoCache;

			public CachingWeqEdgeLabelPoComparator() {
				mCcPoCache = new PartialOrderCache<>(mWeqCcManager.getICcComparator(mEmptyDisjunct));
			}

			boolean isStrongerOrEqual(final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> label1,
					final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> label2) {
	//			return label1.isStrongerThan(label2, mCcPoCache::lowerEqual);
				return mWeqCcManager.isStrongerThan(label1, label2, mCcPoCache::lowerEqual);
			}

			WeakEquivalenceEdgeLabel<NODE, DISJUNCT> union(final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> label1,
					final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> label2) {
				return label1.union(label2, mCcPoCache);
			}
		}
}

