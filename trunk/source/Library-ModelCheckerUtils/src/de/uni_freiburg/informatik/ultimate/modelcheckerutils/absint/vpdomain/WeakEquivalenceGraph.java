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
import java.util.function.BiPredicate;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;

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
import de.uni_freiburg.informatik.ultimate.util.datastructures.ICongruenceClosureElement;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.PartialOrderCache;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * (short: weq graph)
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class WeakEquivalenceGraph<NODE extends IEqNodeIdentifier<NODE>> {

	private final CCManager<NODE> mCcManager;

	private final EqConstraintFactory<NODE> mFactory;

	private final Map<Doubleton<NODE>, WeakEquivalenceEdgeLabel> mWeakEquivalenceEdges;

	private final HashRelation<NODE, NODE> mArrayEqualities;

	/**
	 * The WeqCongruenceClosure that this weq graph is part of. This may be null, if we use this weq graph as an
	 * intermediate, for example during a join or meet operation.
	 */
	private final WeqCongruenceClosure<NODE> mPartialArrangement;

	private boolean mWeqMeetMode;

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
			final Map<Doubleton<NODE>, WeakEquivalenceEdgeLabel> weakEquivalenceEdges,
			final HashRelation<NODE, NODE> arrayEqualities,
			final EqConstraintFactory<NODE> factory) {
		mPartialArrangement = null;
		mWeakEquivalenceEdges = weakEquivalenceEdges;
		mArrayEqualities = arrayEqualities;
		assert factory != null;
		mFactory = factory;
		mCcManager = factory.getCcManager();
		assert sanityCheck();
	}

	/**
	 * Copy constructor
	 * @param weakEquivalenceGraph
	 * @param factory
	 */
	public WeakEquivalenceGraph(final WeqCongruenceClosure<NODE> pArr,
			final WeakEquivalenceGraph<NODE> weakEquivalenceGraph) {

		mPartialArrangement = pArr;

		mArrayEqualities = new HashRelation<>(weakEquivalenceGraph.mArrayEqualities);
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

	public void updateVerticesOnRemoveElement(final NODE elem, final NODE replacement) {

		final Map<Doubleton<NODE>, WeakEquivalenceEdgeLabel> edgesCopy = new HashMap<>(mWeakEquivalenceEdges);

		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel> en : edgesCopy.entrySet()) {

			final NODE source = en.getKey().getOneElement();
			final NODE target = en.getKey().getOtherElement();

			if (source.equals(elem)) {
				final WeakEquivalenceGraph<NODE>.WeakEquivalenceEdgeLabel label =
						mWeakEquivalenceEdges.remove(en.getKey());
				if (replacement != null) {
					mWeakEquivalenceEdges.put(new Doubleton<NODE>(replacement, target), label);
				}
			} else if (target.equals(elem)) {
				final WeakEquivalenceGraph<NODE>.WeakEquivalenceEdgeLabel label =
						mWeakEquivalenceEdges.remove(en.getKey());
				if (replacement != null) {
					mWeakEquivalenceEdges.put(new Doubleton<NODE>(source, replacement), label);
				}
			}
		}
	}

	public Set<NODE> projectSimpleElementInEdgeLabels(final NODE elem, final boolean useWeqGpa) {
		final Set<NODE> nodesToAdd = new HashSet<>();
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel> en : mWeakEquivalenceEdges.entrySet()) {
			assert !elem.equals(en.getKey().getOneElement());
			assert !elem.equals(en.getKey().getOtherElement());

			nodesToAdd.addAll(en.getValue().projectSingleOrSimpleElement(elem, useWeqGpa));
		}
		assert elementIsFullyRemoved(elem);
		return nodesToAdd;
	}

//	public void projectSingleElementInEdgeLabels(final NODE elem) {
//
//		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel> en : mWeakEquivalenceEdges.entrySet()) {
//
//			assert !elem.equals(en.getKey().getOneElement());
//			assert !elem.equals(en.getKey().getOtherElement());
//
//			en.getValue().projectSingleOrSimpleElement(elem, false);
//		}
//		assert elementIsFullyRemoved(elem);
//	}


//	public void projectSingleElement(final NODE elem, final NODE replacement) {
//
//		final Map<Doubleton<NODE>, WeakEquivalenceEdgeLabel> edgesCopy = new HashMap<>(mWeakEquivalenceEdges);
//
//		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel> en : edgesCopy.entrySet()) {
//
//			final NODE source = en.getKey().getOneElement();
//			final NODE target = en.getKey().getOtherElement();
//
//			if (source.equals(elem)) {
//				final WeakEquivalenceGraph<NODE>.WeakEquivalenceEdgeLabel label =
//						mWeakEquivalenceEdges.remove(en.getKey());
//				if (replacement != null) {
//					label.projectSingleElement(elem, replacement);
//					mWeakEquivalenceEdges.put(new Doubleton<NODE>(replacement, target), label);
//				}
//			} else if (target.equals(elem)) {
//				final WeakEquivalenceGraph<NODE>.WeakEquivalenceEdgeLabel label =
//						mWeakEquivalenceEdges.remove(en.getKey());
//				if (replacement != null) {
//					label.projectSingleElement(elem, replacement);
//					mWeakEquivalenceEdges.put(new Doubleton<NODE>(source, replacement), label);
//				}
//			} else {
//				en.getValue().projectSingleElement(elem, replacement);
//			}
//		}
//		assert elementIsFullyRemoved(elem);
//	}

//	public void renameVariables(final Map<Term, Term> substitutionMapping) {
//		final HashMap<Doubleton<NODE>, WeakEquivalenceEdgeLabel> weqEdgesCopy =
//				new HashMap<>(mWeakEquivalenceEdges);
//		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel> en : weqEdgesCopy.entrySet()) {
//			mWeakEquivalenceEdges.remove(en.getKey());
//
//			final Doubleton<NODE> newDton = new Doubleton<>(
//					en.getKey().getOneElement().renameVariables(substitutionMapping),
//					en.getKey().getOtherElement().renameVariables(substitutionMapping));
//			en.getValue().renameVariables(substitutionMapping);
//			mWeakEquivalenceEdges.put(newDton, en.getValue());
//		}
//		assert sanityCheck();
//	}

	public void transformElementsAndFunctions(final Function<NODE, NODE> transformer) {
		final HashMap<Doubleton<NODE>, WeakEquivalenceEdgeLabel> weqEdgesCopy =
				new HashMap<>(mWeakEquivalenceEdges);
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel> en : weqEdgesCopy.entrySet()) {
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

				final WeakEquivalenceGraph<NODE>.WeakEquivalenceEdgeLabel newEdgeLabel = thisWeqEdge.getValue()
						.meet(Collections.singletonList(this.mPartialArrangement))
						.projectToElements(mFactory.getAllWeqNodes());

				newWeakEquivalenceEdges.put(thisWeqEdge.getKey(), newEdgeLabel);
				assert correspondingWeqEdgeLabelInOther == null;
				continue;
			}

			if (correspondingWeqEdgeLabelInOther == null) {
				continue;
			}

			final WeakEquivalenceGraph<NODE>.WeakEquivalenceEdgeLabel thisNewEdgeLabel = thisWeqEdge.getValue()
						.meet(Collections.singletonList(this.mPartialArrangement))
						.projectToElements(mFactory.getAllWeqNodes());
			final WeakEquivalenceGraph<NODE>.WeakEquivalenceEdgeLabel otherNewEdgeLabel =
					correspondingWeqEdgeLabelInOther
						.meet(Collections.singletonList(other.mPartialArrangement))
						.projectToElements(mFactory.getAllWeqNodes());

			newWeakEquivalenceEdges.put(thisWeqEdge.getKey(), thisNewEdgeLabel.union(otherNewEdgeLabel));
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
				final WeakEquivalenceGraph<NODE>.WeakEquivalenceEdgeLabel newEdgeLabel = otherWeqEdge.getValue()
						.meet(Collections.singletonList(other.mPartialArrangement))
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

	Map<Doubleton<NODE>, WeakEquivalenceGraph<NODE>.WeakEquivalenceEdgeLabel> close() {
		if (mWeakEquivalenceEdges.isEmpty()) {
			return Collections.emptyMap();
		}

		final CachingWeqEdgeLabelPoComparator cwelpc = new CachingWeqEdgeLabelPoComparator();

		final FloydWarshall<NODE, WeakEquivalenceEdgeLabel> fw =
				new FloydWarshall<>(cwelpc::isStrongerOrEqual,
//				new FloydWarshall<>(WeakEquivalenceEdgeLabel::isStrongerThan,
						cwelpc::union,
//						WeakEquivalenceEdgeLabel::union,
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
		for (final Entry<Doubleton<NODE>, WeakEquivalenceGraph<NODE>.WeakEquivalenceEdgeLabel> edge
				: mWeakEquivalenceEdges.entrySet()) {
			if (!edge.getValue().isTautological()) {
				return false;
			}
		}
		return true;
	}

	public boolean isStrongerThan(final WeakEquivalenceGraph<NODE> other) {
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
		assert paList.stream().allMatch(l -> l.assertHasOnlyWeqVarConstraints(mFactory.getAllWeqNodes()));
		assert paList.size() != 1 || !paList.get(0).isTautological() : "catch this case before?";
		assert sanityCheck();

		final WeakEquivalenceEdgeLabel oldLabel = mWeakEquivalenceEdges.get(sourceAndTarget);

		if (paList.isEmpty()) {
			mWeakEquivalenceEdges.put(sourceAndTarget, new WeakEquivalenceEdgeLabel(paList));
			mArrayEqualities.addPair(sourceAndTarget.getOneElement(), sourceAndTarget.getOtherElement());
			return oldLabel == null || !oldLabel.isInconsistent();
		}

		if (oldLabel == null || oldLabel.isTautological()) {
			assert paList.size() != 1 || !paList.get(0).isTautological();

			final WeakEquivalenceGraph<NODE>.WeakEquivalenceEdgeLabel newLabel = new WeakEquivalenceEdgeLabel(paList);
			newLabel.meetWithCcGpa();
			final WeakEquivalenceGraph<NODE>.WeakEquivalenceEdgeLabel newLabelMeetProject =
					newLabel.projectToElements(mFactory.getAllWeqNodes());
			mWeakEquivalenceEdges.put(sourceAndTarget, newLabelMeetProject);

			assert sanityCheck();
			return true;
		}

		final WeakEquivalenceEdgeLabel oldLabelCopy = new WeakEquivalenceEdgeLabel(oldLabel);

		final WeakEquivalenceEdgeLabel labelToStrengthenWith = new WeakEquivalenceEdgeLabel(paList);
		assert labelToStrengthenWith.sanityCheck() : "input label not normalized??";

		labelToStrengthenWith.meetWithCcGpa();
		oldLabelCopy.meetWithCcGpa();
		if (oldLabelCopy.isStrongerThan(labelToStrengthenWith)) {
			// nothing to do
			return false;
		}

		WeakEquivalenceEdgeLabel strengthenedEdgeLabel = oldLabelCopy.meet(labelToStrengthenWith);

		// meet with gpa (done before) and project afterwards
		strengthenedEdgeLabel = strengthenedEdgeLabel.projectToElements(mFactory.getAllWeqNodes());

		// inconsistency check
		if (strengthenedEdgeLabel.isInconsistent()) {
			mArrayEqualities.addPair(sourceAndTarget.getOneElement(), sourceAndTarget.getOtherElement());
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
			final WeakEquivalenceGraph<NODE>.WeakEquivalenceEdgeLabel value) {
		assert mPartialArrangement.isRepresentative(sourceAndTarget.getOneElement())
			&& mPartialArrangement.isRepresentative(sourceAndTarget.getOtherElement());
		assert sourceAndTarget.getOneElement().getTerm().getSort().equals(sourceAndTarget.getOtherElement().getTerm().getSort());

		final boolean result = strengthenEdgeLabel(sourceAndTarget, value.getLabelContents());
		assert sanityCheck();
		return result;
	}

	public boolean reportWeakEquivalence(final NODE array1, final NODE array2,
			final List<CongruenceClosure<NODE>> edgeLabelContents) {
		assert mPartialArrangement.isRepresentative(array1) && mPartialArrangement.isRepresentative(array2);
		if (edgeLabelContents.size() == 1 && edgeLabelContents.get(0).isTautological()) {
			return false;
		}

		final boolean result = reportWeakEquivalence(new Doubleton<NODE>(array1, array2),
				new WeakEquivalenceEdgeLabel(edgeLabelContents));
		assert sanityCheck();
		return result;
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
		final WeakEquivalenceGraph<NODE>.WeakEquivalenceEdgeLabel edge =
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

		final WeakEquivalenceGraph<NODE>.WeakEquivalenceEdgeLabel originalEdgeLabel =
				new WeakEquivalenceEdgeLabel(labelContents);

		final NODE firstDimWeqVarNode = weqVarsForThisEdge.get(0);

		final CongruenceClosure<NODE> qEqualsI = new CongruenceClosure<>();

		qEqualsI.reportEquality(firstDimWeqVarNode, value);

		final WeakEquivalenceGraph<NODE>.WeakEquivalenceEdgeLabel copy =
				new WeakEquivalenceEdgeLabel(originalEdgeLabel);

//		copy.meetWithWeqGpa();
		copy.meetWithCcGpa();

		final WeakEquivalenceGraph<NODE>.WeakEquivalenceEdgeLabel meet =
				copy.meetRec(Collections.singletonList(qEqualsI));

		meet.setExternalRemInfo(mPartialArrangement.getElementCurrentlyBeingRemoved());
		meet.projectWeqVarNode(firstDimWeqVarNode);

		meet.inOrDecreaseWeqVarIndices(-1, weqVarsForThisEdge);
		assert !meet.getAppearingNodes().contains(weqVarsForThisEdge.get(weqVarsForThisEdge.size() - 1)) : "double "
				+ "check the condition if this assertion fails, but as we decreased all weq vars, the last one should "
				+ "not be present in the result, right?..";
		assert !meet.mLabel.stream().anyMatch(l -> l.isInconsistent()) : "label not well-formed";

		assert meet.sanityCheckDontEnforceProjectToWeqVars(mPartialArrangement);

		final WeakEquivalenceGraph<NODE>.WeakEquivalenceEdgeLabel result =
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
	public List<CongruenceClosure<NODE>> shiftLabelAndAddException(
			final List<CongruenceClosure<NODE>> labelContents, final NODE argument,
			final List<NODE> weqVarsForResolventEdge) {
		assert !weqVarsForResolventEdge.isEmpty() : "because the array in the resolvent must have a dimension >= 1";

		final WeakEquivalenceGraph<NODE>.WeakEquivalenceEdgeLabel meet =
				new WeakEquivalenceEdgeLabel(labelContents);

//		meet.meetWithWeqGpa();
		meet.meetWithCcGpa();

		meet.setExternalRemInfo(mPartialArrangement.getElementCurrentlyBeingRemoved());
		meet.projectWeqVarNode(weqVarsForResolventEdge.get(weqVarsForResolventEdge.size() - 1));

		final WeakEquivalenceGraph<NODE>.WeakEquivalenceEdgeLabel labelToShiftAndAdd =
				meet.projectToElements(new HashSet<>(weqVarsForResolventEdge));

		labelToShiftAndAdd.inOrDecreaseWeqVarIndices(1, weqVarsForResolventEdge);

		final NODE firstWeqVar = weqVarsForResolventEdge.get(0);
		assert !labelToShiftAndAdd.getAppearingNodes().contains(firstWeqVar);

		final List<CongruenceClosure<NODE>> shiftedLabelContents =
				new ArrayList<>(labelToShiftAndAdd.getLabelContents());

		final CongruenceClosure<NODE> firstWeqVarUnequalArgument = new CongruenceClosure<>();
		firstWeqVarUnequalArgument.reportDisequality(firstWeqVar, argument);
		shiftedLabelContents.add(firstWeqVarUnequalArgument);
		assert shiftedLabelContents.stream().allMatch(l -> l.sanityCheckOnlyCc());

		final List<CongruenceClosure<NODE>> normalized = mCcManager.filterRedundantCcs(new HashSet<>(shiftedLabelContents));

		assert normalized.stream().allMatch(l -> l.sanityCheckOnlyCc());
		return normalized;
	}

	boolean sanityCheck() {
//		if (mPartialArrangement.mMeetWithGpaCase) {
//			// TODO sharpen sanity check for this case
//			return true;
//		}

		for (final Entry<Doubleton<NODE>, WeakEquivalenceGraph<NODE>.WeakEquivalenceEdgeLabel> en
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

	/**
	 * check that no weak equivalence edge contains a NODE that is not known to mPartialArrangement
	 * or is one of the special quantified variables from getVariableForDimension(..).
	 * @param nodesScheduledForAdding
	 */
	protected boolean sanityAllNodesOnWeqLabelsAreKnownToGpa(final Set<NODE> nodesScheduledForAdding) {
		if (mPartialArrangement != null) {
			for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel> edge : mWeakEquivalenceEdges.entrySet()) {

				final WeakEquivalenceGraph<NODE>.WeakEquivalenceEdgeLabel label = edge.getValue();

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
			for (final Entry<NODE, WeakEquivalenceGraph<NODE>.WeakEquivalenceEdgeLabel> edge
					: getAdjacentWeqEdges(node2OldRep).entrySet()) {
				mWeakEquivalenceEdges.remove(new Doubleton<>(node2OldRep, edge.getKey()));
				mWeakEquivalenceEdges.put(new Doubleton<>(newRep, edge.getKey()), edge.getValue());
			}
		} else {
			// node1OldRep is not representative anymore
			for (final Entry<NODE, WeakEquivalenceGraph<NODE>.WeakEquivalenceEdgeLabel> edge
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
		for (final WeakEquivalenceGraph<NODE>.WeakEquivalenceEdgeLabel edgeLabel : mWeakEquivalenceEdges.values()) {
			edgeLabel.meetWithWeqGpa(originalPa);
		}
		mWeqMeetMode = true;
	}

	public void meetEdgeLabelsWithCcGpaBeforeRemove() {
		for (final WeakEquivalenceGraph<NODE>.WeakEquivalenceEdgeLabel edgeLabel : mWeakEquivalenceEdges.values()) {
			edgeLabel.meetWithCcGpa();
		}
		mWeqMeetMode = false;
	}

	public boolean elementIsFullyRemoved(final NODE elem) {
		for (final Entry<Doubleton<NODE>, WeakEquivalenceGraph<NODE>.WeakEquivalenceEdgeLabel> edge
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
		for (final Entry<Doubleton<NODE>, WeakEquivalenceGraph<NODE>.WeakEquivalenceEdgeLabel> weq :
			mWeakEquivalenceEdges.entrySet()) {
			sb.append(weq.getKey());
			sb.append("\n");
		}
		return sb.toString();
	}

	public String toLogString() {
		final StringBuilder sb = new StringBuilder();

		for (final Entry<Doubleton<NODE>, WeakEquivalenceGraph<NODE>.WeakEquivalenceEdgeLabel> weq :
			mWeakEquivalenceEdges.entrySet()) {
			sb.append(weq.getKey());
			sb.append("\n");
			sb.append(weq.getValue().toLogString());
			sb.append("\n");
		}

		return sb.toString();
	}

	class CachingWeqEdgeLabelPoComparator {

		private final PartialOrderCache<CongruenceClosure<NODE>> mCcPoCache;

		public CachingWeqEdgeLabelPoComparator() {
			mCcPoCache = new PartialOrderCache<>(mCcManager.getCcComparator());
		}

		boolean isStrongerOrEqual(final WeakEquivalenceEdgeLabel label1,
				final WeakEquivalenceEdgeLabel label2) {
			return label1.isStrongerThan(label2, mCcPoCache::lowerEqual);
		}

		WeakEquivalenceEdgeLabel union(final WeakEquivalenceEdgeLabel label1, final WeakEquivalenceEdgeLabel label2) {
			return label1.union(label2, mCcPoCache);
		}

	}

//	class WeqEdgeLabelComparator implements IPartialComparator<WeakEquivalenceEdgeLabel> {
//
//		@Override
//		public ComparisonResult compare(final WeakEquivalenceGraph<NODE>.WeakEquivalenceEdgeLabel o1,
//				final WeakEquivalenceGraph<NODE>.WeakEquivalenceEdgeLabel o2) {
//			assert asser
//			// TODO Auto-generated method stub
//			return null;
//		}
//	}

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

		public void setExternalRemInfo(final CongruenceClosure<NODE>.RemoveElement remInfo) {
			for (final CongruenceClosure<NODE> lab : mLabel) {
				lab.setExternalRemInfo(remInfo);
			}
		}

		public boolean hasExternalRemInfo() {
			for (final CongruenceClosure<NODE> l : mLabel) {
				assert l.assertHasExternalRemInfo();
			}
			return true;
		}

		public boolean assertHasOnlyWeqVarConstraints(final Set<NODE> weqVarsForThisEdge) {
			for (final CongruenceClosure<NODE> l : mLabel) {
				if (!l.assertHasOnlyWeqVarConstraints(weqVarsForThisEdge)) {
					assert false;
					return false;
				}
			}
			return true;
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

		/**
		 * Constructs an empty edge. (labeled "true")
		 */
		public WeakEquivalenceEdgeLabel() {
			mLabel = new ArrayList<>();
			mLabel.add(new CongruenceClosure<>());
			assert sanityCheck();
		}

		public void projectWeqVarNode(final NODE firstDimWeqVarNode) {
			for (final CongruenceClosure<NODE> lab : mLabel) {
				lab.removeSimpleElementDontIntroduceNewNodes(firstDimWeqVarNode);
			}
			assert sanityCheckDontEnforceProjectToWeqVars(mPartialArrangement);
		}

//		public void projectSingleElement(final NODE elem, final NODE replacement) {
//		public void projectSingleOrSimpleElement(final NODE elem, final boolean simpleNotSingle) {
		public Set<NODE> projectSingleOrSimpleElement(final NODE elem, final boolean simpleNotSingle) {
			if (isTautological()) {
				return Collections.emptySet();
//				return;
			}
			if (isInconsistent()) {
				return Collections.emptySet();
//				return;
			}

			final Set<NODE> nodesToAddToGpa = new HashSet<>();
//			assert mLabel.stream().allMatch(l -> (l instanceof WeqCongruenceClosure<?>)) : "the meetWeqGpa method"
//					+ "should ensure this, right?";

			final List<CongruenceClosure<NODE>> newLabelContents = new ArrayList<>(mLabel.size());
			for (final CongruenceClosure<NODE> lab : mLabel) {
				assert lab.sanityCheckOnlyCc(mPartialArrangement.getElementCurrentlyBeingRemoved());

				/*
				 * just removing elem is not enough
				 * example:
				 *  elem = a
				 *  label has a[q]
				 *  then a[q] needs to be removed, but mPartialArrangement cannot know that..
				 *
				 *  actually, even removeSimpleElement is not enough, because we might be removing
				 *   a[i], a (in that order)
				 *   then during removing a[i] we add a node a[q], but dont insert a, because it is in remInfo
				 *   then when we remove a, the removeSimpleElement will just say the cc does not have a and do
				 *   nothing
				 *
				 *  plan: compute all dependents, and remove them one by one
				 */
				if (simpleNotSingle) {
					final Set<NODE> nodesAdded = lab.removeSimpleElementDontUseWeqGpa(elem);
					nodesAdded.stream()
						.filter(n -> !CongruenceClosure.dependsOnAny(n, mFactory.getAllWeqPrimedNodes()))
						.forEach(nodesToAddToGpa::add);
//					nodesToAddToGpa.addAll(lab.removeSimpleElementDontUseWeqGpa(elem));
				} else {
					// "single" case
					final Set<NODE> dependents = lab.getAllElements().stream()
							.filter(e -> CongruenceClosure.dependsOnAny(e, Collections.singleton(elem)))
							.collect(Collectors.toSet());
					lab.removeElementAndDependents(elem, dependents, Collections.emptyMap(), false);
				}
//					final Set<NODE> dependents = lab.getAllElements().stream()
//							.filter(e -> CongruenceClosure.dependsOnAny(e, Collections.singleton(elem)))
//							.collect(Collectors.toSet());
//					for (final NODE dep : dependents) {
//						lab.removeSingleElement(dep, null);
//					}


				assert lab.assertSingleElementIsFullyRemoved(elem);

				if (lab.isTautological()) {
					// a disjunct became "true" through projection --> the whole disjunction is tautological
					mLabel.clear();
					mLabel.add(new CongruenceClosure<>());
					return Collections.emptySet();
				}
				assert lab.sanityCheckOnlyCc(mPartialArrangement.getElementCurrentlyBeingRemoved());

				final CongruenceClosure<NODE> lab2;
				if (simpleNotSingle) {
					// unprime weqvars
					lab2 = new CongruenceClosure<>(lab);
//					lab2 = lab;
					lab2.transformElementsAndFunctions(node -> node.renameVariables(mFactory.getWeqPrimedVarsToWeqVars()));
				} else {
					lab2 = lab;
				}

				final CongruenceClosure<NODE> newLab = lab2.projectToElements(mFactory.getAllWeqNodes(),
						mPartialArrangement.getElementCurrentlyBeingRemoved());
				assert newLab.assertSingleElementIsFullyRemoved(elem);
				assert !newLab.isTautological();
				assert newLab.sanityCheckOnlyCc(mPartialArrangement.getElementCurrentlyBeingRemoved());
				newLabelContents.add(newLab);
			}
			mLabel.clear();
			mLabel.addAll(newLabelContents);
			assert mLabel.stream().allMatch(l -> l.assertSingleElementIsFullyRemoved(elem));
			assert sanityCheck();
			return nodesToAddToGpa;
		}

		public WeakEquivalenceEdgeLabel projectToElements(final Set<NODE> allWeqNodes) {
			if (isInconsistent()) {
				return this;
			}
			final List<CongruenceClosure<NODE>> newLabelContents = new ArrayList<>();
			for (final CongruenceClosure<NODE> item : mLabel) {
				newLabelContents.add(item.projectToElements(allWeqNodes,
						mPartialArrangement.getElementCurrentlyBeingRemoved()));
			}
			assert newLabelContents.stream().allMatch(l -> l.sanityCheckOnlyCc());
			final WeakEquivalenceGraph<NODE>.WeakEquivalenceEdgeLabel result =
					new WeakEquivalenceEdgeLabel(newLabelContents);
			assert result.sanityCheck();
			return result;
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
//							this.renameVariables(substitutionMapping);
							this.transformElements(e -> e.renameVariables(substitutionMapping));
							assert sanityCheckDontEnforceProjectToWeqVars(mPartialArrangement);
		}

		public boolean isConstrained(final NODE elem) {
			return mLabel.stream().anyMatch(l -> l.isConstrained(elem));
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
			assert this.sanityCheck();


			final List<CongruenceClosure<NODE>> newLabel = new ArrayList<>();

			for (int i = 0; i < getLabelContents().size(); i++) {
				assert mPartialArrangement.sanityCheck();
				assert getLabelContents().get(i).sanityCheckOnlyCc();
				final CongruenceClosure<NODE> currentPaWgpa = mCcManager.getMeet(getLabelContents().get(i),
						mPartialArrangement, mPartialArrangement.getElementCurrentlyBeingRemoved());

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
				newLabel.add(currentPaWgpa.projectToElements(mFactory.getAllWeqNodes(),
						mPartialArrangement.getElementCurrentlyBeingRemoved()));

				assert WeakEquivalenceGraph.this.sanityCheck();
			}
			assert newLabel.stream().allMatch(l -> l.sanityCheckOnlyCc());
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

		public void transformElements(final Function<NODE, NODE> transformer) {
			assert sanityCheckDontEnforceProjectToWeqVars(mPartialArrangement);
			for (int i = 0; i < getLabelContents().size(); i++) {
				getLabelContents().get(i).transformElementsAndFunctions(transformer);
				assert sanityCheckDontEnforceProjectToWeqVars(mPartialArrangement);
			}
			assert sanityCheckDontEnforceProjectToWeqVars(mPartialArrangement);
		}

//		public void renameVariables(final Map<Term, Term> substitutionMapping) {
//			for (int i = 0; i < getLabelContents().size(); i++) {
//				getLabelContents().get(i).transformElementsAndFunctions(node -> node.renameVariables(substitutionMapping));
//			}
//			assert sanityCheckDontEnforceProjectToWeqVars(mPartialArrangement);
//		}

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
			assert sanityCheckDontEnforceProjectToWeqVars(mPartialArrangement);
			return meetRec(paList);
		}

		private WeakEquivalenceEdgeLabel meetRec(final List<CongruenceClosure<NODE>> paList) {
			final List<CongruenceClosure<NODE>> newLabelContent = new ArrayList<>();
			for (final CongruenceClosure<NODE> lc1 : mLabel) {
				for (final CongruenceClosure<NODE> lc2 : paList) {
					newLabelContent.add(lc1.meetRec(lc2));
				}
			}

			final List<CongruenceClosure<NODE>> newLabel = mCcManager.filterRedundantCcs(new HashSet<>(newLabelContent));
			assert newLabel.stream().allMatch(l -> l.sanityCheckOnlyCc());

			final List<CongruenceClosure<NODE>> newLabelProjected = newLabel.stream()
					.map(l -> l.projectToElements(mFactory.getAllWeqNodes(),
							mPartialArrangement.getElementCurrentlyBeingRemoved())).collect(Collectors.toList());
			assert newLabelProjected.stream()
			.allMatch(l -> l.sanityCheckOnlyCc(mPartialArrangement.getElementCurrentlyBeingRemoved()));

			final WeakEquivalenceEdgeLabel result =
					new WeakEquivalenceEdgeLabel(newLabelProjected);
			assert result.sanityCheck();
			return result;
		}

		/**
		 * rule:  A isStrongerThan B
		 *     iff
		 *   forall ai exists bi. ai subseteq bi
		 * @param ccPoCache
		 * @param value
		 * @return
		 */
		public boolean isStrongerThan(final WeakEquivalenceEdgeLabel other) {
			return isStrongerThan(other, CongruenceClosure::isStrongerThan);
		}

		public boolean isStrongerThan(final WeakEquivalenceEdgeLabel other,
				final BiPredicate<CongruenceClosure<NODE>, CongruenceClosure<NODE>> lowerOrEqual) {
//				final PartialOrderCache<CongruenceClosure<NODE>> ccPoCache) {
			for (final CongruenceClosure<NODE> paThis : getLabelContents()) {
				boolean existsWeaker = false;
				for (final CongruenceClosure<NODE> paOther : other.getLabelContents()) {
//					if (paThis.isStrongerThan(paOther)) {
//					if (ccPoCache.lowerEqual(paThis, paOther)) {
					if (lowerOrEqual.test(paThis, paOther)) {
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
		 * @param ccPoCache
		 * @param correspondingWeqEdgeInOther
		 * @return
		 */
		public WeakEquivalenceEdgeLabel union(final WeakEquivalenceEdgeLabel other) {
				return this.union(other, null);
		}

		public WeakEquivalenceEdgeLabel union(final WeakEquivalenceEdgeLabel other,
				final PartialOrderCache<CongruenceClosure<NODE>> ccPoCache) {
			assert this.sanityCheck() && other.sanityCheck();
			//			assert this.mLabel.size() < 10 && other.mLabel.size() < 10;
			final List<CongruenceClosure<NODE>> unionList = new ArrayList<>(
					mLabel.size() + other.getLabelContents().size());
			unionList.addAll(mLabel);
			unionList.addAll(other.getLabelContents());

			final List<CongruenceClosure<NODE>> filtered = ccPoCache == null ?
					mCcManager.filterRedundantCcs(new HashSet<>(unionList))
						: mCcManager.filterRedundantCcs(new HashSet<>(unionList), ccPoCache);

			final WeakEquivalenceGraph<NODE>.WeakEquivalenceEdgeLabel result = new WeakEquivalenceEdgeLabel(filtered);
			assert result.sanityCheck();
			return result;
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
			if (mLabel.size() < 3) {
				return toLogString();
			}
			return "weq edge label, size: " + mLabel.size();
		}

		public String toLogString() {
			final StringBuilder sb = new StringBuilder();

			mLabel.forEach(l -> sb.append(l.toLogString() + "\n"));
			return sb.toString();
		}

		private boolean sanityCheck() {
			return sanityCheck(mPartialArrangement);
		}

		private boolean sanityCheck(final WeqCongruenceClosure<NODE> groundPartialArrangement) {
			if (mFactory == null) {
				return true;
			}
			if (isEmpty()) {
				return true;
			}

			if (mLabel.stream().anyMatch(l -> l.isTautological()) && mLabel.size() > 1) {
				// not normalized
				assert false;
				return false;
			}

			if (mLabel.stream().anyMatch(l -> l.isInconsistent())) {
				// not normalized
				assert false;
				return false;
			}

			// check that labels are free of weqPrimed vars
			if (!groundPartialArrangement.mMeetWithGpaCase) {
				for (final CongruenceClosure<NODE> lab : mLabel) {
					for (final NODE el : lab.getAllElements()) {
						if (CongruenceClosure.dependsOnAny(el, mFactory.getAllWeqPrimedNodes())) {
							assert false;
							return false;
						}
					}
				}
			}

			// check that labels are free of constraints that don't contain weq nodes
			for (final CongruenceClosure<NODE> lab : mLabel) {
//				if (groundPartialArrangement.mMeetWithGpaCase) {
//					// don't check in this case, as edges may have been "metWithWeqGpa" already..
////					assert lab.assertHasOnlyWeqVarConstraints(mFactory.getAllWeqPrimedAndUnprimedNodes());
//				} else {
					assert lab.assertHasOnlyWeqVarConstraints(mFactory.getAllWeqNodes());
//				}
			}

			return sanityCheckDontEnforceProjectToWeqVars(mPartialArrangement);
		}

		public void meetWithWeqGpa(final WeqCongruenceClosure<NODE> originalPa) {
			// prime the weq vars
//			this.renameVariables(mFactory.getWeqVarsToWeqPrimedVars());

			final List<CongruenceClosure<NODE>> newLabelContents = new ArrayList<>();
			for (final CongruenceClosure<NODE> l : mLabel) {
				final WeqCongruenceClosure<NODE> paCopy = new WeqCongruenceClosure<>(originalPa, true);

				final CongruenceClosure<NODE> lCopy = new CongruenceClosure<>(l);
				// prime the weq vars
//				lCopy.transformElementsAndFunctions(n -> n.renameVariables(mFactory.getWeqVarsToWeqPrimedVars()));
				lCopy.transformElementsAndFunctions(n -> n.renameVariables(mFactory.getWeqVarsToWeqPrimedVars()));

				for (final Entry<NODE, NODE> eq : lCopy.getSupportingElementEqualities().entrySet()) {
					if (paCopy.isInconsistent()) {
						mLabel.clear();
						return;
					}
					paCopy.reportEquality(eq.getKey(), eq.getValue());
				}
				for (final Entry<NODE, NODE> deq : lCopy.getElementDisequalities().entrySet()) {
					if (paCopy.isInconsistent()) {
						mLabel.clear();
						return;
					}
					paCopy.reportDisequality(deq.getKey(), deq.getValue());
				}

				if (paCopy.isTautological()) {
						mLabel.clear();
						mLabel.add(new CongruenceClosure<NODE>());
						return;
				}
				newLabelContents.add(paCopy);
			}

			mLabel.clear();
			mLabel.addAll(newLabelContents);

			assert sanityCheckDontEnforceProjectToWeqVars(mPartialArrangement);

		}

		public void meetWithCcGpa() {
			meetWithGpa(false);
		}

		public void meetWithGpa(final boolean meetWithFullWeqCc) {

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
				final CongruenceClosure<NODE> meet;
				if (meetWithFullWeqCc) {
					meet = mCcManager.getWeqMeet(mLabel.get(i), mPartialArrangement);
				} else {
					meet = mCcManager.getMeet(mLabel.get(i), mPartialArrangement, mPartialArrangement.getElementCurrentlyBeingRemoved());
				}

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
				newLabelContents.add(meet);
			}
			assert newLabelContents.size() <= 1 || !newLabelContents.stream().anyMatch(c -> c.isTautological());


			mLabel.clear();
			mLabel.addAll(newLabelContents);

			assert sanityCheckDontEnforceProjectToWeqVars(mPartialArrangement);
		}

		private boolean sanityCheckDontEnforceProjectToWeqVars(final CongruenceClosure<NODE> groundPartialArrangement) {
			for (final CongruenceClosure<NODE> lab : mLabel) {
				if (!lab.sanityCheckOnlyCc(groundPartialArrangement.getElementCurrentlyBeingRemoved())) {
					assert false;
					return false;
				}
			}

			// check label normalization
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

		public boolean assertElementIsFullyRemoved(final NODE elem) {
			for (final CongruenceClosure<NODE> lab : mLabel) {
				if (!lab.assertSingleElementIsFullyRemoved(elem)) {
					assert false;
					return false;
				}
			}
			return true;
		}
	}
}

