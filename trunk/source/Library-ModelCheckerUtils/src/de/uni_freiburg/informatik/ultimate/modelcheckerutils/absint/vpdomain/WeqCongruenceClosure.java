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
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.vpdomain.WeakEquivalenceGraph.WeqSettings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.CongruenceClosure;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.EqualityStatus;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class WeqCongruenceClosure<NODE extends IEqNodeIdentifier<NODE>>
		extends CongruenceClosure<NODE> {

	private final WeakEquivalenceGraph<NODE> mWeakEquivalenceGraph;
	private final EqConstraintFactory<NODE> mFactory;

	public final boolean mMeetWithGpaCase;

	/**
	 * Create an empty ("True"/unconstrained) WeqCC.
	 *
	 * @param factory
	 */
	public WeqCongruenceClosure(final EqConstraintFactory<NODE> factory) {
		super();
		assert factory != null;
		mWeakEquivalenceGraph = new WeakEquivalenceGraph<>(this, factory);
		mFactory = factory;
		mMeetWithGpaCase = false;
		assert sanityCheck();
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
		mMeetWithGpaCase = false;
	}

	/**
	 * Create a WeqCC using the given CongruenceClosure as ground partial
	 * arrangement (gpa) and an empty WeakEquivalenceGraph.
	 *
	 * @param original
	 * @param factory
	 */
	public WeqCongruenceClosure(final CongruenceClosure<NODE> original,
			final EqConstraintFactory<NODE> factory) {
		super(original);
		assert factory != null;
		mWeakEquivalenceGraph = new WeakEquivalenceGraph<>(this, factory);
		mFactory = factory;
		mMeetWithGpaCase = false;
		assert sanityCheck();
	}

	/**
	 * Create a WeqCC using the given CongruenceClosure as ground partial
	 * arrangement (gpa) and the given WeakEquivalenceGraph.
	 *
	 * @param original
	 */
	public WeqCongruenceClosure(final CongruenceClosure<NODE> original,
			final WeakEquivalenceGraph<NODE> weqGraph, final EqConstraintFactory<NODE> factory) {
		super(original);
		assert factory != null;
		if (original.isInconsistent()) {
			throw new IllegalArgumentException("use other constructor!");
		}
		mFactory = factory;

		mMeetWithGpaCase = false;

		// we need a fresh instance of WeakEquivalenceGraph here, because we cannot set the link in the weq
		// graph to the right cc instance..
		mWeakEquivalenceGraph = new WeakEquivalenceGraph<>(this, weqGraph, false);

		assert sanityCheck();
	}

	public WeqCongruenceClosure(final WeqCongruenceClosure<NODE> original, final boolean meetWGpaCase) {
		super(original);
		assert original.mFactory != null;
		mMeetWithGpaCase = meetWGpaCase;
		mFactory = original.mFactory;
		mWeakEquivalenceGraph = new WeakEquivalenceGraph<>(this, original.mWeakEquivalenceGraph,
//				false);
				meetWGpaCase && WeqSettings.FLATTEN_WEQ_EDGES_BEFORE_JOIN); //TODO simplify
		assert sanityCheck();
	}

//	/**
//	 * copy constructor
//	 *
//	 * @param original
//	 */
//	public WeqCongruenceClosure(final WeqCongruenceClosure<NODE> original) {
//		this(original, false);
//	}

	public Term getTerm(final Script script) {
		final List<Term> allConjuncts = new ArrayList<>();
		allConjuncts.addAll(EqConstraint.partialArrangementToCube(script, this));

		final List<Term> weakEqConstraints = mWeakEquivalenceGraph.getWeakEquivalenceConstraintsAsTerms(script);
		allConjuncts.addAll(weakEqConstraints);

		final Term result = SmtUtils.and(script, allConjuncts.toArray(new Term[allConjuncts.size()]));
		return result;
	}

	@Override
	public void addElement(final NODE elem) {
		assert !isFrozen();
//		final boolean result = super.addElementRec(elem);
		super.addElementRec(elem);

		executeFloydWarshallAndReportResultToWeqCc();
		reportAllArrayEqualitiesFromWeqGraph();

		assert sanityCheck();
//		return result;
	}

	private WeqCongruenceClosure<NODE> alignElementsAndFunctionsWeqRec(final CongruenceClosure<NODE> otherCC,
			final RemoveElement remInfo) {
		assert !isFrozen();
		assert !this.isInconsistent() && !otherCC.isInconsistent();
		assert remInfo == null;

//		final WeqCongruenceClosure<NODE> result = new WeqCongruenceClosure<>(this);
		final WeqCongruenceClosure<NODE> result = mFactory.getCcManager().makeCopy(this);
		assert result.sanityCheck();

		for (final NODE e : otherCC.getAllElements()) {
			result.addElementRec(e);
		}

		assert result.sanityCheck();
		return result;
	}

	public void reportWeakEquivalence(final NODE array1, final NODE array2, final NODE storeIndex) {
		assert !isFrozen();
		assert array1.hasSameTypeAs(array2);

		getRepresentativeAndAddElementIfNeeded(storeIndex);
		assert sanityCheck();

		final CongruenceClosure<NODE> newConstraint = computeWeqConstraintForIndex(
				Collections.singletonList(storeIndex));
		reportWeakEquivalence(array1, array2, Collections.singleton(newConstraint));
		assert sanityCheck();
	}

	public void reportWeakEquivalence(final NODE array1, final NODE array2,
			final Set<CongruenceClosure<NODE>> edgeLabel) {
		assert !isFrozen();
		if (isInconsistent()) {
			return;
		}

		while (true) {
			boolean madeChanges = false;
			madeChanges |= reportWeakEquivalenceDoOnlyRoweqPropagations(array1, array2, edgeLabel);
			if (!madeChanges) {
				break;
			}

			madeChanges = false;
			madeChanges |= executeFloydWarshallAndReportResultToWeqCc();
			if (!madeChanges) {
				break;
			}
		}
		assert sanityCheck();

		/*
		 * ext propagations
		 */
		reportAllArrayEqualitiesFromWeqGraph();
		assert sanityCheck();
	}

	boolean executeFloydWarshallAndReportResultToWeqCc() {
		if (isInconsistent()) {
			return false;
		}
		boolean fwmc = false;
		final Map<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE>> fwResult = mWeakEquivalenceGraph
				.close();
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE>> fwEdge : fwResult
				.entrySet()) {
			fwmc |= reportWeakEquivalenceDoOnlyRoweqPropagations(fwEdge.getKey().getOneElement(),
					fwEdge.getKey().getOtherElement(), fwEdge.getValue().getLabelContents());
			assert sanityCheck();
		}
		assert sanityCheck();
		return fwmc;
	}

	private boolean reportWeakEquivalenceDoOnlyRoweqPropagations(final NODE array1, final NODE array2,
			final Set<CongruenceClosure<NODE>> edgeLabel) {
		assert edgeLabel.stream().allMatch(l -> l.assertHasOnlyWeqVarConstraints(mFactory.getAllWeqNodes()));
		if (isInconsistent()) {
			return false;
		}
		if (isLabelTautological(edgeLabel)) {
			return false;
		}

		boolean madeChanges = false;
		madeChanges |= addElementRec(array1);
		madeChanges |= addElementRec(array2);

		final NODE array1Rep = mElementTVER.getRepresentative(array1);
		final NODE array2Rep = mElementTVER.getRepresentative(array2);

		if (array1Rep == array2Rep) {
			// no need to have a weq edge from the node to itself
			return madeChanges;
		}

		madeChanges |= mWeakEquivalenceGraph.reportWeakEquivalence(array1Rep, array2Rep, edgeLabel);

		if (!madeChanges) {
			// nothing to propagate
			return false;
		}

		Set<CongruenceClosure<NODE>> strengthenedEdgeLabelContents = mWeakEquivalenceGraph
				.getEdgeLabelContents(array1Rep, array2Rep);

		if (strengthenedEdgeLabelContents == null) {
			// edge became "false";
			strengthenedEdgeLabelContents = Collections.emptySet();
		}

		/*
		 * roweq propagations
		 *
		 * look for fitting c[i], d[j] with i ~ j, array1 ~ c, array2 ~ d
		 */
		final Collection<NODE> ccps1 = mAuxData.getAfCcPars(array1Rep);
		final Collection<NODE> ccps2 = mAuxData.getAfCcPars(array2Rep);
		for (final NODE ccp1 : ccps1) {
			if (!hasElements(ccp1, ccp1.getArgument(), ccp1.getAppliedFunction())) {
				continue;
			}
			for (final NODE ccp2 : ccps2) {
				if (isInconsistent()) {
					return true;
				}

				if (!hasElements(ccp2, ccp2.getArgument(), ccp2.getAppliedFunction())) {
					continue;
				}

				if (getEqualityStatus(ccp1.getArgument(), ccp2.getArgument()) != EqualityStatus.EQUAL) {
					continue;
				}
				/*
				 * i ~ j holds propagate array1[i] -- -- array2[j] (note that this adds the
				 * arrayX[Y] nodes, possibly -- EDIT: not..)
				 */

				final Set<CongruenceClosure<NODE>> projectedLabel = mWeakEquivalenceGraph.projectEdgeLabelToPoint(
						strengthenedEdgeLabelContents, ccp1.getArgument(),
						mFactory.getAllWeqVarsNodeForFunction(array1));

				// recursive call
				reportWeakEquivalenceDoOnlyRoweqPropagations(ccp1, ccp2, projectedLabel);
			}
		}

		/*
		 * roweq-1 propagations
		 */
		for (final Entry<NODE, NODE> ccc1 : mAuxData.getCcChildren(array1Rep).entrySet()) {
			for (final Entry<NODE, NODE> ccc2 : mAuxData.getCcChildren(array2Rep).entrySet()) {
				if (getEqualityStatus(ccc1.getValue(), ccc2.getValue()) != EqualityStatus.EQUAL) {
					continue;
				}

				final Set<CongruenceClosure<NODE>> shiftedLabelWithException = mWeakEquivalenceGraph
						.shiftLabelAndAddException(strengthenedEdgeLabelContents, ccc1.getValue(),
								mFactory.getAllWeqVarsNodeForFunction(ccc1.getKey()));

				// recursive call
				reportWeakEquivalenceDoOnlyRoweqPropagations(ccc1.getKey(), ccc2.getKey(),
						shiftedLabelWithException);
			}
		}

//		assert sanityCheck();
		return true;
	}

	/**
	 * Given a (multidimensional) index, compute the corresponding annotation for a
	 * weak equivalence edge.
	 *
	 * Example: for (i1, .., in), this should return (q1 = i1, ..., qn = in) as a
	 * list of CongruenceClosures. (where qi is the variable returned by
	 * getWeqVariableForDimension(i))
	 *
	 * @param nodes
	 * @return
	 */
	private CongruenceClosure<NODE> computeWeqConstraintForIndex(final List<NODE> nodes) {
		final CongruenceClosure<NODE> result = new CongruenceClosure<>();
		for (int i = 0; i < nodes.size(); i++) {
			final NODE ithNode = nodes.get(i);
			result.reportEquality(mFactory.getWeqVariableNodeForDimension(i, ithNode.getTerm().getSort()), ithNode);
		}
		return result;
	}

	@Override
	public boolean reportEquality(final NODE node1, final NODE node2) {
		assert !isFrozen();
		final boolean result = reportEqualityRec(node1, node2);
		executeFloydWarshallAndReportResultToWeqCc();
		assert sanityCheck();
		return result;
	}

	@Override
	protected boolean reportEqualityRec(final NODE node1, final NODE node2) {
		assert node1.hasSameTypeAs(node2);
		if (isInconsistent()) {
			throw new IllegalStateException();
		}

		boolean freshElem = false;
		freshElem |= addElementRec(node1);
		freshElem |= addElementRec(node2);
		assert assertAtMostOneLiteralPerEquivalenceClass();

		if (getEqualityStatus(node1, node2) == EqualityStatus.EQUAL) {
			// nothing to do
			return freshElem;
		}
		if (getEqualityStatus(node1, node2) == EqualityStatus.NOT_EQUAL) {
			// report it to tver so that it is in an inconsistent state
			mElementTVER.reportEquality(node1, node2);
			// not so nice, but needed for literals where TVER does not know they are unequal otherwise
			if (!mElementTVER.isInconsistent()) {
				mElementTVER.reportDisequality(node1, node2);
			}
			assert mElementTVER.isInconsistent();
			return true;
		}


		// old means "before the merge", here..
		final NODE node1OldRep = getRepresentativeElement(node1);
		final NODE node2OldRep = getRepresentativeElement(node2);
		final CongruenceClosure<NODE>.CcAuxData oldAuxData = new CcAuxData(mAuxData, true);

		mWeakEquivalenceGraph.collapseEdgeAtMerge(node1OldRep, node2OldRep);

		/*
		 * cannot just du a super.reportEquality here, because we want to reestablish some class invariants (checked
		 * through sanityCheck()) before doing the recursive calls for the fwcc and bwcc propagations)
		 * in particular we need to do mWeakEquivalenceGraph.updateforNewRep(..)
		 */
		final Pair<HashRelation<NODE, NODE>, HashRelation<NODE, NODE>> propInfo = doMergeAndComputePropagations(node1,
				node2);
		if (propInfo == null) {
			// this became inconsistent through the merge
			return true;
		}


		final NODE newRep = getRepresentativeElement(node1);
		mWeakEquivalenceGraph.updateForNewRep(node1OldRep, node2OldRep, newRep);

		if (isInconsistent()) {
			return true;
		}

		doFwccAndBwccPropagationsFromMerge(propInfo);

		if (isInconsistent()) {
			return true;
		}

		doRoweqPropagationsOnMerge(node1, node2, node1OldRep, node2OldRep, oldAuxData);

		if (isInconsistent()) {
			return true;
		}

//		executeFloydWarshallAndReportResult();

		/*
		 * ext
		 */
		reportGpaChangeToWeqGraphAndPropagateArrayEqualities(
				(final CongruenceClosure<NODE> cc) -> cc.reportEquality(node1, node2));

		return true;
	}

	private void doRoweqPropagationsOnMerge(final NODE node1, final NODE node2, final NODE node1OldRep,
			final NODE node2OldRep, final CcAuxData oldAuxData) {
		if (isInconsistent()) {
			return;
		}

		/*
		 * there are three types of propagations related to weak equivalences,
		 * corresponding to the rules ext, roweq and roweq-1
		 */

		/*
		 * the merge may collapse two nodes in the weak equivalence graph (which may trigger propagations)
		 */
		// (recursive call)
		// EDIT: adding an edge between nodes that are being merged is problematic algorithmically
		// instead do the rule roweqMerge (which models the consequence of the below a -- false -- b edge, together
		//  with fwcc), doing it in an extra procedure..
		//	goOn |= reportWeakEquivalenceDoOnlyRoweqPropagations(node1OldRep, node2OldRep, Collections.emptyList());
		// we will treat roweqMerge during the other propagations below as it need similar matching..

		for (final Entry<NODE, NODE> ccc1 : oldAuxData.getCcChildren(node1OldRep)) {
			// don't propagate something that uses the currently removed element
			final NODE ccc1AfReplaced = ccc1.getKey();
			final NODE ccc1ArgReplaced = ccc1.getValue();
			if (ccc1AfReplaced == null || ccc1ArgReplaced == null) {
				continue;
			}

			for (final Entry<NODE, NODE> ccc2 : oldAuxData.getCcChildren(node2OldRep)) {

				// don't propagate something that uses the currently removed element
				final NODE ccc2AfReplaced = ccc2.getKey();
				final NODE ccc2ArgReplaced = ccc2.getValue();
				if (ccc2AfReplaced == null || ccc2ArgReplaced == null) {
					continue;
				}

				assert hasElements(ccc1AfReplaced, ccc1ArgReplaced, ccc2AfReplaced, ccc2ArgReplaced);

				// case ccc1 = (a,i), ccc2 = (b,j)
				if (getEqualityStatus(ccc1ArgReplaced, ccc2ArgReplaced) != EqualityStatus.EQUAL) {
					// not i = j --> cannot propagate
					continue;
				}
				// i = j

				final NODE firstWeqVar = mFactory.getAllWeqVarsNodeForFunction(ccc1AfReplaced).get(0);
				final CongruenceClosure<NODE> qUnequalI = new CongruenceClosure<>();
				qUnequalI.reportDisequality(firstWeqVar, ccc1ArgReplaced);
				reportWeakEquivalenceDoOnlyRoweqPropagations(ccc1AfReplaced, ccc2AfReplaced,
						Collections.singleton(qUnequalI));
			}
		}


		/*
		 * roweq, roweq-1 (1)
		 */
		// node1 = i, node2 = j in the rule
		// for (final NODE ccp1 : mAuxData.getArgCcPars(node1)) {
		for (final NODE ccp1 : oldAuxData.getArgCcPars(node1OldRep)) {
			for (final NODE ccp2 : oldAuxData.getArgCcPars(node2OldRep)) {
				// ccp1 = a[i], ccp2 = b[j] in the rule

				if (!ccp1.getSort().equals(ccp2.getSort())) {
					continue;
				}

				/*
				 * roweq:
				 */
				final Set<CongruenceClosure<NODE>> aToBLabel = mWeakEquivalenceGraph
						.getEdgeLabelContents(ccp1.getAppliedFunction(), ccp2.getAppliedFunction());
				final Set<CongruenceClosure<NODE>> projectedLabel = mWeakEquivalenceGraph.projectEdgeLabelToPoint(
						aToBLabel, ccp1.getArgument(),
						mFactory.getAllWeqVarsNodeForFunction(ccp1.getAppliedFunction()));
				// recursive call
				reportWeakEquivalenceDoOnlyRoweqPropagations(ccp1, ccp2, projectedLabel);

				/*
				 * roweq-1:
				 */
				final Set<CongruenceClosure<NODE>> aiToBjLabel = mWeakEquivalenceGraph.getEdgeLabelContents(ccp1,
						ccp2);
				final Set<CongruenceClosure<NODE>> shiftedLabelWithException = mWeakEquivalenceGraph
						.shiftLabelAndAddException(aiToBjLabel, node1,
								mFactory.getAllWeqVarsNodeForFunction(ccp1.getAppliedFunction()));
				// recursive call
				reportWeakEquivalenceDoOnlyRoweqPropagations(ccp1.getAppliedFunction(),
						ccp2.getAppliedFunction(), shiftedLabelWithException);

				/*
				 * roweqMerge
				 */
				if (getEqualityStatus(ccp1, ccp2) == EqualityStatus.EQUAL) {
					// we have node1 = i, node2 = j, ccp1 = a[i], ccp2 = b[j]
					final NODE firstWeqVar = mFactory.getAllWeqVarsNodeForFunction(ccp1.getAppliedFunction()).get(0);
					assert mFactory.getAllWeqVarsNodeForFunction(ccp1.getAppliedFunction())
						.equals(mFactory.getAllWeqVarsNodeForFunction(ccp2.getAppliedFunction()));
					assert getEqualityStatus(ccp2.getArgument(), ccp1.getArgument()) == EqualityStatus.EQUAL :
						" propagation is only allowed if i = j";

					final CongruenceClosure<NODE> qUnequalI = new CongruenceClosure<>();
					qUnequalI.reportDisequality(firstWeqVar, ccp1.getArgument());

					reportWeakEquivalenceDoOnlyRoweqPropagations(ccp1.getAppliedFunction(),
							ccp2.getAppliedFunction(), Collections.singleton(qUnequalI));
				}
			}

		}
//		assert sanityCheck();

		/*
		 * roweq-1(2)
		 *
		 * a somewhat more intricate case:
		 *
		 * the added equality may trigger the pattern matching on the weak equivalence
		 * condition of the roweq-1 rule
		 */
		otherRoweqPropOnMerge(node1OldRep, oldAuxData);
		otherRoweqPropOnMerge(node2OldRep, oldAuxData);
	}



	private boolean otherRoweqPropOnMerge(final NODE nodeOldRep, final CcAuxData oldAuxData) {
		boolean madeChanges = false;
		for (final Entry<NODE, NODE> ccc : oldAuxData.getCcChildren(nodeOldRep)) {
			// ccc = (b,j) , as in b[j]
			for (final Entry<NODE, WeakEquivalenceEdgeLabel<NODE>> edgeAdjacentToNode
					: mWeakEquivalenceGraph .getAdjacentWeqEdges(nodeOldRep).entrySet()) {
				final NODE n = edgeAdjacentToNode.getKey();
				final WeakEquivalenceEdgeLabel<NODE> phi = edgeAdjacentToNode.getValue();

				// TODO is it ok here to use that auxData from after the merge??
				if (!oldAuxData.getArgCcPars(ccc.getValue()).contains(edgeAdjacentToNode.getKey())) {
					continue;
				}
				// n in argccp(j)

				// TODO is it ok here to use tha auxData from after the merge??
				for (final Entry<NODE, NODE> aj : oldAuxData.getCcChildren(edgeAdjacentToNode.getKey())) {
					// aj = (a,j), as in a[j]

					// propagate b -- q != j, Phi+ -- a

					final Set<CongruenceClosure<NODE>> shiftedLabelWithException = mWeakEquivalenceGraph
							.shiftLabelAndAddException(phi.getLabelContents(), ccc.getValue(),
									mFactory.getAllWeqVarsNodeForFunction(ccc.getKey()));
					// recursive call
					madeChanges |= reportWeakEquivalenceDoOnlyRoweqPropagations(ccc.getKey(), aj.getKey(),
							shiftedLabelWithException);
				}
			}

			/*
			 * roweqMerge rule:
			 *  not necessary here as we used ccpar in do doRoweqPropagationsOnMerge
			 */
		}
		return madeChanges;
	}

	void reportAllArrayEqualitiesFromWeqGraph() {
		while (mWeakEquivalenceGraph.hasArrayEqualities()) {
			final Entry<NODE, NODE> aeq = mWeakEquivalenceGraph.pollArrayEquality();
			reportEquality(aeq.getKey(), aeq.getValue());
			if (isInconsistent()) {
				assert sanityCheck();
				return;
			}
			assert sanityCheck();
		}
		assert sanityCheck();
		assert weqGraphFreeOfArrayEqualities();
	}

	@Override
	public boolean reportDisequality(final NODE node1, final NODE node2) {
		assert !isFrozen();
		final boolean result = reportDisequalityRec(node1, node2);
		assert sanityCheck();
		return result;
	}

	@Override
	protected boolean reportDisequalityRec(final NODE node1, final NODE node2) {
		boolean madeChanges = false;

		madeChanges |= super.reportDisequalityRec(node1, node2);

		if (!madeChanges) {
			return false;
		}

		if (isInconsistent()) {
			// no need for further propagations
			return true;
		}

		reportGpaChangeToWeqGraphAndPropagateArrayEqualities(
				(final CongruenceClosure<NODE> cc) -> cc.reportDisequality(node1, node2));

		if (isInconsistent()) {
			// omit sanity checks
			return true;
		}

		assert weqGraphFreeOfArrayEqualities();
		return true;
	}

	/**
	 * Updates the weq-graph wrt. a change in the ground partial arrangement.
	 * Immediately propagates array equalities if some have occurred.
	 *
	 * @param reporter
	 * @return
	 */
	private boolean reportGpaChangeToWeqGraphAndPropagateArrayEqualities(
			final Predicate<CongruenceClosure<NODE>> reporter) {
		assert sanityCheck();
		if (isInconsistent()) {
			return false;
		}
		boolean madeChanges = false;
		madeChanges |= mWeakEquivalenceGraph.reportChangeInGroundPartialArrangement(reporter);
		reportAllArrayEqualitiesFromWeqGraph();
		assert sanityCheck();
		return madeChanges;
	}

	@Override
	public boolean isTautological() {
		// TODO: literal disequalities don't prevent being tautological --> account for that!
		return super.isTautological() && mWeakEquivalenceGraph.isEmpty();
	}

	@Override
	public boolean isStrongerThan(final CongruenceClosure<NODE> other) {
		if (!(other instanceof WeqCongruenceClosure<?>)) {
			throw new IllegalArgumentException();
		}
		if (!super.isStrongerThan(other)) {
			return false;
		}

		final WeqCongruenceClosure<NODE> otherWeqCc = (WeqCongruenceClosure<NODE>) other;

		if (!mWeakEquivalenceGraph.isStrongerThan(otherWeqCc.mWeakEquivalenceGraph)) {
			return false;
		}
		return true;
	}

	@Override
	protected void prepareForRemove(final boolean useWeqGpa) {
		if (useWeqGpa) {
//			mWeakEquivalenceGraph.meetEdgeLabelsWithWeqGpaBeforeRemove(new WeqCongruenceClosure<>(this));
			mWeakEquivalenceGraph.meetEdgeLabelsWithWeqGpaBeforeRemove(mFactory.getCcManager().makeCopy(this));
		} else {
			mWeakEquivalenceGraph.meetEdgeLabelsWithCcGpaBeforeRemove();
		}
		super.prepareForRemove(useWeqGpa);
	}

	@Override
	protected void applyClosureOperations() {
		executeFloydWarshallAndReportResultToWeqCc();
		assert sanityCheck();
		reportAllArrayEqualitiesFromWeqGraph();
		assert sanityCheck();
	}

	@Override
	public Set<NODE> removeElementAndDependents(final NODE elem, final Set<NODE> elementsToRemove,
			final Map<NODE, NODE> nodeToReplacementNode, final boolean useWeqGpa) {

		for (final NODE etr : elementsToRemove) {
			mWeakEquivalenceGraph.updateVerticesOnRemoveElement(etr, nodeToReplacementNode.get(etr));
		}


		final Set<NODE> nodesToAddInGpa = mWeakEquivalenceGraph.projectSimpleElementInEdgeLabels(elem, useWeqGpa);

		assert !useWeqGpa || nodesToAddInGpa.isEmpty() : "we don't allow introduction of new nodes at labels if we"
				+ "are not in the meet-with-WeqGpa case";

		super.removeElementAndDependents(elem, elementsToRemove, nodeToReplacementNode, useWeqGpa);

		return nodesToAddInGpa;
	}

	@Override
	protected Set<NODE> getNodesToIntroduceBeforeRemoval(final NODE elemToRemove,
			final Map<NODE, NODE> elemToRemoveToReplacement) {
		final boolean stopAtFirst = false;

	    final Set<NODE> replByFwcc = super.getNodesToIntroduceBeforeRemoval(elemToRemove,
	    		elemToRemoveToReplacement);


		if (!replByFwcc.isEmpty()) {
			assert DataStructureUtils.intersection(
					mElementCurrentlyBeingRemoved.getRemovedElements(), replByFwcc).isEmpty();
			return replByFwcc;
		}


		final boolean etrIsRemovedBecauseOfAf =
				elemToRemoveToReplacement.keySet().contains(elemToRemove.getAppliedFunction());
		if (!etrIsRemovedBecauseOfAf) {
			return Collections.emptySet();
		}

		/*
		 * say elemToRemove = a[i]
		 */
		assert elemToRemove.isFunctionApplication();

		final Set<NODE> result = new HashSet<>();

		/*
		 * we may need this later if i is also scheduled for removal
		 */
		final boolean iToBeRemovedToo = elemToRemoveToReplacement.keySet().contains(elemToRemove.getArgument());
		final NODE jEqualToI =
				getOtherEquivalenceClassMember(elemToRemove.getArgument(), elemToRemoveToReplacement.keySet());
		if (iToBeRemovedToo && jEqualToI == null) {
			// no way of introducing a b[j] because we cannot find a j (and i is being removed, too..)
			return Collections.emptySet();
		}
		// a node equal to i
		final NODE j = iToBeRemovedToo ? jEqualToI : elemToRemove.getArgument();

		// forall b --Phi(q)-- a
		for (final Entry<NODE, WeakEquivalenceEdgeLabel<NODE>> edge
				: mWeakEquivalenceGraph.getAdjacentWeqEdges(elemToRemove.getAppliedFunction()).entrySet()) {
			assert !edge.getKey().equals(elemToRemove.getAppliedFunction());
			if (elemToRemoveToReplacement.keySet().contains(edge.getKey())) {
				// b is also being removed, cannot use it for propagations..
				continue;
			}

			final Set<CongruenceClosure<NODE>> projectedLabel = mWeakEquivalenceGraph
					.projectEdgeLabelToPoint(edge.getValue().getLabelContents(),
							elemToRemove.getArgument(),
							mFactory.getAllWeqVarsNodeForFunction(elemToRemove.getAppliedFunction()));

			if (isLabelTautological(projectedLabel)) {
				continue;
			}

			/*
			 *  best case: projectedLabel is inconsistent, this means if we introduce b[i] we can later propagate
			 *  a[i] = b[i], this also means we don't need to introduce any other node
			 */
			if (projectedLabel.isEmpty()) {
				final NODE bi = mFactory.getEqNodeAndFunctionFactory()
						.getOrConstructFuncAppElement(edge.getKey(), j);
				assert !mElementCurrentlyBeingRemoved.getRemovedElements().contains(bi);
				elemToRemoveToReplacement.put(elemToRemove, bi);
				if (!hasElement(bi)) {
					return Collections.singleton(bi);
				} else {
					return Collections.emptySet();
				}
			}

			/*
			 * if there is a disjunct in projectedLabel that does not depend on any weq var, we don't introduce a new
			 * node (we would get a weak equivalence with a ground disjunct
			 * EDIT: this case should be treatable via check for tautology (see also assert below)
			 */
			if (isLabelTautological(projectedLabel)) {
				continue;
			}
			// if a disjunct was ground, the the projectToElem(weqvars) operation should have made it "true"
			assert !projectedLabel.stream().anyMatch(l ->
				DataStructureUtils.intersection(l.getAllElements(), mFactory.getAllWeqNodes()).isEmpty());


			final NODE bi = mFactory.getEqNodeAndFunctionFactory() .getOrConstructFuncAppElement(edge.getKey(), j);

			if (stopAtFirst) {
				assert !mElementCurrentlyBeingRemoved.getRemovedElements().contains(bi);
				if (!hasElement(bi)) {
					return Collections.singleton(bi);
				} else {
					return Collections.emptySet();
				}
			}
			assert !mElementCurrentlyBeingRemoved.getRemovedElements().contains(bi);
			if (!hasElement(bi)) {
				result.add(bi);
			}
		}

		return result;
	}

	private boolean isLabelTautological(final Set<CongruenceClosure<NODE>> projectedLabel) {
		return projectedLabel.size() == 1 && projectedLabel.iterator().next().isTautological();
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
	protected void registerNewElement(final NODE elem, final RemoveElement remInfo) {
		super.registerNewElement(elem, remInfo);

		if (isInconsistent()) {
			// nothing more to do
			return;
		}


		if (!elem.isFunctionApplication()) {
			// nothing to do
//			assert sanityCheck();
			return;
		}

//		assert sanityCheck();

		boolean madeChanges = false;
		/*
		 * roweq
		 *
		 * say elem = a[i], then we attempt to discover all b[j] in exp such that i = j, these are the argccpar of i
		 */
		for (final NODE ccp : mAuxData.getArgCcPars(getRepresentativeElement(elem.getArgument()))) {
			if (!ccp.hasSameTypeAs(elem)) {
				// TODO: nicer would be to have argCcPars contain only elements of fitting sort..
				continue;
			}

			assert hasElements(ccp, ccp.getAppliedFunction(), ccp.getArgument());

			// ccp = b[j], look for a weq edge between a and b
			if (getEqualityStatus(elem.getAppliedFunction(), ccp.getAppliedFunction()) == EqualityStatus.EQUAL) {
				// a = b, strong, not weak equivalence, nothing to do here (propagations done by fwcc)
				continue;
			}

			// get label of edge between a and b
			final Set<CongruenceClosure<NODE>> weqEdgeLabelContents =
					mWeakEquivalenceGraph.getEdgeLabelContents(ccp.getAppliedFunction(), elem.getAppliedFunction());

			final Set<CongruenceClosure<NODE>> projectedLabel = mWeakEquivalenceGraph.projectEdgeLabelToPoint(
					weqEdgeLabelContents,
					ccp.getArgument(),
					mFactory.getAllWeqVarsNodeForFunction(ccp.getAppliedFunction()));

			madeChanges |= reportWeakEquivalenceDoOnlyRoweqPropagations(elem,
					ccp,
					projectedLabel);
		}

		if (madeChanges) {
			executeFloydWarshallAndReportResultToWeqCc();
		}
//		assert sanityCheck();
	}

	@Override
	protected void registerNewElement(final NODE elem) {
		registerNewElement(elem, null);
	}

	@Override
	public void transformElementsAndFunctions(final Function<NODE, NODE> elemTransformer) {
		assert !isFrozen();
		super.transformElementsAndFunctions(elemTransformer);

		mWeakEquivalenceGraph.transformElementsAndFunctions(elemTransformer);
	}

	/**
	 * is a simple element and all the elements that depend on it fully removed?
	 */
	@Override
	public boolean assertSimpleElementIsFullyRemoved(final NODE elem) {
		for (final NODE e : getAllElements()) {
			if (e.isDependent() && e.getSupportingNodes().contains(elem)) {
				assert false;
				return false;
			}
		}
		return super.assertSimpleElementIsFullyRemoved(elem);
	}

	@Override
	public boolean assertSingleElementIsFullyRemoved(final NODE elem) {
		if (!mWeakEquivalenceGraph.elementIsFullyRemoved(elem)) {
			assert false;
			return false;
		}

		return super.assertSingleElementIsFullyRemoved(elem);
	}

	@Override
	public WeqCongruenceClosure<NODE> join(final CongruenceClosure<NODE> otherCC) {
		if (!(otherCC instanceof WeqCongruenceClosure)) {
			throw new IllegalArgumentException();
		}
		if (otherCC.isInconsistent()) {
//			return new WeqCongruenceClosure<>(this);
			return mFactory.getCcManager().makeCopy(this);
		}

		final WeqCongruenceClosure<NODE> other = (WeqCongruenceClosure<NODE>) otherCC;

		return new WeqCongruenceClosure<>(super.join(other), mWeakEquivalenceGraph.join(other.mWeakEquivalenceGraph),
				mFactory);
	}

	@Override
	public WeqCongruenceClosure<NODE> meet(final CongruenceClosure<NODE> other) {

		final WeqCongruenceClosure<NODE> result = meetRec(other);

		result.executeFloydWarshallAndReportResultToWeqCc();
		if (result.isInconsistent()) {
			return new WeqCongruenceClosure<>(true);
		}
		result.reportAllArrayEqualitiesFromWeqGraph();
		if (result.isInconsistent()) {
			return new WeqCongruenceClosure<>(true);
		}

		assert result.sanityCheck();
		return result;
	}

	@Override
	public WeqCongruenceClosure<NODE> meetRec(final CongruenceClosure<NODE> other) {
		final WeqCongruenceClosure<NODE> gPaMeet = meetWeqWithCc(other);
		assert gPaMeet.sanityCheck();
		if (gPaMeet.isInconsistent()) {
			return new WeqCongruenceClosure<>(true);
		}
		assert gPaMeet.assertAtMostOneLiteralPerEquivalenceClass();
		assert !this.mWeakEquivalenceGraph.hasArrayEqualities();


		if (!(other instanceof WeqCongruenceClosure)) {
			return gPaMeet;
		}

		/*
		 * strategy: conjoin all weq edges of otherCC to a copy of this's weq graph
		 */

		final WeqCongruenceClosure<NODE> newWeqCc = gPaMeet;
		assert newWeqCc.sanityCheck();

		final WeqCongruenceClosure<NODE> otherWeqCc = (WeqCongruenceClosure<NODE>) other;
		assert otherWeqCc.mWeakEquivalenceGraph.sanityCheck();
		assert otherWeqCc.sanityCheck();

		// report all weq edges from other
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE>> edge
				: otherWeqCc.mWeakEquivalenceGraph.getEdges().entrySet()) {

//			assert gPaMeet.getAllElements().containsAll(edge.getValue().getAppearingNodes());

			newWeqCc.reportWeakEquivalenceDoOnlyRoweqPropagations(edge.getKey().getOneElement(),
					edge.getKey().getOtherElement(),
					edge.getValue().getLabelContents());
			assert newWeqCc.sanityCheck();
		}

		return newWeqCc;
	}

	private WeqCongruenceClosure<NODE> meetWeqWithCc(final CongruenceClosure<NODE> other) {
		assert !this.isInconsistent() && !other.isInconsistent();

		final WeqCongruenceClosure<NODE> thisAligned = this.alignElementsAndFunctionsWeqRec(other, null);
		final CongruenceClosure<NODE> otherAligned = other.alignElementsAndFunctionsCc(this, null);

		for (final Entry<NODE, NODE> eq : otherAligned.getSupportingElementEqualities().entrySet()) {
			if (thisAligned.isInconsistent()) {
				return new WeqCongruenceClosure<>(true);
			}
			thisAligned.reportEqualityRec(eq.getKey(), eq.getValue());
		}
		for (final Entry<NODE, NODE> deq : otherAligned.getElementDisequalities()) {
			if (thisAligned.isInconsistent()) {
				return new WeqCongruenceClosure<>(true);
			}
			thisAligned.reportDisequalityRec(deq.getKey(), deq.getValue());
		}
		assert thisAligned.sanityCheck();
		return thisAligned;
	}

	@Override
	public boolean sanityCheck() {
		boolean res = super.sanityCheck();
		if (mWeakEquivalenceGraph != null) {
			res &= mWeakEquivalenceGraph.sanityCheck();
		}

		if (!mMeetWithGpaCase && !isInconsistent()) {
			for (final NODE el : getAllElements()) {
				if (dependsOnAny(el, mFactory.getAllWeqPrimedNodes())) {
					assert false;
					return false;
				}
			}
		}

		return res;
	}

	@Override
	public String toString() {
		if (isTautological()) {
			return "True";
		}
		if (isInconsistent()) {
			return "False";
		}
		if (getAllElements().size() < 20) {
			return toLogString();
		}

		final StringBuilder sb = new StringBuilder();
		sb.append("Partial arrangement:\n");
		sb.append(super.toString());
		sb.append("\n");
		if (mWeakEquivalenceGraph != null) {
			sb.append("Weak equivalences:\n");
			sb.append(mWeakEquivalenceGraph.toString());
		} else {
			sb.append("weak equivalence graph is null\n");
		}
		return sb.toString();
	}

	@Override
	public String toLogString() {
		if (isTautological()) {
			return "True";
		}
		if (isInconsistent()) {
			return "False";
		}
		final StringBuilder sb = new StringBuilder();
		sb.append("Partial arrangement:\n");
		sb.append(super.toLogString());
		sb.append("\n");
		if (mWeakEquivalenceGraph != null && !mWeakEquivalenceGraph.isEmpty()) {
			sb.append("Weak equivalences:\n");
			sb.append(mWeakEquivalenceGraph.toLogString());
		} else if (mWeakEquivalenceGraph.isEmpty()) {
			sb.append("weak equivalence graph is empty\n");
		} else {
			sb.append("weak equivalence graph is null\n");
		}
		return sb.toString();
	}

	/**
	 * for sanity checking
	 * @return
	 */
	public boolean weqGraphFreeOfArrayEqualities() {
		if (mWeakEquivalenceGraph.hasArrayEqualities()) {
			assert false;
			return false;
		}
		return true;
	}

	public Integer getStatistics(final VPStatistics stat) {
		switch (stat) {
		case MAX_WEQGRAPH_SIZE:
			return mWeakEquivalenceGraph.getNumberOfEdgesStatistic();
		case MAX_SIZEOF_WEQEDGELABEL:
			return mWeakEquivalenceGraph.getMaxSizeOfEdgeLabelStatistic();
		case NO_SUPPORTING_DISEQUALITIES:
			// we have to eliminate symmetric entries
			final HashRelation<NODE, NODE> cleanedDeqs = new HashRelation<>();
			for (final Entry<NODE, NODE> deq : mElementTVER.getDisequalities()) {
				if (cleanedDeqs.containsPair(deq.getValue(), deq.getKey())) {
					continue;
				}
				cleanedDeqs.addPair(deq.getKey(), deq.getValue());
			}
			return cleanedDeqs.size();
		case NO_SUPPORTING_EQUALITIES:
			return getSupportingElementEqualities().size();
		default :
			return VPStatistics.getNonApplicableValue(stat);
		}
	}

}
