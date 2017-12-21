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

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.EqualityStatus;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.CcAuxData;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.CcSettings;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.CongruenceClosure;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.ICongruenceClosure;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.IRemovalInfo;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class WeqCongruenceClosure<NODE extends IEqNodeIdentifier<NODE>>
		implements ICongruenceClosure<NODE> {

	private final CongruenceClosure<NODE> mCongruenceClosure;

	// slim version
//	private WeakEquivalenceGraph<NODE, CongruenceClosure<NODE>> mWeakEquivalenceGraph;
	private WeakEquivalenceGraph<NODE, CongruenceClosure<NODE>> mWeakEquivalenceGraphThin;

	private WeakEquivalenceGraph<NODE, CongruenceClosure<NODE>> mWeakEquivalenceGraphCcFat;
	private WeakEquivalenceGraph<NODE, WeqCongruenceClosure<NODE>> mWeakEquivalenceGraphWeqCcFat;

	public final boolean mMeetWithGpaCase;

	private boolean mIsFrozen = false;

	private final ILogger mLogger;

	private WeqCcManager<NODE> mManager;

	Diet mDiet;

	/**
	 * Create an empty ("True"/unconstrained) WeqCC.
	 *
	 * @param factory
	 */
	public WeqCongruenceClosure(final WeqCcManager<NODE> manager) {
		assert manager != null;
		mLogger = manager.getLogger();
		mManager = manager;
		mCongruenceClosure = manager.getEmptyCc(true);
		mWeakEquivalenceGraphThin = new WeakEquivalenceGraph<>(this, manager, manager.getEmptyCc(false));
		mDiet = Diet.THIN;

		mMeetWithGpaCase = false;
		assert sanityCheck();
	}

	/**
	 * Create an inconsistent ("False") WeqCC.
	 *
	 * @param isInconsistent
	 */
	public WeqCongruenceClosure(final boolean isInconsistent) {
		if (!isInconsistent) {
			throw new IllegalArgumentException("use other constructor!");
		}
		mCongruenceClosure = null;
//		mWeakEquivalenceGraph = null;
		mManager = null;
		mLogger = null;
		mMeetWithGpaCase = false;
		mIsFrozen = true;
	}

	/**
	 * Create a WeqCC using the given CongruenceClosure as ground partial
	 * arrangement (gpa) and the given WeakEquivalenceGraph.
	 *
	 * @param cc
	 * @param manager
	 */
	public WeqCongruenceClosure(final CongruenceClosure<NODE> cc,
			final WeakEquivalenceGraph<NODE, CongruenceClosure<NODE>> weqGraph,
			final WeqCcManager<NODE> manager) {
		assert !cc.isFrozen();

		mLogger = manager.getLogger();
		mCongruenceClosure = manager.copyCcNoRemInfo(cc);

		assert manager != null;
		if (cc.isInconsistent()) {
			throw new IllegalArgumentException("use other constructor!");
		}
		mManager = manager;

		mMeetWithGpaCase = false;

		// we need a fresh instance of WeakEquivalenceGraph here, because we cannot set the link in the weq
		// graph to the right cc instance..
		mWeakEquivalenceGraphThin = new WeakEquivalenceGraph<>(this, weqGraph, false);
		mDiet = Diet.THIN;

		assert sanityCheck();
	}

	public WeqCongruenceClosure(final WeqCongruenceClosure<NODE> original) {
		this(original, original.mMeetWithGpaCase);
		assert !mCongruenceClosure.isFrozen();
		assert !mIsFrozen;
		assert getWeakEquivalenceGraph().assertLabelsAreUnfrozen();
	}

	/**
	 * Makes a copy.
	 * May conflate weq edges.
	 *
	 * @param original
	 * @param meetWGpaCase
	 */
	public WeqCongruenceClosure(final WeqCongruenceClosure<NODE> original, final boolean meetWGpaCase) {
		mLogger = original.getLogger();
		mManager = original.mManager;
		mCongruenceClosure = mManager.copyCcNoRemInfoUnfrozen(original.mCongruenceClosure);
		assert !mCongruenceClosure.isFrozen();
		assert original.mManager != null;
		mMeetWithGpaCase = meetWGpaCase;

		assert original.mDiet == Diet.THIN;
		mDiet = original.mDiet;
		mWeakEquivalenceGraphThin = new WeakEquivalenceGraph<>(this, original.mWeakEquivalenceGraphThin,
				meetWGpaCase && WeqSettings.FLATTEN_WEQ_EDGES_BEFORE_JOIN); //TODO simplify

		assert sanityCheck();
	}

	public void addElement(final NODE elem) {
		assert !isFrozen();
		addElementRec(elem);
		assert mCongruenceClosure.sanityCheck();

		if (!CcSettings.DELAY_EXT_AND_DELTA_CLOSURE) {
			// TODO: do full applyClosureOperations here??
			extAndTriangleClosure();
			executeFloydWarshallAndReportResultToWeqCc();
		}
		reportAllArrayEqualitiesFromWeqGraph();

		assert sanityCheck();
	}

	@Override
	public boolean isFrozen() {
		assert mIsFrozen == mCongruenceClosure.isFrozen();
		return mIsFrozen;
	}

	@Override
	public void freeze() {
		/*
		 *  Do all possible propagations that were delayed.
		 *  Currently: propagations according to the rules ext and delta.
		 */

		extAndTriangleClosure();

		// set the flags
		if (mCongruenceClosure != null) {
			mCongruenceClosure.freeze();;
		}
//		if (mWeakEquivalenceGraph != null) {
		if (!isInconsistent()) {
			getWeakEquivalenceGraph().freeze();
		}
		mIsFrozen = true;
	}

	@Override
	public boolean isInconsistent() {
		return mCongruenceClosure == null || mCongruenceClosure.isInconsistent();
	}

	/**
	 * (works in place)
	 * @param array1
	 * @param array2
	 * @param storeIndex
	 * @param inplace
	 */
	public void reportWeakEquivalence(final NODE array1, final NODE array2, final NODE storeIndex) {
		assert !isFrozen();
		assert array1.hasSameTypeAs(array2);

		mManager.addNode(storeIndex, mCongruenceClosure, true, true);
		assert sanityCheck();

		reportWeakEquivalence(array1, array2, mManager.getEdgeLabelForIndex(getWeakEquivalenceGraph(), storeIndex));
		assert sanityCheck();
	}

	/**
	 * (works in place)
	 *
	 * @param array1
	 * @param array2
	 * @param edgeLabel
	 */
	private void reportWeakEquivalence(final NODE array1, final NODE array2,
			final WeakEquivalenceEdgeLabel<NODE, CongruenceClosure<NODE>> edgeLabel) {
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

			if (!CcSettings.DELAY_EXT_AND_DELTA_CLOSURE) {
				madeChanges = false;
				madeChanges |= executeFloydWarshallAndReportResultToWeqCc();
				if (!madeChanges) {
					break;
				}
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
		final Map<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE, CongruenceClosure<NODE>>> fwResult = getWeakEquivalenceGraph()
				.propagateViaTriangleRule();
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE, CongruenceClosure<NODE>>> fwEdge : fwResult
				.entrySet()) {
			fwmc |= reportWeakEquivalenceDoOnlyRoweqPropagations(fwEdge.getKey().getOneElement(),
					fwEdge.getKey().getOtherElement(), fwEdge.getValue());
			assert sanityCheck();
		}
		assert sanityCheck();
		return fwmc;
	}

	private boolean reportWeakEquivalenceDoOnlyRoweqPropagations(final NODE array1, final NODE array2,
			final WeakEquivalenceEdgeLabel<NODE, CongruenceClosure<NODE>> edgeLabel) {
		assert edgeLabel.assertIsSlim();

		if (isInconsistent()) {
			return false;
		}

		if (edgeLabel.isTautological()) {
			return false;
		}

		boolean madeChanges = false;
		madeChanges |= !mCongruenceClosure.hasElement(array1);
		madeChanges |= !mCongruenceClosure.hasElement(array2);
		mManager.addNode(array1, mCongruenceClosure, true, true);
		mManager.addNode(array2, mCongruenceClosure, true, true);

		final NODE array1Rep = mCongruenceClosure.getRepresentativeElement(array1);
		final NODE array2Rep = mCongruenceClosure.getRepresentativeElement(array2);

		if (array1Rep == array2Rep) {
			// no need to have a weq edge from the node to itself
			return madeChanges;
		}

		madeChanges |= getWeakEquivalenceGraph().reportWeakEquivalence(array1Rep, array2Rep, edgeLabel);

		if (!madeChanges) {
			// nothing to propagate
			return false;
		}

		final WeakEquivalenceEdgeLabel<NODE, CongruenceClosure<NODE>> strengthenedEdgeLabel =
				getWeakEquivalenceGraph().getEdgeLabel(array1Rep, array2Rep);

		if (strengthenedEdgeLabel == null) {
			// edge became "false";
			assert false : "TODO : check this case, this does not happen, right? (and the comment above is nonsense..)";
//			strengthenedEdgeLabel = Collections.emptySet();
		}

		/*
		 * roweq propagations
		 *
		 * look for fitting c[i], d[j] with i ~ j, array1 ~ c, array2 ~ d
		 */
		final Collection<NODE> ccps1 = mCongruenceClosure.getAuxData().getAfCcPars(array1Rep);
		final Collection<NODE> ccps2 = mCongruenceClosure.getAuxData().getAfCcPars(array2Rep);
		for (final NODE ccp1 : ccps1) {
			if (!mCongruenceClosure.hasElements(ccp1, ccp1.getArgument(), ccp1.getAppliedFunction())) {
				continue;
			}
			for (final NODE ccp2 : ccps2) {
				if (isInconsistent()) {
					return true;
				}

				if (!mCongruenceClosure.hasElements(ccp2, ccp2.getArgument(), ccp2.getAppliedFunction())) {
					continue;
				}

				if (mCongruenceClosure.getEqualityStatus(ccp1.getArgument(), ccp2.getArgument()) != EqualityStatus.EQUAL) {
					continue;
				}
				/*
				 * i ~ j holds propagate array1[i] -- -- array2[j] (note that this adds the
				 * arrayX[Y] nodes, possibly -- EDIT: not..)
				 */
				final WeakEquivalenceEdgeLabel<NODE, CongruenceClosure<NODE>> projectedLabel = getWeakEquivalenceGraph().projectEdgeLabelToPoint(
						strengthenedEdgeLabel, ccp1.getArgument(),
						mManager.getAllWeqVarsNodeForFunction(array1));

				// recursive call
				reportWeakEquivalenceDoOnlyRoweqPropagations(ccp1, ccp2, projectedLabel);
			}
		}

		/*
		 * roweq-1 propagations
		 */
		for (final Entry<NODE, NODE> ccc1 :
					mCongruenceClosure.getAuxData().getCcChildren(array1Rep).entrySet()) {
			for (final Entry<NODE, NODE> ccc2 :
					mCongruenceClosure.getAuxData().getCcChildren(array2Rep).entrySet()) {
				if (mCongruenceClosure.getEqualityStatus(ccc1.getValue(), ccc2.getValue()) != EqualityStatus.EQUAL) {
					continue;
				}

				final WeakEquivalenceEdgeLabel<NODE, CongruenceClosure<NODE>> shiftedLabelWithException = getWeakEquivalenceGraph()
						.shiftLabelAndAddException(strengthenedEdgeLabel, ccc1.getValue(),
								mManager.getAllWeqVarsNodeForFunction(ccc1.getKey()));

				// recursive call
				reportWeakEquivalenceDoOnlyRoweqPropagations(ccc1.getKey(), ccc2.getKey(),
						shiftedLabelWithException);
			}
		}

//		assert sanityCheck();
		return true;
	}


	/**
	 * (works in place)
	 * @param node1
	 * @param node2
	 * @return
	 */
	public boolean reportEquality(final NODE node1, final NODE node2) {
		assert !isFrozen();
		final boolean result = reportEqualityRec(node1, node2);
		if (!CcSettings.DELAY_EXT_AND_DELTA_CLOSURE) {
			executeFloydWarshallAndReportResultToWeqCc();
		}
		assert sanityCheck();
		return result;
	}

	/**
	 * (works in place)
	 * @param node1
	 * @param node2
	 * @return
	 */
	private boolean reportEqualityRec(final NODE node1, final NODE node2) {
		assert node1.hasSameTypeAs(node2);
		if (isInconsistent()) {
			throw new IllegalStateException();
		}

		boolean freshElem = false;
		freshElem |= mCongruenceClosure.hasElement(node1);
		freshElem |= mCongruenceClosure.hasElement(node2);
		mManager.addNode(node1, mCongruenceClosure, true, true);
		mManager.addNode(node2, mCongruenceClosure, true, true);
		assert mCongruenceClosure.assertAtMostOneLiteralPerEquivalenceClass();

		if (mCongruenceClosure.getEqualityStatus(node1, node2) == EqualityStatus.EQUAL) {
			// nothing to do
			return freshElem;
		}
		if (mCongruenceClosure.getEqualityStatus(node1, node2) == EqualityStatus.NOT_EQUAL) {
			// report it to tver so that it is in an inconsistent state
			mCongruenceClosure.reportEqualityToElementTVER(node1, node2);
			// not so nice, but needed for literals where TVER does not know they are unequal otherwise
			if (!mCongruenceClosure.isElementTverInconsistent()) {
				mCongruenceClosure.reportDisequalityToElementTver(node1, node2);
			}
			assert mCongruenceClosure.isElementTverInconsistent();
			return true;
		}


		// old means "before the merge", here..
		final NODE node1OldRep = getRepresentativeElement(node1);
		final NODE node2OldRep = getRepresentativeElement(node2);
		final CcAuxData<NODE> oldAuxData = new CcAuxData<>(mCongruenceClosure, mCongruenceClosure.getAuxData(), true);

		getWeakEquivalenceGraph().collapseEdgeAtMerge(node1OldRep, node2OldRep);

		/*
		 * cannot just do a super.reportEquality here, because we want to reestablish some class invariants (checked
		 * through sanityCheck()) before doing the recursive calls for the fwcc and bwcc propagations)
		 * in particular we need to do getWeakEquivalenceGraph().updateforNewRep(..)
		 */
		final Pair<HashRelation<NODE, NODE>, HashRelation<NODE, NODE>> propInfo =
				mCongruenceClosure.doMergeAndComputePropagations(node1, node2);
		if (propInfo == null) {
			// this became inconsistent through the merge
			return true;
		}


		final NODE newRep = getRepresentativeElement(node1);
		getWeakEquivalenceGraph().updateForNewRep(node1OldRep, node2OldRep, newRep);

		if (isInconsistent()) {
			return true;
		}

		mCongruenceClosure.doFwccAndBwccPropagationsFromMerge(propInfo);
		if (isInconsistent()) {
			return true;
		}

		doRoweqPropagationsOnMerge(node1, node2, node1OldRep, node2OldRep, oldAuxData);

		if (isInconsistent()) {
			return true;
		}

		if (WeqSettings.ALWAYS_REPORT_CHANGE_TO_GPA) {
			// ext
			reportGpaChangeToWeqGraphAndPropagateArrayEqualities(
					(final CongruenceClosure<NODE> cc) -> cc.reportEqualityRec(node1, node2));
		}

		return true;
	}

	public NODE getRepresentativeElement(final NODE elem) {
		return mCongruenceClosure.getRepresentativeElement(elem);
	}

	private void doRoweqPropagationsOnMerge(final NODE node1, final NODE node2, final NODE node1OldRep,
			final NODE node2OldRep, final CcAuxData<NODE> oldAuxData) {
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

				assert mCongruenceClosure.hasElements(ccc1AfReplaced, ccc1ArgReplaced, ccc2AfReplaced, ccc2ArgReplaced);

				// case ccc1 = (a,i), ccc2 = (b,j)
				if (getEqualityStatus(ccc1ArgReplaced, ccc2ArgReplaced) != EqualityStatus.EQUAL) {
					// not i = j --> cannot propagate
					continue;
				}
				// i = j

				final NODE firstWeqVar = mManager.getAllWeqVarsNodeForFunction(ccc1AfReplaced).get(0);
				final CongruenceClosure<NODE> qUnequalI = mManager.getSingleDisequalityCc(firstWeqVar, ccc1ArgReplaced,
						true);
				reportWeakEquivalenceDoOnlyRoweqPropagations(ccc1AfReplaced, ccc2AfReplaced,
						mManager.getSingletonEdgeLabel(getWeakEquivalenceGraph(), qUnequalI));
			}
		}


		/*
		 * roweq, roweq-1 (1)
		 *
		 * node1 = i, node2 = j in the paper version of the rule
		 */
		for (final NODE ccp1 : oldAuxData.getArgCcPars(node1OldRep)) {
			for (final NODE ccp2 : oldAuxData.getArgCcPars(node2OldRep)) {
				// ccp1 = a[i], ccp2 = b[j] in the rule

				if (!ccp1.getSort().equals(ccp2.getSort())) {
					continue;
				}

				/*
				 * roweq:
				 */
				final WeakEquivalenceEdgeLabel<NODE, CongruenceClosure<NODE>> aToBLabel = getWeakEquivalenceGraph()
						.getEdgeLabel(ccp1.getAppliedFunction(), ccp2.getAppliedFunction());
				final WeakEquivalenceEdgeLabel<NODE, CongruenceClosure<NODE>> projectedLabel = getWeakEquivalenceGraph().projectEdgeLabelToPoint(
						aToBLabel, ccp1.getArgument(),
						mManager.getAllWeqVarsNodeForFunction(ccp1.getAppliedFunction()));
				// recursive call
				reportWeakEquivalenceDoOnlyRoweqPropagations(ccp1, ccp2, projectedLabel);

				/*
				 * roweq-1:
				 */
				final WeakEquivalenceEdgeLabel<NODE, CongruenceClosure<NODE>> aiToBjLabel = getWeakEquivalenceGraph().getEdgeLabel(ccp1,
						ccp2);
				final WeakEquivalenceEdgeLabel<NODE, CongruenceClosure<NODE>> shiftedLabelWithException = getWeakEquivalenceGraph()
						.shiftLabelAndAddException(aiToBjLabel, node1,
								mManager.getAllWeqVarsNodeForFunction(ccp1.getAppliedFunction()));
				// recursive call
				reportWeakEquivalenceDoOnlyRoweqPropagations(ccp1.getAppliedFunction(),
						ccp2.getAppliedFunction(), shiftedLabelWithException);

				/*
				 * roweqMerge
				 */
				if (getEqualityStatus(ccp1, ccp2) == EqualityStatus.EQUAL) {
					// we have node1 = i, node2 = j, ccp1 = a[i], ccp2 = b[j]
					final NODE firstWeqVar = mManager.getAllWeqVarsNodeForFunction(ccp1.getAppliedFunction()).get(0);
					assert mManager.getAllWeqVarsNodeForFunction(ccp1.getAppliedFunction())
						.equals(mManager.getAllWeqVarsNodeForFunction(ccp2.getAppliedFunction()));
					assert getEqualityStatus(ccp2.getArgument(), ccp1.getArgument()) == EqualityStatus.EQUAL :
						" propagation is only allowed if i = j";

					final CongruenceClosure<NODE> qUnequalI = mManager.getSingleDisequalityCc(firstWeqVar,
							ccp1.getArgument(), true);

					reportWeakEquivalenceDoOnlyRoweqPropagations(ccp1.getAppliedFunction(), ccp2.getAppliedFunction(),
							mManager.getSingletonEdgeLabel(getWeakEquivalenceGraph(), qUnequalI));
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

	public EqualityStatus getEqualityStatus(final NODE node1, final NODE node2) {
		return mCongruenceClosure.getEqualityStatus(node1, node2);
	}

	private boolean otherRoweqPropOnMerge(final NODE nodeOldRep, final CcAuxData<NODE> oldAuxData) {
		boolean madeChanges = false;
		for (final Entry<NODE, NODE> ccc : oldAuxData.getCcChildren(nodeOldRep)) {
			// ccc = (b,j) , as in b[j]
			for (final Entry<NODE, WeakEquivalenceEdgeLabel<NODE, CongruenceClosure<NODE>>> edgeAdjacentToNode
					: getWeakEquivalenceGraph() .getAdjacentWeqEdges(nodeOldRep).entrySet()) {
				final NODE n = edgeAdjacentToNode.getKey();
				final WeakEquivalenceEdgeLabel<NODE, CongruenceClosure<NODE>> phi = edgeAdjacentToNode.getValue();

				// TODO is it ok here to use that auxData from after the merge??
				if (!oldAuxData.getArgCcPars(ccc.getValue())
						.contains(edgeAdjacentToNode.getKey())) {
					continue;
				}
				// n in argccp(j)

				// TODO is it ok here to use tha auxData from after the merge??
				for (final Entry<NODE, NODE> aj : oldAuxData.getCcChildren(edgeAdjacentToNode.getKey())) {
					// aj = (a,j), as in a[j]

					// propagate b -- q != j, Phi+ -- a

					final WeakEquivalenceEdgeLabel<NODE, CongruenceClosure<NODE>> shiftedLabelWithException = getWeakEquivalenceGraph()
							.shiftLabelAndAddException(phi, ccc.getValue(),
									mManager.getAllWeqVarsNodeForFunction(ccc.getKey()));
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

	/**
	 *
	 * @return true iff any constraints were added
	 */
	boolean reportAllArrayEqualitiesFromWeqGraph() {
		boolean madeChanges = false;
		while (getWeakEquivalenceGraph().hasArrayEqualities()) {
			final Entry<NODE, NODE> aeq = getWeakEquivalenceGraph().pollArrayEquality();
			madeChanges |= reportEquality(aeq.getKey(), aeq.getValue());
			if (isInconsistent()) {
				assert sanityCheck();
				assert madeChanges;
				return true;
			}
			assert sanityCheck();
		}
		assert sanityCheck();
		assert weqGraphFreeOfArrayEqualities();
		return madeChanges;
	}

	public boolean reportDisequality(final NODE node1, final NODE node2) {
		assert !isFrozen();
		final boolean result = reportDisequalityRec(node1, node2);
		assert sanityCheck();
		return result;
	}

	private boolean reportDisequalityRec(final NODE node1, final NODE node2) {
		boolean madeChanges = false;

		madeChanges |= mCongruenceClosure.reportDisequalityRec(node1, node2);

		if (!madeChanges) {
			return false;
		}

		if (isInconsistent()) {
			// no need for further propagations
			return true;
		}

		if (WeqSettings.ALWAYS_REPORT_CHANGE_TO_GPA) {
			reportGpaChangeToWeqGraphAndPropagateArrayEqualities(
					(final CongruenceClosure<NODE> cc) -> cc.reportDisequalityRec(node1, node2));
		}

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
	 * implements the rule "ext"
	 *
	 * @param reporter
	 * @return
	 */
	@Deprecated
	private boolean reportGpaChangeToWeqGraphAndPropagateArrayEqualities(
			final Predicate<CongruenceClosure<NODE>> reporter) {
		assert sanityCheck();
		if (isInconsistent()) {
			return false;
		}
		boolean madeChanges = false;
		madeChanges |= getWeakEquivalenceGraph().reportChangeInGroundPartialArrangement(reporter);
		reportAllArrayEqualitiesFromWeqGraph();
		assert sanityCheck();
		return madeChanges;
	}

	@Override
	public boolean isTautological() {
		if (mCongruenceClosure == null) {
			return false;
		}
		return mCongruenceClosure.isTautological() && getWeakEquivalenceGraph().isEmpty();
	}

	public boolean isStrongerThan(final WeqCongruenceClosure<NODE> other) {
//		if (!mCongruenceClosure.isStrongerThan(other.mCongruenceClosure)) {
		if (!mManager.isStrongerThan(this.mCongruenceClosure, other.mCongruenceClosure)) {
			return false;
		}

		if (!mManager.isStrongerThan(getWeakEquivalenceGraph(), other.getWeakEquivalenceGraph())) {
			return false;
		}
		return true;
	}

	/**
	 * "Fatten" all weq edge labels by conjoining the ground truth we know (equalities and disequalities) with them.
	 * Fattening with the whole ground truth (equalities, disequalities, and weak equivalences) is possible, too, but
	 *  expensive and not implemented in a generic way, so it can only be used for a more precise projectAway operation.
	 *
	 * @param useWeqGpa
	 */
	public void fatten(final boolean useWeqGpa) {
		if (useWeqGpa) {
			mWeakEquivalenceGraphWeqCcFat =
					getWeakEquivalenceGraph().meetEdgeLabelsWithWeqGpaBeforeRemove(mManager.copyWeqCc(this, false));
			mWeakEquivalenceGraphThin = null;
			mDiet = Diet.WEQCCFAT;
		} else {
			mWeakEquivalenceGraphCcFat =
					getWeakEquivalenceGraph().meetEdgeLabelsWithCcGpaBeforeRemove();
			mWeakEquivalenceGraphThin = null;
			mDiet = Diet.CCFAT;
		}
	}

	public void extAndTriangleClosure() {

		while (true) {
			// 1. fatten, then saturate propagations (fatten may trigger ext, ext may trigger reportEq, etc..)
			{
				boolean madeChanges = true;
				while (madeChanges) {
					/*
					 *  note:
					 *  cannot fatten to weqcc-fat with current architecture (weq vars on labels become primed currently and we
					 *  don't account for that e.g. in reportWeakEquivalence..)
					 */
					fatten(false);
					madeChanges = reportAllArrayEqualitiesFromWeqGraph();
				}
			}
			thin();

			// 2. do floyd-warshall (triangle-rule), report
			executeFloydWarshallAndReportResultToWeqCc();
			if (!getWeakEquivalenceGraph().hasArrayEqualities()) {
				// status: closed under ext and under triangle --> done
				return;
			}
			reportAllArrayEqualitiesFromWeqGraph();
		}
	}

	public Set<NODE> removeElementAndDependents(final NODE elem, final Set<NODE> elementsToRemove,
			final Map<NODE, NODE> nodeToReplacementNode, final boolean useWeqGpa) {

		for (final NODE etr : elementsToRemove) {
			getWeakEquivalenceGraph().replaceVertex(etr, nodeToReplacementNode.get(etr));
		}

		final Set<NODE> nodesToAddInGpa = getWeakEquivalenceGraph().projectAwaySimpleElementInEdgeLabels(elem);

		assert !useWeqGpa || nodesToAddInGpa.isEmpty() : "we don't allow introduction of new nodes at labels if we"
				+ "are not in the meet-with-WeqGpa case";

		mCongruenceClosure.removeElements(elementsToRemove, nodeToReplacementNode);

		return nodesToAddInGpa;
	}

	public Set<NODE> getNodesToIntroduceBeforeRemoval(final NODE elemToRemove, final Set<NODE> elementsToRemove,
			final Map<NODE, NODE> elemToRemoveToReplacement) {

	    final Set<NODE> replByFwcc = mCongruenceClosure.getNodesToIntroduceBeforeRemoval(elemToRemove, elementsToRemove,
	    		elemToRemoveToReplacement);


		if (!replByFwcc.isEmpty()) {
			/*
			 * We have found a replacement in mCongruenceClosure, this is always a "perfect" replacement, i.e., a node
			 * that is equivalent to elemToRemove.
			 */
			assert replByFwcc.size() == 1;
			assert DataStructureUtils.intersection(
					mCongruenceClosure.getElementCurrentlyBeingRemoved().getRemovedElements(), replByFwcc).isEmpty();
			return replByFwcc;
		}


		final boolean etrIsRemovedBecauseOfAf = elementsToRemove.contains(elemToRemove.getAppliedFunction());
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
		final boolean iToBeRemovedToo = elementsToRemove.contains(elemToRemove.getArgument());
		final NODE jEqualToI =
				mCongruenceClosure.getOtherEquivalenceClassMember(elemToRemove.getArgument(), elementsToRemove);
		if (iToBeRemovedToo && jEqualToI == null) {
			// no way of introducing a b[j] because we cannot find a j (and i is being removed, too..)
			return Collections.emptySet();
		}
		// a node equal to i
		final NODE j = iToBeRemovedToo ? jEqualToI : elemToRemove.getArgument();

		// forall b --Phi(q)-- a
		for (final Entry<NODE, WeakEquivalenceEdgeLabel<NODE, CongruenceClosure<NODE>>> edge
				: getWeakEquivalenceGraph().getAdjacentWeqEdges(elemToRemove.getAppliedFunction()).entrySet()) {
			assert !edge.getKey().equals(elemToRemove.getAppliedFunction());
			if (elementsToRemove.contains(edge.getKey())) {
				// b is also being removed, cannot use it for propagations..
				continue;
			}

			final WeakEquivalenceEdgeLabel<NODE, CongruenceClosure<NODE>> projectedLabel = getWeakEquivalenceGraph()
					.projectEdgeLabelToPoint(edge.getValue(),
							elemToRemove.getArgument(),
							mManager.getAllWeqVarsNodeForFunction(elemToRemove.getAppliedFunction()));

			if (projectedLabel.isTautological()) {
				continue;
			}

			/*
			 *  best case: projectedLabel is inconsistent, this means if we introduce b[i] we can later propagate
			 *  a[i] = b[i], this also means we don't need to introduce any other node
			 */
			if (projectedLabel.isInconsistent()) {
				final NODE bi = mManager.getEqNodeAndFunctionFactory()
						.getOrConstructFuncAppElement(edge.getKey(), j);
				assert !mCongruenceClosure.getElementCurrentlyBeingRemoved().getRemovedElements().contains(bi);
				elemToRemoveToReplacement.put(elemToRemove, bi);
				if (!mCongruenceClosure.hasElement(bi)) {
					assert nodeToAddIsEquivalentToOriginal(bi, elemToRemove);
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
			if (projectedLabel.isTautological()) {
				continue;
			}
			// if a disjunct was ground, the the projectToElem(weqvars) operation should have made it "true"
			assert !projectedLabel.getDisjuncts().stream().anyMatch(l ->
				DataStructureUtils.intersection(l.getAllElements(), mManager.getAllWeqNodes()).isEmpty());


			final NODE bi = mManager.getEqNodeAndFunctionFactory() .getOrConstructFuncAppElement(edge.getKey(), j);

			if (WeqSettings.INTRODUCE_AT_MOST_ONE_NODE_FOR_EACH_REMOVED_NODE) {
				assert !mCongruenceClosure.getElementCurrentlyBeingRemoved().getRemovedElements().contains(bi);
				if (!hasElement(bi)) {
					return Collections.singleton(bi);
				} else {
					return Collections.emptySet();
				}
			}
			assert !mCongruenceClosure.getElementCurrentlyBeingRemoved().getRemovedElements().contains(bi);
			if (!hasElement(bi)) {
				result.add(bi);
			}
		}

		return result;
	}

	private boolean nodeToAddIsEquivalentToOriginal(final NODE nodeToAdd, final NODE elemToRemove) {
//		final WeqCongruenceClosure<NODE> copy = mManager.getFrozenCopy(this);
		final WeqCongruenceClosure<NODE> copy = mManager.copyWeqCc(this, false);
		mManager.addNode(nodeToAdd, copy, true);
		if (copy.getEqualityStatus(nodeToAdd, elemToRemove) != EqualityStatus.EQUAL) {
			assert false;
			return false;
		}
		return true;
	}

	public boolean hasElement(final NODE node) {
		return mCongruenceClosure.hasElement(node);
	}

	@Override
	public boolean isConstrained(final NODE elem) {
		if (mCongruenceClosure.isConstrained(elem)) {
			return true;
		}
		if (getWeakEquivalenceGraph().isConstrained(elem)) {
			return true;
		}
		return false;
	}

	protected void registerNewElement(final NODE elem, final IRemovalInfo<NODE> remInfo) {
		mCongruenceClosure.registerNewElement(elem, remInfo);

		if (isInconsistent()) {
			// nothing more to do
			return;
		}

		if (!elem.isFunctionApplication()) {
			// nothing more to do
			return;
		}

		boolean madeChanges = false;

		/*
		 * roweq
		 *
		 * say elem = a[i], then we attempt to discover all b[j] in exp such that i = j, these are the argccpar of i
		 */
		for (final NODE ccp : mCongruenceClosure.getArgCcPars(getRepresentativeElement(elem.getArgument()))) {
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
			final WeakEquivalenceEdgeLabel<NODE, CongruenceClosure<NODE>> weqEdgeLabelContents =
					getWeakEquivalenceGraph().getEdgeLabel(ccp.getAppliedFunction(), elem.getAppliedFunction());

			final WeakEquivalenceEdgeLabel<NODE, CongruenceClosure<NODE>> projectedLabel = getWeakEquivalenceGraph().projectEdgeLabelToPoint(
					weqEdgeLabelContents,
					ccp.getArgument(),
					mManager.getAllWeqVarsNodeForFunction(ccp.getAppliedFunction()));

			madeChanges |= reportWeakEquivalenceDoOnlyRoweqPropagations(elem,
					ccp,
					projectedLabel);
		}

		if (madeChanges && !CcSettings.DELAY_EXT_AND_DELTA_CLOSURE) {
			extAndTriangleClosure();
//			executeFloydWarshallAndReportResultToWeqCc();
		}
//		assert sanityCheck();
	}

	public boolean hasElements(final NODE... elems) {
		return mCongruenceClosure.hasElements(elems);
	}

	public void registerNewElement(final NODE elem) {
		registerNewElement(elem, null);
	}

	@Override
	public void transformElementsAndFunctions(final Function<NODE, NODE> elemTransformer) {
		assert !isFrozen();
		mCongruenceClosure.transformElementsAndFunctions(elemTransformer);

		getWeakEquivalenceGraph().transformElementsAndFunctions(elemTransformer);
	}

	/**
	 * is a simple element and all the elements that depend on it fully removed?
	 */
	public boolean assertSimpleElementIsFullyRemoved(final NODE elem) {
		for (final NODE e : getAllElements()) {
			if (e.isDependent() && e.getSupportingNodes().contains(elem)) {
				assert false;
				return false;
			}
		}
		return mCongruenceClosure.assertSimpleElementIsFullyRemoved(elem);
	}

	@Override
	public Set<NODE> getAllElements() {
		return mCongruenceClosure.getAllElements();
	}

	@Override
	public boolean assertSingleElementIsFullyRemoved(final NODE elem) {
		if (!getWeakEquivalenceGraph().assertElementIsFullyRemoved(elem)) {
			assert false;
			return false;
		}

		return mCongruenceClosure.assertSingleElementIsFullyRemoved(elem);
	}

	WeqCongruenceClosure<NODE> join(final WeqCongruenceClosure<NODE> other) {
		assert !this.isInconsistent() && !other.isInconsistent() && !this.isTautological() && !other.isTautological()
			: "catch this case in WeqCcManager";

		final WeqCongruenceClosure<NODE> result = mManager.getWeqCongruenceClosure(
				mManager.join(mCongruenceClosure, other.mCongruenceClosure, true),
				mManager.join(getWeakEquivalenceGraph(), other.getWeakEquivalenceGraph(), true),
				true);

		return result;
	}

	WeqCongruenceClosure<NODE> meet(final WeqCongruenceClosure<NODE> other, final boolean inplace) {

		final WeqCongruenceClosure<NODE> result = meetRec(other, inplace);

		if (!CcSettings.DELAY_EXT_AND_DELTA_CLOSURE) {
			result.executeFloydWarshallAndReportResultToWeqCc();
		}
		if (result.isInconsistent() && !inplace) {
			return mManager.getInconsistentWeqCc();
		}
		result.reportAllArrayEqualitiesFromWeqGraph();

		if (result.isInconsistent() && !inplace) {
			return mManager.getInconsistentWeqCc();
		}

		assert result.sanityCheck();
		return result;
	}

	public WeqCongruenceClosure<NODE> meetRec(final CongruenceClosure<NODE> other, final boolean inplace) {
		final WeqCongruenceClosure<NODE> gPaMeet = meetWeqWithCc(other, inplace);
		assert gPaMeet.sanityCheck();
		if (gPaMeet.isInconsistent() && !inplace) {
			return mManager.getInconsistentWeqCc();
		}
		assert gPaMeet.mCongruenceClosure.assertAtMostOneLiteralPerEquivalenceClass();
		assert !this.getWeakEquivalenceGraph().hasArrayEqualities();


		return gPaMeet;
	}


	public WeqCongruenceClosure<NODE> meetRec(final WeqCongruenceClosure<NODE> other, final boolean inplace) {

		final WeqCongruenceClosure<NODE> gPaMeet = meetWeqWithCc(other.mCongruenceClosure, inplace);
		assert gPaMeet.sanityCheck();
		if (gPaMeet.isInconsistent() && !inplace) {
			return mManager.getInconsistentWeqCc();
		}
		assert gPaMeet.mCongruenceClosure.assertAtMostOneLiteralPerEquivalenceClass();
		assert !this.getWeakEquivalenceGraph().hasArrayEqualities();


//		if (!(other instanceof WeqCongruenceClosure)) {
//			return gPaMeet;
//		}

		/*
		 * strategy: conjoin all weq edges of otherCC to a copy of this's weq graph
		 */

		final WeqCongruenceClosure<NODE> newWeqCc = gPaMeet;
		assert newWeqCc.sanityCheck();

		final WeqCongruenceClosure<NODE> otherWeqCc = other;
		assert otherWeqCc.getWeakEquivalenceGraph().sanityCheck();
		assert otherWeqCc.sanityCheck();

		// report all weq edges from other
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE, CongruenceClosure<NODE>>> edge
				: otherWeqCc.getWeakEquivalenceGraph().getEdges().entrySet()) {

//			assert gPaMeet.getAllElements().containsAll(edge.getValue().getAppearingNodes());

			newWeqCc.reportWeakEquivalenceDoOnlyRoweqPropagations(edge.getKey().getOneElement(),
					edge.getKey().getOtherElement(),
					edge.getValue());
			assert newWeqCc.sanityCheck();
		}

		return newWeqCc;
	}

	private WeqCongruenceClosure<NODE> meetWeqWithCc(final CongruenceClosure<NODE> other, final boolean inplace) {
		assert !this.isInconsistent() && !other.isInconsistent();

		final WeqCongruenceClosure<NODE> thisAligned = mManager.addAllElements(this, other.getAllElements(), null,
				inplace);

		for (final Entry<NODE, NODE> eq : other.getSupportingElementEqualities().entrySet()) {
			if (thisAligned.isInconsistent()) {
				return mManager.getInconsistentWeqCc();
			}
			thisAligned.reportEqualityRec(eq.getKey(), eq.getValue());
		}
		for (final Entry<NODE, NODE> deq : other.getElementDisequalities()) {
			if (thisAligned.isInconsistent()) {
				return mManager.getInconsistentWeqCc();
			}
			thisAligned.reportDisequalityRec(deq.getKey(), deq.getValue());
		}
		assert thisAligned.sanityCheck();
		return thisAligned;
	}

	public boolean sanityCheck() {
		if (isInconsistent()) {
			return true;
		}

		if (mIsFrozen != mCongruenceClosure.isFrozen()) {
			assert false;
			return false;
		}

		boolean res = mCongruenceClosure.sanityCheck();
		if (getWeakEquivalenceGraph() != null) {
			res &= getWeakEquivalenceGraph().sanityCheck();
		}

		if (!mMeetWithGpaCase && !isInconsistent()) {
			for (final NODE el : getAllElements()) {
				if (CongruenceClosure.dependsOnAny(el, mManager.getAllWeqPrimedNodes())) {
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
		if (getAllElements().size() < WeqSettings.MAX_NO_ELEMENTS_FOR_VERBOSE_TO_STRING) {
			return toLogString();
		}

		final StringBuilder sb = new StringBuilder();
		sb.append("Partial arrangement:\n");
		sb.append(mCongruenceClosure.toString());
		sb.append("\n");
		if (getWeakEquivalenceGraph() != null) {
			sb.append("Weak equivalences:\n");
			sb.append(getWeakEquivalenceGraph().toString());
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
		sb.append(mCongruenceClosure.toLogString());
		sb.append("\n");
		if (getWeakEquivalenceGraph() != null && !getWeakEquivalenceGraph().isEmpty()) {
			sb.append("Weak equivalences:\n");
			sb.append(getWeakEquivalenceGraph().toLogString());
		} else if (getWeakEquivalenceGraph() != null && getWeakEquivalenceGraph().isEmpty()) {
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
		if (getWeakEquivalenceGraph().hasArrayEqualities()) {
			assert false;
			return false;
		}
		return true;
	}

	public Integer getStatistics(final VPStatistics stat) {
		switch (stat) {
		case MAX_WEQGRAPH_SIZE:
			return getWeakEquivalenceGraph().getNumberOfEdgesStatistic();
		case MAX_SIZEOF_WEQEDGELABEL:
			return getWeakEquivalenceGraph().getMaxSizeOfEdgeLabelStatistic();
		case NO_SUPPORTING_DISEQUALITIES:
			// we have to eliminate symmetric entries
			final HashRelation<NODE, NODE> cleanedDeqs = new HashRelation<>();
			for (final Entry<NODE, NODE> deq : mCongruenceClosure.getElementDisequalities()) {
				if (cleanedDeqs.containsPair(deq.getValue(), deq.getKey())) {
					continue;
				}
				cleanedDeqs.addPair(deq.getKey(), deq.getValue());
			}
			return cleanedDeqs.size();
		case NO_SUPPORTING_EQUALITIES:
			return mCongruenceClosure.getSupportingElementEqualities().size();
		default :
			return VPStatistics.getNonApplicableValue(stat);
		}
	}

	public Set<NODE> collectElementsToRemove(final NODE elem) {
		return mCongruenceClosure.collectElementsToRemove(elem);
	}

	public NODE getOtherEquivalenceClassMember(final NODE node, final Set<NODE> forbiddenSet) {
		return mCongruenceClosure.getOtherEquivalenceClassMember(node, forbiddenSet);
	}

	public boolean addElementRec(final NODE node) {
		final boolean newlyAdded = !mCongruenceClosure.hasElement(node);
		mManager.addNode(node, mCongruenceClosure, true, true);

		if (!newlyAdded) {
			return false;
		}
		registerNewElement(node);
		return true;
	}

	@Override
	public IRemovalInfo<NODE> getElementCurrentlyBeingRemoved() {
		return mCongruenceClosure.getElementCurrentlyBeingRemoved();
	}

	public boolean isRepresentative(final NODE elem) {
		return mCongruenceClosure.isRepresentative(elem);
	}

	public CongruenceClosure<NODE> getCongruenceClosure() {
		return mCongruenceClosure;
	}

	public void setElementCurrentlyBeingRemoved(final IRemovalInfo<NODE> re) {
		mCongruenceClosure.setElementCurrentlyBeingRemoved(re);
	}

	public boolean isDebugMode() {
		return mLogger != null;
	}

	public ILogger getLogger() {
		return mLogger;
	}

	public WeakEquivalenceGraph<NODE, CongruenceClosure<NODE>> getWeakEquivalenceGraph() {
//		assert assertOnlyOneWeqGraph();
//		if (mWeakEquivalenceGraphThin != null) {
//			return mWeakEquivalenceGraphThin;
//		}
//		if (mWeakEquivalenceGraphWeqCcFat != null) {
//			return mWeakEquivalenceGraphWeqCcFat;
//		}
//		if (mWeakEquivalenceGraphThin != null) {
//			return mWeakEquivalenceGraphThin;
//		}
		throw new AssertionError();
	}

	public <DISJUNCT extends ICongruenceClosure<NODE>> WeakEquivalenceGraph<NODE, DISJUNCT> getWeakEquivalenceGraph(
			final DISJUNCT dummyDisjunct) {
		assert assertDietSanity();
		switch (mDiet) {
		case THIN:
			return (WeakEquivalenceGraph<NODE, DISJUNCT>) mWeakEquivalenceGraphThin;
		case CCFAT:
			return (WeakEquivalenceGraph<NODE, DISJUNCT>) mWeakEquivalenceGraphCcFat;
		case WEQCCFAT:
			return (WeakEquivalenceGraph<NODE, DISJUNCT>) mWeakEquivalenceGraphWeqCcFat;
		}
		throw new AssertionError();
	}

	private boolean assertDietSanity() {
		switch (mDiet) {
		case THIN:
			if (mWeakEquivalenceGraphThin == null) {
				assert false;
				return false;
			}
			if (mWeakEquivalenceGraphCcFat != null) {
				assert false;
				return false;
			}
			if (mWeakEquivalenceGraphWeqCcFat != null) {
				assert false;
				return false;
			}
			break;
		case CCFAT:
			if (mWeakEquivalenceGraphThin != null) {
				assert false;
				return false;
			}
			if (mWeakEquivalenceGraphCcFat == null) {
				assert false;
				return false;
			}
			if (mWeakEquivalenceGraphWeqCcFat != null) {
				assert false;
				return false;
			}
			break;
		case WEQCCFAT:
				if (mWeakEquivalenceGraphThin != null) {
				assert false;
				return false;
			}
			if (mWeakEquivalenceGraphCcFat != null) {
				assert false;
				return false;
			}
			if (mWeakEquivalenceGraphWeqCcFat == null) {
				assert false;
				return false;
			}
			break;
		}
		return true;
	}

	@Override
	public boolean sanityCheckOnlyCc() {
		return mCongruenceClosure.sanityCheck();
	}

	@Override
	public boolean sanityCheckOnlyCc(final IRemovalInfo<NODE> remInfo) {
		return mCongruenceClosure.sanityCheck(remInfo);
	}

	public void thin() {
		assert mDiet != Diet.THIN;
		assert assertDietSanity();
		if (mWeakEquivalenceGraphWeqCcFat != null) {
			mWeakEquivalenceGraphThin = mWeakEquivalenceGraphWeqCcFat.thinLabels(this);
			mWeakEquivalenceGraphWeqCcFat = null;
		} else if (mWeakEquivalenceGraphCcFat != null) {
			mWeakEquivalenceGraphThin = mWeakEquivalenceGraphCcFat.thinLabels(this);
			mWeakEquivalenceGraphCcFat = null;
		} else {
			throw new AssertionError();
		}
		mDiet = Diet.THIN;
	}
}

/**
 * Describes the state of the edge labels of the weq graph.
 * (..)
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
enum Diet {
	THIN, CCFAT, WEQCCFAT;
}