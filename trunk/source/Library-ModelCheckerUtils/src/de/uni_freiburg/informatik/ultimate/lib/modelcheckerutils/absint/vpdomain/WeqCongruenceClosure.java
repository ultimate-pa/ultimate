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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain.WeqCcManager.WeqCcBmNames;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.EqualityStatus;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.CcAuxData;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.CcSettings;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.CongruenceClosure;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.IElementRemovalTarget;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.IEqualityReportingTarget;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.IRemovalInfo;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.SetConstraint;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.SetConstraintConjunction;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class WeqCongruenceClosure<NODE extends IEqNodeIdentifier<NODE>>
		implements IEqualityReportingTarget<NODE>, IElementRemovalTarget<NODE> {

	private CongruenceClosure<NODE> mCongruenceClosure;

	// slim version
	private WeakEquivalenceGraph<NODE> mWeakEquivalenceGraphThin;

	private WeakEquivalenceGraph<NODE> mWeakEquivalenceGraphCcFat;
	// private WeakEquivalenceGraph<NODE> mWeakEquivalenceGraphWeqCcFat;

	/**
	 * True iff this WeqCc is a disjunct in a weq label (in contrast to being a "base WeqCc" that is not used inside
	 * another WeqCc)
	 */
	private boolean mIsWeqFatEdgeLabel;

	private boolean mIsFrozen = false;

	/** see {@link #extAndTriangleClosure(boolean)} */
	private boolean mIsClosed = true;

	private final ILogger mLogger;

	private final WeqCcManager<NODE> mManager;

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

		assert mManager.getSettings().omitSanitycheckFineGrained2() || sanityCheck();
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
		mManager = null;
		mLogger = null;
		mIsFrozen = true;
	}

	/**
	 * Create a WeqCC using the given CongruenceClosure as ground partial arrangement (gpa) and the given
	 * WeakEquivalenceGraph.
	 *
	 * @param cc
	 * @param manager
	 */
	public WeqCongruenceClosure(final CongruenceClosure<NODE> cc, final WeakEquivalenceGraph<NODE> weqGraph,
			final WeqCcManager<NODE> manager) {
		assert !cc.isFrozen();

		mLogger = manager.getLogger();
		mCongruenceClosure = manager.copyCcNoRemInfo(cc);

		assert manager != null;
		if (cc.isInconsistent(false)) {
			throw new IllegalArgumentException("use other constructor!");
		}
		mManager = manager;

		/*
		 * we need a fresh instance of WeakEquivalenceGraph here, because we cannot set the link in the weq graph to the
		 * right cc instance..
		 */
		mWeakEquivalenceGraphThin = new WeakEquivalenceGraph<>(this, weqGraph); // , false);
		mDiet = Diet.THIN;

		assert mManager.getSettings().omitSanitycheckFineGrained2() || sanityCheck();
	}

	/**
	 * Makes a copy. May conflate weq edges.
	 *
	 * @param original
	 * @param meetWGpaCase
	 */
	public WeqCongruenceClosure(final WeqCongruenceClosure<NODE> original) {
		mLogger = original.getLogger();
		mManager = original.mManager;
		mCongruenceClosure = mManager.copyCc(original.mCongruenceClosure, true);
		assert !mCongruenceClosure.isFrozen();
		assert original.mManager != null;

		if (// original.mDiet != Diet.TRANSITORY_THIN_TO_WEQCCFAT &&
		original.mDiet != Diet.TRANSITORY_THIN_TO_CCFAT && original.mDiet != Diet.THIN) {
			throw new AssertionError();
		}

		mIsWeqFatEdgeLabel = original.mIsWeqFatEdgeLabel;
		mDiet = original.mDiet;
		mWeakEquivalenceGraphThin = new WeakEquivalenceGraph<>(this, original.mWeakEquivalenceGraphThin);

		assert mManager.getSettings().omitSanitycheckFineGrained2() || sanityCheck();
		assert !mIsFrozen;
	}

	/**
	 *
	 * @return always "true", meaning something might have changed (added just to match the
	 *         {@link IEqualityReportingTarget} interface)
	 */
	@Override
	public boolean addElement(final NODE elem, final boolean omitSanityChecks) {
		assert !isFrozen();
		addElementRec(elem);
		if (!mManager.getSettings().omitSanitycheckFineGrained1()) {
			assert omitSanityChecks || sanityCheck();
		}

		if (!CcSettings.DELAY_EXT_AND_DELTA_CLOSURE) {
			extAndTriangleClosure(omitSanityChecks);
		} else {
			mIsClosed = false;
		}
		reportAllConstraintsFromWeqGraph(omitSanityChecks);

		assert omitSanityChecks || sanityCheck();
		return true;
	}

	public boolean isFrozen() {
		assert isInconsistent(false) || mIsFrozen == mCongruenceClosure.isFrozen();
		return mIsFrozen;
	}

	/**
	 * Call this, when you are sure that this WeqCc is already closed.
	 */
	public void freezeOmitPropagations() {
		// set the flags
		if (mCongruenceClosure != null) {
			mManager.getCcManager().freezeIfNecessary(mCongruenceClosure);
		}
		if (!isInconsistent(false)) {
			getWeakEquivalenceGraph().freezeIfNecessary();
		}
		mIsFrozen = true;

	}

	// @Override
	public void freezeAndClose() {
		mManager.bmStart(WeqCcBmNames.FREEZE_AND_CLOSE);
		assert !mIsFrozen;

		/*
		 * Do all possible propagations that were delayed. Currently: propagations according to the rules ext and delta.
		 */
		extAndTriangleClosure(false);

		freezeOmitPropagations();
		mManager.bmEnd(WeqCcBmNames.FREEZE_AND_CLOSE);
	}

	/**
	 * closes depending on the setting
	 */
	@Override
	public boolean isInconsistent() {
		return isInconsistent(mManager.getSettings().closeBeforeIsInconsistentCheck());
	}

	/**
	 * use this if you want to enforce or avoid closure
	 *
	 * @param close
	 * @return
	 */
	@Override
	public boolean isInconsistent(final boolean close) {
		if (close) {
			mManager.closeIfNecessary(this);
		}
		return mCongruenceClosure == null || mCongruenceClosure.isInconsistent();
	}

	/**
	 * (works in place)
	 *
	 * @param array1
	 * @param array2
	 * @param storeIndex
	 * @param inplace
	 */
	public void reportWeakEquivalence(final NODE array1, final NODE array2, final NODE storeIndex,
			final boolean omitSanityChecks) {
		assert !isFrozen();
		assert array1.hasSameTypeAs(array2);

		mManager.addNode(storeIndex, this, true, true);
		if (!mManager.getSettings().omitSanitycheckFineGrained1()) {
			assert sanityCheck();
		}

		reportWeakEquivalence(array1, array2, mManager.getEdgeLabelForIndex(getWeakEquivalenceGraph(), storeIndex),
				omitSanityChecks);
		assert mManager.getSettings().omitSanitycheckFineGrained2() || sanityCheck();
	}

	/**
	 * (works in place)
	 *
	 * @param array1
	 * @param array2
	 * @param edgeLabel
	 */
	private void reportWeakEquivalence(final NODE array1, final NODE array2,
			final WeakEquivalenceEdgeLabel<NODE> edgeLabel, final boolean omitSanityChecks) {
		assert !isFrozen();
		if (isInconsistent(false)) {
			return;
		}

		reportWeakEquivalenceDoOnlyRoweqPropagations(array1, array2, edgeLabel, omitSanityChecks);

		assert mManager.getSettings().omitSanitycheckFineGrained2() || sanityCheck();
	}

	boolean executeFloydWarshallAndReportResultToWeqCc(final boolean omitSanityChecks) {
		if (isInconsistent(false)) {
			return false;
		}

		WeqCongruenceClosure<NODE> originalCopy = null;
		if (WeqCcManager.areAssertsEnabled() && mManager.mDebug && !mManager.mSkipSolverChecks) {
			originalCopy = mManager.copyWeqCc(this, true);
		}

		boolean fwmc = false;
		final Map<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE>> fwResult =
				getCcWeakEquivalenceGraph().propagateViaTriangleRule();
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE>> fwEdge : fwResult.entrySet()) {
			fwmc |= reportWeakEquivalenceDoOnlyRoweqPropagations(fwEdge.getKey().getOneElement(),
					fwEdge.getKey().getOtherElement(), fwEdge.getValue(), omitSanityChecks);

			if (!mManager.getSettings().omitSanitycheckFineGrained1()) {
				assert omitSanityChecks || sanityCheck();
			}
		}

		assert mManager.checkEquivalence(originalCopy, this);
		assert omitSanityChecks || sanityCheck();
		return fwmc;
	}

	private boolean reportWeakEquivalenceDoOnlyRoweqPropagations(final NODE array1, final NODE array2,
			final WeakEquivalenceEdgeLabel<NODE> edgeLabel, final boolean omitSanityChecks) {
		assert !isFrozen();
		assert !mManager.getSettings().isDeactivateWeakEquivalences();
		assert !array1.dependsOnUntrackedArray();
		assert !array2.dependsOnUntrackedArray();

		if (isInconsistent(false)) {
			return false;
		}

		if (edgeLabel.isTautological()) {
			return false;
		}

		boolean addedNewNode = false;
		addedNewNode |= !mCongruenceClosure.hasElement(array1);
		addedNewNode |= !mCongruenceClosure.hasElement(array2);
		mManager.addNode(array1, this, true, omitSanityChecks);
		mManager.addNode(array2, this, true, omitSanityChecks);

		final WeakEquivalenceEdgeLabel<NODE> strengthenedEdgeLabel;
		{
			final NODE array1Rep = mCongruenceClosure.getRepresentativeElement(array1);
			final NODE array2Rep = mCongruenceClosure.getRepresentativeElement(array2);

			if (array1Rep == array2Rep) {
				// no need to have a weq edge from the node to itself
				return addedNewNode;
			}

			final boolean reportedNewWeq = getCcWeakEquivalenceGraph().reportWeakEquivalence(array1Rep, array2Rep,
					edgeLabel, omitSanityChecks);

			if (!reportedNewWeq) {
				// nothing to propagate
				return addedNewNode;
			}

			strengthenedEdgeLabel = getCcWeakEquivalenceGraph().getEdgeLabel(array1Rep, array2Rep);

			if (strengthenedEdgeLabel == null) {
				// edge became "false";
				throw new AssertionError(
						"TODO : check this case, this does not happen, right? (and the comment above is "
								+ "nonsense..)");
			}
		}

		if (isInconsistent(false)) {
			return true;
		}

		{

			final NODE array1Rep = mCongruenceClosure.getRepresentativeElement(array1);
			final NODE array2Rep = mCongruenceClosure.getRepresentativeElement(array2);

			CongruenceClosure.constantAndMixFunctionTreatmentOnAddEquality(array1Rep, array2Rep,
					mCongruenceClosure.getEquivalenceClass(array1), mCongruenceClosure.getEquivalenceClass(array2),
					mCongruenceClosure.getAuxData(), n -> mManager.addNode(n, this, true, true), this);
		}

		/*
		 * roweq propagations
		 *
		 * look for fitting c[i], d[j] with i ~ j, array1 ~ c, array2 ~ d
		 */
		{
			// picking the reps again, because propagations may have changed them
			final NODE array1Rep = mCongruenceClosure.getRepresentativeElement(array1);
			final NODE array2Rep = mCongruenceClosure.getRepresentativeElement(array2);

			final Collection<NODE> ccps1 = mCongruenceClosure.getAuxData().getAfCcPars(array1Rep);
			final Collection<NODE> ccps2 = mCongruenceClosure.getAuxData().getAfCcPars(array2Rep);
			for (final NODE ccp1 : ccps1) {
				if (!mCongruenceClosure.hasElements(ccp1, ccp1.getArgument(), ccp1.getAppliedFunction())) {
					continue;
				}
				for (final NODE ccp2 : ccps2) {
					if (isInconsistent(false)) {
						return true;
					}

					if (!mCongruenceClosure.hasElements(ccp2, ccp2.getArgument(), ccp2.getAppliedFunction())) {
						continue;
					}

					if (mCongruenceClosure.getEqualityStatus(ccp1.getArgument(),
							ccp2.getArgument()) != EqualityStatus.EQUAL) {
						continue;
					}
					/*
					 * i ~ j holds propagate array1[i] -- -- array2[j] (note that this adds the arrayX[Y] nodes,
					 * possibly -- EDIT: not..)
					 */
					final WeakEquivalenceEdgeLabel<NODE> projectedLabel =
							getCcWeakEquivalenceGraph().projectEdgeLabelToPoint(strengthenedEdgeLabel,
									ccp1.getArgument(), mManager.getAllWeqVarsNodeForFunction(array1));

					// recursive call
					reportWeakEquivalenceDoOnlyRoweqPropagations(ccp1, ccp2, projectedLabel, omitSanityChecks);
				}
			}
		}

		{
			// picking the reps again, because propagations may have changed them
			final NODE array1Rep = mCongruenceClosure.getRepresentativeElement(array1);
			final NODE array2Rep = mCongruenceClosure.getRepresentativeElement(array2);
			/*
			 * roweq-1 propagations
			 */
			final Set<Entry<NODE, NODE>> array1RepCcChildren =
					mCongruenceClosure.getAuxData().getCcChildren(array1Rep).entrySet();
			final Set<Entry<NODE, NODE>> array2RepCcChildren =
					mCongruenceClosure.getAuxData().getCcChildren(array2Rep).entrySet();

			for (final Entry<NODE, NODE> ccc1 : array1RepCcChildren) {
				if (ccc1.getKey().dependsOnUntrackedArray()) {
					continue;
				}

				for (final Entry<NODE, NODE> ccc2 : array2RepCcChildren) {
					if (isInconsistent(false)) {
						return true;
					}

					if (ccc2.getKey().dependsOnUntrackedArray()) {
						continue;
					}

					if (mCongruenceClosure.getEqualityStatus(ccc1.getValue(),
							ccc2.getValue()) != EqualityStatus.EQUAL) {
						continue;
					}

					final WeakEquivalenceEdgeLabel<NODE> shiftedLabelWithException =
							getCcWeakEquivalenceGraph().shiftLabelAndAddException(strengthenedEdgeLabel,
									ccc1.getValue(), mManager.getAllWeqVarsNodeForFunction(ccc1.getKey()));

					// recursive call
					reportWeakEquivalenceDoOnlyRoweqPropagations(ccc1.getKey(), ccc2.getKey(),
							shiftedLabelWithException, omitSanityChecks);
				}

			}
		}

		// constArrayWeqProp(array1, array2, edgeLabel);

		// assert sanityCheck();
		return true;
	}

	/**
	 * propagation rule: a--(a[q] in L)--(const l), a[i] in exp ==> a[i] in L cup {l}
	 *
	 * TODO: this rule might be obsolete because of a more general rule involving set constraints and weak equivalences
	 */
	private void constArrayWeqProp(final NODE array1, final NODE array2,
			final WeakEquivalenceEdgeLabel<NODE> edgeLabel) {
		// picking the reps again, because propagations may have changed them
		final NODE array1Rep = mCongruenceClosure.getRepresentativeElement(array1);
		final NODE array2Rep = mCongruenceClosure.getRepresentativeElement(array2);

		final NODE nonConstantArray;
		final NODE constantArray;
		if (array1Rep.isConstantFunction()) {
			assert !array2Rep.isConstantFunction() : "?";
			constantArray = array1Rep;
			nonConstantArray = array2Rep;
		} else if (array2Rep.isConstantFunction()) {
			assert !array1Rep.isConstantFunction() : "?";
			constantArray = array2Rep;
			nonConstantArray = array1Rep;
		} else {
			constantArray = null;
			nonConstantArray = null;
		}

		// collect nodes of the form a[i] according to the rule that are present currently
		Collection<NODE> aIs = null;
		Set<SetConstraint<NODE>> containsConstraint = null;
		if (nonConstantArray != null) {
			aIs = mCongruenceClosure.getFuncAppsWithFunc(nonConstantArray);

			if (!aIs.isEmpty()) {
				final NODE sampleAi = aIs.iterator().next();
				// node that corresponds to a[q] in the rule
				// final NODE aQ = sampleAi.replaceArgument(
				// mManager.getWeqVariableNodeForDimension(0, sampleAi.getArgument().getSort()));
				final NODE aQ = mManager.getEqNodeAndFunctionFactory().getFuncAppElement(nonConstantArray,
						mManager.getWeqVariableNodeForDimension(0, sampleAi.getArgument().getSort()), true);

				containsConstraint = edgeLabel.getContainsConstraintForElement(aQ);
				assert containsConstraint == null || !mManager.getCcManager().getSetConstraintManager()
						.isInconsistent(containsConstraint) : "uncaught inconsistent case";
			}
		}

		if (constantArray != null && !aIs.isEmpty() && containsConstraint != null) {

			final NODE constantArrayConstant = constantArray.getConstantFunctionValue();
			assert constantArrayConstant.isLiteral();

			// do propagations
			for (final NODE aI : aIs) {
				if (mCongruenceClosure.getEquivalenceClass(aI).stream().anyMatch(n -> n.isLiteral())) {
					// aI is already equal to a literal -- reporting a set constraint will not strengthen that
					continue;
				}

				// construct L cup {l}
				final Set<SetConstraint<NODE>> newLiteralSet = mManager.getCcManager().getSetConstraintManager().join(
						mCongruenceClosure.getLiteralSetConstraints(), containsConstraint,
						Collections.singleton(mManager.getCcManager().getSetConstraintManager()
								.buildSetConstraint(Collections.singleton(constantArrayConstant))));

				mCongruenceClosure.reportContainsConstraint(aI, newLiteralSet);
			}
		}
	}

	/**
	 * (works in place)
	 *
	 * @param node1
	 * @param node2
	 * @param omitSanityChecks
	 * @return
	 */
	public boolean reportEquality(final NODE node1, final NODE node2, final boolean omitSanityChecks) {
		assert !isFrozen();
		if (!mManager.getSettings().omitSanitycheckFineGrained1()) {
			assert omitSanityChecks || sanityCheck();
		}

		final boolean madeChanges = reportEqualityRec(node1, node2);
		if (!CcSettings.DELAY_EXT_AND_DELTA_CLOSURE) {
			executeFloydWarshallAndReportResultToWeqCc(omitSanityChecks);
		} else {
			mIsClosed = false;
		}
		assert mManager.getSettings().omitSanitycheckFineGrained2() || omitSanityChecks || sanityCheck();
		return madeChanges;
	}

	/**
	 * (works in place)
	 *
	 * @param node1
	 * @param node2
	 * @return
	 */
	@Override
	public boolean reportEqualityRec(final NODE node1, final NODE node2) {
		assert !isFrozen();
		assert node1.hasSameTypeAs(node2);
		if (isInconsistent(false)) {
			throw new IllegalStateException();
		}

		boolean freshElem = false;
		freshElem |= !mCongruenceClosure.hasElement(node1);
		freshElem |= !mCongruenceClosure.hasElement(node2);
		mManager.addNode(node1, this, true, true);
		mManager.addNode(node2, this, true, true);
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
		 * through sanityCheck()) before doing the recursive calls for the fwcc and bwcc propagations) in particular we
		 * need to do getWeakEquivalenceGraph().updateforNewRep(..)
		 */
		final Pair<HashRelation<NODE, NODE>, HashRelation<NODE, NODE>> propInfo =
				mCongruenceClosure.doMergeAndComputePropagations(node1, node2);
		if (propInfo == null) {
			// this became inconsistent through the merge
			return true;
		}

		final NODE newRep = getRepresentativeElement(node1);
		getWeakEquivalenceGraph().updateForNewRep(node1OldRep, node2OldRep, newRep);

		if (isInconsistent(false)) {
			return true;
		}

		CongruenceClosure.doFwccAndBwccPropagationsFromMerge(propInfo, this);
		if (isInconsistent(false)) {
			return true;
		}

		if (!mManager.getSettings().isDeactivateWeakEquivalences()
				&& (!node1.dependsOnUntrackedArray() && !node2.dependsOnUntrackedArray())) {
			// assert !node1.dependsOnUntrackedArray() && !node2.dependsOnUntrackedArray()
			// : "user must mark arrays correctly";
			doRoweqPropagationsOnMerge(node1, node2, node1OldRep, node2OldRep, oldAuxData, true);
		}

		if (isInconsistent(false)) {
			return true;
		}

		if (mManager.getSettings().isAlwaysReportChangeToGpa()) {
			// ext
			reportGpaChangeToWeqGraphAndPropagateArrayEqualities(
					(final CongruenceClosure<NODE> cc) -> cc.reportEqualityRec(node1, node2));
		}

		return true;
	}

	public NODE getRepresentativeElement(final NODE elem) {
		return mCongruenceClosure.getRepresentativeElement(elem);
	}

	/**
	 * When we merge two nodes in the weq graph this may trigger propagations in several ways.
	 * <li>first, the roweq and roweq-1 rules have a condition "i~j" in their antecedents, we call these the explicit
	 * triggers
	 * <li>second the weak equivalence condition of the roweq and roweq-1 rules may be triggered by a merge, because
	 * something "of the right form" may be added to a weak equivalence class which had only elements "of the wrong
	 * form" for example.
	 *
	 * @param node1
	 * @param node2
	 * @param node1OldRep
	 * @param node2OldRep
	 * @param oldAuxData
	 * @param b
	 */
	private void doRoweqPropagationsOnMerge(final NODE node1, final NODE node2, final NODE node1OldRep,
			final NODE node2OldRep, final CcAuxData<NODE> oldAuxData, final boolean omitSanityChecks) {
		if (isInconsistent(false)) {
			return;
		}

		/*
		 * there are three types of propagations related to weak equivalences, corresponding to the rules ext, roweq and
		 * roweq-1
		 */

		/*
		 * the merge may collapse two nodes in the weak equivalence graph (which may trigger propagations)
		 */
		// (recursive call)
		// EDIT: adding an edge between nodes that are being merged is problematic algorithmically
		// instead do the rule roweqMerge (which models the consequence of the below a -- false -- b edge, together
		// with fwcc), doing it in an extra procedure..
		// goOn |= reportWeakEquivalenceDoOnlyRoweqPropagations(node1OldRep, node2OldRep, Collections.emptyList());
		// we will treat roweqMerge during the other propagations below as it need similar matching..

		for (final Entry<NODE, NODE> ccc1 : oldAuxData.getCcChildren(node1OldRep)) {
			// don't propagate something that uses the currently removed element
			final NODE ccc1AfReplaced = ccc1.getKey();
			final NODE ccc1ArgReplaced = ccc1.getValue();
			if (ccc1AfReplaced == null || ccc1ArgReplaced == null) {
				continue;
			}
			if (ccc1AfReplaced.dependsOnUntrackedArray() || ccc1ArgReplaced.dependsOnUntrackedArray()) {
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
				final CongruenceClosure<NODE> qUnequalI =
						mManager.getSingleDisequalityCc(firstWeqVar, ccc1ArgReplaced, true);

				reportWeakEquivalenceDoOnlyRoweqPropagations(ccc1AfReplaced, ccc2AfReplaced,
						mManager.getSingletonEdgeLabel(getWeakEquivalenceGraph(), qUnequalI), omitSanityChecks);
			}
		}

		/*
		 * roweq, roweq-1 (1)
		 *
		 * node1 = i, node2 = j in the paper version of the rule
		 */
		for (final NODE ccp1 : oldAuxData.getArgCcPars(node1OldRep)) {
			for (final NODE ccp2 : oldAuxData.getArgCcPars(node2OldRep)) {
				/*
				 * ccp1 = a[i'], ccp2 = b[j'] in the rule, where i'~i, j'~j, before the merge that is currently
				 * happening
				 */

				if (!ccp1.getSort().equals(ccp2.getSort())) {
					continue;
				}

				/*
				 * roweq, explicit trigger, i.e., i'~j' && a--phi(q)--b ==> a[i']--phi(i')--b[j'] (the current merge
				 * establishes i'~j')
				 */
				final WeakEquivalenceEdgeLabel<NODE> aToBLabel =
						getCcWeakEquivalenceGraph().getEdgeLabel(ccp1.getAppliedFunction(), ccp2.getAppliedFunction());
				final WeakEquivalenceEdgeLabel<NODE> projectedLabel =
						getCcWeakEquivalenceGraph().projectEdgeLabelToPoint(aToBLabel, ccp1.getArgument(),
								mManager.getAllWeqVarsNodeForFunction(ccp1.getAppliedFunction()));
				// recursive call
				if (!ccp1.dependsOnUntrackedArray() && !ccp2.dependsOnUntrackedArray()) {
					reportWeakEquivalenceDoOnlyRoweqPropagations(ccp1, ccp2, projectedLabel, omitSanityChecks);
				}

				/*
				 * roweq-1, explicit trigger, i.e., i'~j' && a[i']--phi(q)--b[j'] ==> a--(q!=i' \/ phi(q+))--b (the
				 * current merge establishes i'~j')
				 */
				final WeakEquivalenceEdgeLabel<NODE> aiToBjLabel = getCcWeakEquivalenceGraph().getEdgeLabel(ccp1, ccp2);
				final WeakEquivalenceEdgeLabel<NODE> shiftedLabelWithException =
						getCcWeakEquivalenceGraph().shiftLabelAndAddException(aiToBjLabel, node1,
								mManager.getAllWeqVarsNodeForFunction(ccp1.getAppliedFunction()));
				// recursive call
				if (!ccp1.getAppliedFunction().dependsOnUntrackedArray()
						&& !ccp2.getAppliedFunction().dependsOnUntrackedArray()) {
					reportWeakEquivalenceDoOnlyRoweqPropagations(ccp1.getAppliedFunction(), ccp2.getAppliedFunction(),
							shiftedLabelWithException, omitSanityChecks);
				}

				/*
				 * roweqMerge --> a special case of roweq-1 (or if you will the combination of roweq-1 and
				 * strongtoweak), where the weak equivalence is actually strong, i.e. the label is "false" e.g.
				 * a[i']~b[j'] ==> a--(q!=i)--b
				 */
				if (getEqualityStatus(ccp1, ccp2) == EqualityStatus.EQUAL
						&& !ccp1.getAppliedFunction().dependsOnUntrackedArray()
						&& !ccp2.getAppliedFunction().dependsOnUntrackedArray()) {
					// we have node1 = i, node2 = j, ccp1 = a[i], ccp2 = b[j]
					final NODE firstWeqVar = mManager.getAllWeqVarsNodeForFunction(ccp1.getAppliedFunction()).get(0);
					assert mManager.getAllWeqVarsNodeForFunction(ccp1.getAppliedFunction())
							.equals(mManager.getAllWeqVarsNodeForFunction(ccp2.getAppliedFunction()));
					assert getEqualityStatus(ccp2.getArgument(),
							ccp1.getArgument()) == EqualityStatus.EQUAL : " propagation is only allowed if i = j";

					final CongruenceClosure<NODE> qUnequalI =
							mManager.getSingleDisequalityCc(firstWeqVar, ccp1.getArgument(), true);

					reportWeakEquivalenceDoOnlyRoweqPropagations(ccp1.getAppliedFunction(), ccp2.getAppliedFunction(),
							mManager.getSingletonEdgeLabel(getWeakEquivalenceGraph(), qUnequalI), omitSanityChecks);
				}
			}

		}
		// assert sanityCheck();

		/*
		 * roweq-1(2)
		 *
		 * a somewhat more intricate case: ("implicit triggers")
		 *
		 * the added equality may trigger the pattern matching on the weak equivalence condition of the roweq-1 rule
		 */
		otherRoweqPropOnMerge(node1OldRep, oldAuxData, omitSanityChecks);
		otherRoweqPropOnMerge(node2OldRep, oldAuxData, omitSanityChecks);
	}

	public EqualityStatus getEqualityStatus(final NODE node1, final NODE node2) {
		return mCongruenceClosure.getEqualityStatus(node1, node2);
	}

	private boolean otherRoweqPropOnMerge(final NODE nodeOldRep, final CcAuxData<NODE> oldAuxData,
			final boolean omitSanityChecks) {
		boolean madeChanges = false;
		for (final Entry<NODE, NODE> ccc : oldAuxData.getCcChildren(nodeOldRep)) {
			// ccc = (b,j) , as in b[j]
			for (final Entry<NODE, WeakEquivalenceEdgeLabel<NODE>> edgeAdjacentToNode : getCcWeakEquivalenceGraph()
					.getAdjacentWeqEdges(nodeOldRep).entrySet()) {
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

					final WeakEquivalenceEdgeLabel<NODE> shiftedLabelWithException =
							getCcWeakEquivalenceGraph().shiftLabelAndAddException(phi, ccc.getValue(),
									mManager.getAllWeqVarsNodeForFunction(ccc.getKey()));
					// recursive call
					madeChanges |= reportWeakEquivalenceDoOnlyRoweqPropagations(ccc.getKey(), aj.getKey(),
							shiftedLabelWithException, omitSanityChecks);
				}
			}

			/*
			 * roweqMerge rule: not necessary here as we used ccpar in do doRoweqPropagationsOnMerge
			 */
		}
		return madeChanges;
	}

	/**
	 *
	 * @param omitSanityChecks
	 * @return true iff any constraints were added
	 */
	boolean reportAllConstraintsFromWeqGraph(final boolean omitSanityChecks) {
		if (!mManager.getSettings().omitSanitycheckFineGrained1()) {
			assert omitSanityChecks || sanityCheck();
		}

		if (isInconsistent(false)) {
			assert sanityCheck();
			return false;
		}

		boolean madeChanges = false;
		while (getWeakEquivalenceGraph().hasConstraintsToReport()) {
			final WeakEquivalenceGraph<NODE>.ConstraintFromWeqGraph aeq =
					getWeakEquivalenceGraph().pollStoredConstraintAndRemoveRelatedWeqEdge();
			if (aeq.isIsArrayEquality()) {
				madeChanges |=
						reportEquality(aeq.getEquality().getFirst(), aeq.getEquality().getSecond(), omitSanityChecks);
			} else if (aeq.isSetConstraint()) {
				// TODO: reportContainsConstraint does not report if changes have been made --> this overapproximates..
				madeChanges = true;

				reportContainsConstraint(aeq.getSetConstraint().getFirst(),
						Collections.singleton(aeq.getSetConstraint().getSecond()));
			} else if (aeq.isDummyConstraint()) {
				// nothing to do corresponding weq edge has already been removed
			} else {
				throw new AssertionError();
			}

			if (isInconsistent(false)) {
				assert sanityCheck();
				assert madeChanges;
				return true;
			}
			if (!mManager.getSettings().omitSanitycheckFineGrained1()) {
				assert omitSanityChecks || sanityCheck();
			}
		}

		assert omitSanityChecks || sanityCheck();
		assert weqGraphFreeOfArrayEqualities();
		return madeChanges;
	}

	public boolean reportDisequality(final NODE node1, final NODE node2) {
		assert !isFrozen();
		final boolean result = reportDisequalityRec(node1, node2);
		assert mManager.getSettings().omitSanitycheckFineGrained2() || sanityCheck();
		return result;
	}

	@Override
	public boolean reportDisequalityRec(final NODE node1, final NODE node2) {
		boolean madeChanges = false;

		madeChanges |= mCongruenceClosure.reportDisequalityRec(node1, node2);

		if (!madeChanges) {
			return false;
		}

		if (isInconsistent(false)) {
			// no need for further propagations
			return true;
		}

		if (mManager.getSettings().isAlwaysReportChangeToGpa()) {
			reportGpaChangeToWeqGraphAndPropagateArrayEqualities(
					(final CongruenceClosure<NODE> cc) -> cc.reportDisequalityRec(node1, node2));
			assert weqGraphFreeOfArrayEqualities();
		}

		if (isInconsistent(false)) {
			// omit sanity checks
			return true;
		}

		return true;
	}

	@Override
	public void reportContainsConstraint(final NODE elem, final Set<NODE> literalSet) {
		mCongruenceClosure.reportContainsConstraint(elem, literalSet);
		if (mManager.getSettings().isAlwaysReportChangeToGpa()) {
			throw new AssertionError("not implemented");
		}

	}

	public void reportContainsConstraint(final NODE elem, final Collection<SetConstraint<NODE>> setCc) {
		mCongruenceClosure.reportContainsConstraint(elem, setCc);
		if (mManager.getSettings().isAlwaysReportChangeToGpa()) {
			throw new AssertionError("not implemented");
		}

	}

	/**
	 * Updates the weq-graph wrt. a change in the ground partial arrangement. Immediately propagates array equalities if
	 * some have occurred.
	 *
	 * Implements the rule "ext".
	 *
	 * This is only called when the option {@link WeqSettings#isAlwaysReportChangeToGpa()} is set. Probably we will not
	 * use this in the future, so this method is deprecated and should not be used in other cases.
	 *
	 * @param reporter
	 * @return
	 */
	@Deprecated
	private boolean
			reportGpaChangeToWeqGraphAndPropagateArrayEqualities(final Predicate<CongruenceClosure<NODE>> reporter) {
		assert sanityCheck();
		if (isInconsistent(false)) {
			return false;
		}
		boolean madeChanges = false;
		madeChanges |= getCcWeakEquivalenceGraph().reportChangeInGroundPartialArrangement(reporter);
		reportAllConstraintsFromWeqGraph(false);
		assert sanityCheck();
		return madeChanges;
	}

	public boolean isTautological() {
		if (mCongruenceClosure == null) {
			return false;
		}
		return mCongruenceClosure.isTautological() && getWeakEquivalenceGraph().isEmpty();
	}

	public boolean isStrongerThan(final WeqCongruenceClosure<NODE> other) {
		assert this.isClosed() && other.isClosed() : "caller ensures this, right?";
		assert this.getAllElements().equals(other.getAllElements());

		if (this.isInconsistent()) {
			return true;
		}
		if (other.isTautological()) {
			return true;
		}
		if (this.isTautological()) {
			return false;
		}
		if (other.isInconsistent()) {
			return false;
		}

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
	 * expensive and not implemented in a generic way, so it can only be used for a more precise projectAway operation.
	 *
	 * @param useWeqGpa
	 */
	// public void fatten(final boolean useWeqGpa) {
	public void fatten() {
		assert !isFrozen();

		if (this.isInconsistent(false)) {
			return;
		}

		switch (mDiet) {
		case THIN:
		case TRANSITORY_THIN_TO_CCFAT:
			// this case may occur for a weqCc that labels an weq edge (when the base weqCc has diet WEQCCFAT)
			// case TRANSITORY_THIN_TO_WEQCCFAT:
			mDiet = Diet.TRANSITORY_THIN_TO_CCFAT;
			break;
		case CCFAT:
			mDiet = Diet.TRANSITORY_CCREFATTEN;
			break;
		// case WEQCCFAT:
		// mDiet = Diet.TRANSITORY_WEQCCREFATTEN;
		// break;
		default:
			throw new IllegalStateException();
		}

		// if (useWeqGpa) {
		// mWeakEquivalenceGraphWeqCcFat =
		// getWeakEquivalenceGraph().meetEdgeLabelsWithWeqGpaBeforeRemove(this,
		// // get a modifiable copy because freezing would trigger this closure recursively
		// mManager.copyWeqCc(this, true));
		// mWeakEquivalenceGraphThin = null;
		// mDiet = Diet.WEQCCFAT;
		//// assert mWeakEquivalenceGraphWeqCcFat.assertAllEdgeLabelsHaveWeqFatFlagSet(); //holds, but check is
		// redundant
		// } else {
		mWeakEquivalenceGraphCcFat = getWeakEquivalenceGraph().ccFattenEdgeLabels();
		mWeakEquivalenceGraphThin = null;
		mDiet = Diet.CCFAT;
		// }
		assert mManager.getSettings().omitSanitycheckFineGrained2() || sanityCheck();
	}

	/**
	 * All but two propagation rules from the reduction operator are executed immediately when a constraint is updated.
	 * The two exceptions are the rules ext and triangle. This method saturates under those two rules, and thus ensures
	 * full closure of the constraint.
	 * <p>
	 * (Calling this method is rather expensive.)
	 *
	 * @param omitSanityChecks
	 */
	public void extAndTriangleClosure(final boolean omitSanityChecks) {
		if (mIsClosed) {
			// nothing to do
			return;
		}

		mManager.bmStart(WeqCcBmNames.EXT_AND_TRIANGLE_CLOSURE);

		WeqCongruenceClosure<NODE> originalCopy = null;
		if (WeqCcManager.areAssertsEnabled() && mManager.mDebug && !mManager.mSkipSolverChecks) {
			originalCopy = mManager.copyWeqCc(this, true);
		}

		int loopCtr = 0;
		final int loopBound = 10;
		while (loopCtr++ < loopBound) {
			if (mManager.isDebugMode()) {
				mManager.getLogger().debug("ext and triangle closure, loop iteration #" + loopCtr);
			}

			// 1. fatten, then saturate propagations (fatten may trigger ext, ext may trigger reportEq, etc..)
			{
				boolean madeChanges = true;
				while (madeChanges) {
					if (this.isInconsistent(false)) {
						assert mManager.checkEquivalence(originalCopy, this);
						mIsClosed = true;
						mManager.bmEnd(WeqCcBmNames.EXT_AND_TRIANGLE_CLOSURE);
						return;
					}

					/*
					 * note: cannot fatten to weqcc-fat with current architecture (weq vars on labels become primed
					 * currently and we don't account for that e.g. in reportWeakEquivalence..)
					 */
					assert omitSanityChecks || sanityCheck();
					fatten();
					madeChanges = reportAllConstraintsFromWeqGraph(omitSanityChecks);
				}
			}
			thin();
			// assert getWeakEquivalenceGraph().sanityCheckWithoutNodesComparison();
			assert sanityCheck();

			// 2. do floyd-warshall (triangle-rule), report
			executeFloydWarshallAndReportResultToWeqCc(omitSanityChecks);
			if (!getWeakEquivalenceGraph().hasConstraintsToReport()) {
				// status: closed under ext and under triangle --> done
				assert mManager.checkEquivalence(originalCopy, this);

				mIsClosed = true;
				mManager.bmEnd(WeqCcBmNames.EXT_AND_TRIANGLE_CLOSURE);
				return;
			}
			reportAllConstraintsFromWeqGraph(omitSanityChecks);
		}

	}

	public Set<NODE> removeElementAndDependents(final NODE elem, final Set<NODE> elementsToRemove,
			final Map<NODE, NODE> nodeToReplacementNode) {
		// not the case (see caller, if we close fully after addNodesToKeep, we loose performance massively)
		// assert this.isClosed();

		for (final NODE etr : elementsToRemove) {
			getWeakEquivalenceGraph().replaceVertex(etr, nodeToReplacementNode.get(etr));
		}

		final Set<NODE> nodesToAddInGpa = getWeakEquivalenceGraph().projectAwaySimpleElementInEdgeLabels(elem);

		assert nodesToAddInGpa.isEmpty() : "we don't allow introduction of new nodes at labels if we"
				+ "are not in the meet-with-WeqGpa case";

		mCongruenceClosure.removeElements(elementsToRemove, nodeToReplacementNode);

		return nodesToAddInGpa;
	}

	@Override
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
			assert DataStructureUtils
					.intersection(mCongruenceClosure.getElementCurrentlyBeingRemoved().getRemovedElements(), replByFwcc)
					.isEmpty();
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
		for (final Entry<NODE, WeakEquivalenceEdgeLabel<NODE>> edge : getCcWeakEquivalenceGraph()
				.getAdjacentWeqEdges(elemToRemove.getAppliedFunction()).entrySet()) {
			assert !edge.getKey().equals(elemToRemove.getAppliedFunction());
			if (elementsToRemove.contains(edge.getKey())) {
				// b is also being removed, cannot use it for propagations..
				continue;
			}

			final WeakEquivalenceEdgeLabel<NODE> projectedLabel =
					getCcWeakEquivalenceGraph().projectEdgeLabelToPoint(edge.getValue(), elemToRemove.getArgument(),
							mManager.getAllWeqVarsNodeForFunction(elemToRemove.getAppliedFunction()));

			if (projectedLabel.isTautological()) {
				continue;
			}

			/*
			 * best case: projectedLabel is inconsistent, this means if we introduce b[i] we can later propagate a[i] =
			 * b[i], this also means we don't need to introduce any other node
			 */
			if (projectedLabel.isInconsistent()) {
				final NODE bi = mManager.getEqNodeAndFunctionFactory().getOrConstructFuncAppElement(edge.getKey(), j);
				assert !mCongruenceClosure.getElementCurrentlyBeingRemoved().getRemovedElements().contains(bi);
				elemToRemoveToReplacement.put(elemToRemove, bi);
				if (!mCongruenceClosure.hasElement(bi)) {
					assert assertNodeToAddIsEquivalentToOriginal(bi, elemToRemove);
					return Collections.singleton(bi);
				}
				return Collections.emptySet();
			}

			/*
			 * if there is a disjunct in projectedLabel that does not depend on any weq var, we don't introduce a new
			 * node (we would get a weak equivalence with a ground disjunct EDIT: this case should be treatable via
			 * check for tautology (see also assert below)
			 */
			if (projectedLabel.isTautological()) {
				continue;
			}
			// // if a disjunct was ground, the the projectToElem(weqvars) operation should have made it "true"
			// assert mDiet != Diet.THIN || !projectedLabel.getDisjuncts().stream().anyMatch(l ->
			// DataStructureUtils.intersection(l.getAllElements(), mManager.getAllWeqNodes()).isEmpty());

			final NODE bi = mManager.getEqNodeAndFunctionFactory().getOrConstructFuncAppElement(edge.getKey(), j);

			if (mManager.getSettings().isIntroduceAtMostOneNodeForEachRemovedNode()) {
				assert !mCongruenceClosure.getElementCurrentlyBeingRemoved().getRemovedElements().contains(bi);
				if (!hasElement(bi)) {
					return Collections.singleton(bi);
				}
				return Collections.emptySet();
			}
			assert !mCongruenceClosure.getElementCurrentlyBeingRemoved().getRemovedElements().contains(bi);
			if (!hasElement(bi)) {
				result.add(bi);
			}
		}

		return result;
	}

	private boolean assertNodeToAddIsEquivalentToOriginal(final NODE nodeToAdd, final NODE elemToRemove) {
		final WeqCongruenceClosure<NODE> copy = mManager.copyWeqCc(this, true);
		mManager.addNode(nodeToAdd, copy, true, true);
		if (copy.getEqualityStatus(nodeToAdd, elemToRemove) != EqualityStatus.EQUAL) {
			assert false;
			return false;
		}
		return true;
	}

	@Override
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

	private void registerNewElement(final NODE elem) {

		if (isInconsistent(false)) {
			// nothing more to do
			return;
		}

		if (!elem.isFunctionApplication()) {
			// nothing more to do
			return;
		}

		boolean madeChanges = false;

		if (mManager.getSettings().isDeactivateWeakEquivalences() || elem.dependsOnUntrackedArray()) {
			return;
		}

		{
			CongruenceClosure.constantFunctionTreatmentOnAddElement(elem,
					// (e1, e2) -> mManager.reportEquality(this, e1, e2, true),
					// e -> mManager.addNode(e, this, true, true),
					getWeakEquivalenceGraph().getAdjacentWeqEdges(elem.getAppliedFunction()).keySet(), this);
			CongruenceClosure.mixFunctionTreatmentOnAddElement(elem,
					(e, lits) -> mManager.reportContainsConstraint(e, lits, this, true),
					e -> mManager.addNode(e, this, true, true),
					getWeakEquivalenceGraph().getAdjacentWeqEdges(elem.getAppliedFunction()).keySet());
		}

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
			final WeakEquivalenceEdgeLabel<NODE> weqEdgeLabelContents =
					getCcWeakEquivalenceGraph().getEdgeLabel(ccp.getAppliedFunction(), elem.getAppliedFunction());

			final WeakEquivalenceEdgeLabel<NODE> projectedLabel =
					getCcWeakEquivalenceGraph().projectEdgeLabelToPoint(weqEdgeLabelContents, ccp.getArgument(),
							mManager.getAllWeqVarsNodeForFunction(ccp.getAppliedFunction()));

			if (!ccp.dependsOnUntrackedArray()) {
				madeChanges |= reportWeakEquivalenceDoOnlyRoweqPropagations(elem, ccp, projectedLabel, true);
			}

			if (isInconsistent(false)) {
				// propagation made this inconsistent --> no more propagations needed
				return;
			}

		}

		/*
		 * propagation rule: a--(a[q] in L)--(const l), a[i] in exp ==> a[i] in L cup {l}
		 */
		for (final Entry<NODE, WeakEquivalenceEdgeLabel<NODE>> adjacentEdge : getWeakEquivalenceGraph()
				.getAdjacentWeqEdges(elem.getAppliedFunction()).entrySet()) {
			// is weakly equal array a constant function?
			final NODE weaklyEqualArray = adjacentEdge.getKey();
			if (!weaklyEqualArray.isConstantFunction() || !weaklyEqualArray.getConstantFunctionValue().isLiteral()) {
				// other array is not a constant literal array --> do nothing
				continue;
			}
			// other array is a constant array
			// the "l" from the rule
			final NODE constantArrayConstant = weaklyEqualArray.getConstantFunctionValue();
			assert weaklyEqualArray.getConstantFunctionValue().isLiteral();

			// node that corresponds to a[q] in the rule
			final NODE aQ =
					elem.replaceArgument(mManager.getWeqVariableNodeForDimension(0, elem.getArgument().getSort()));

			final WeakEquivalenceEdgeLabel<NODE> edgeLabel = adjacentEdge.getValue();
			final Set<SetConstraint<NODE>> containsConstraint = edgeLabel.getContainsConstraintForElement(aQ);
			// assert containsConstraint.stream().allMatch(n -> n.isLiteral()) : "contains constraint not only over "
			// + "literals --> unexpected..";
			if (containsConstraint == null) {
				// there is no literal set constraint on a[q] --> do nothing
				continue;
			}
			// there is a literal set constraint on a[q]

			// construct L cup {l}
			final Set<SetConstraint<NODE>> newLiteralSet = mManager.getCcManager().getSetConstraintManager().join(
					mCongruenceClosure.getLiteralSetConstraints(), containsConstraint,
					Collections.singleton(mManager.getCcManager().getSetConstraintManager()
							.buildSetConstraint(Collections.singleton(constantArrayConstant))));

			// do propagation
			mCongruenceClosure.reportContainsConstraint(elem, newLiteralSet);
			// TODO: overapproximating here.. --> do something more precise?
			madeChanges = true;
		}

		if (madeChanges && !CcSettings.DELAY_EXT_AND_DELTA_CLOSURE) {
			extAndTriangleClosure(false);
		} else {
			mIsClosed = false;
		}
		// assert sanityCheck();
	}

	public boolean hasElements(final NODE... elems) {
		return mCongruenceClosure.hasElements(elems);
	}

	public void transformElementsAndFunctions(final Function<NODE, NODE> elemTransformer) {
		assert !isFrozen();

		if (mCongruenceClosure.isFrozen()) {
			final CongruenceClosure<NODE> ccUnfrozen = mManager.getCcManager().unfreeze(mCongruenceClosure);
			ccUnfrozen.transformElementsAndFunctions(elemTransformer);
			updateCongruenceClosure(ccUnfrozen);
		} else {
			mCongruenceClosure.transformElementsAndFunctions(elemTransformer);
		}

		if (getWeakEquivalenceGraph().isFrozen()) {
			final WeakEquivalenceGraph<NODE> weqGraphUnfrozen = mManager.unfreeze(getWeakEquivalenceGraph());
			weqGraphUnfrozen.transformElementsAndFunctions(elemTransformer);
			updateWeqGraph(weqGraphUnfrozen);
		} else {
			getWeakEquivalenceGraph().transformElementsAndFunctions(elemTransformer);
		}
		assert sanityCheck();
	}

	private void updateWeqGraph(final WeakEquivalenceGraph<NODE> weqGraphUnfrozen) {
		switch (mDiet) {
		case THIN:
		case TRANSITORY_THIN_TO_CCFAT:
			// case TRANSITORY_THIN_TO_WEQCCFAT:
			mWeakEquivalenceGraphThin = weqGraphUnfrozen;
			break;
		case CCFAT:
		case TRANSITORY_CCREFATTEN:
			mWeakEquivalenceGraphCcFat = weqGraphUnfrozen;
			break;
		// case TRANSITORY_WEQCCREFATTEN:
		// case WEQCCFAT:
		// mWeakEquivalenceGraphWeqCcFat = (WeakEquivalenceGraph<NODE, WeqCongruenceClosure<NODE>>) weqGraphUnfrozen;
		// break;
		}

	}

	private void updateCongruenceClosure(final CongruenceClosure<NODE> ccUnfrozen) {
		assert !isFrozen();
		mCongruenceClosure = ccUnfrozen;
	}

	/**
	 * is a simple element and all the elements that depend on it fully removed?
	 */
	public boolean assertSimpleElementIsFullyRemoved(final NODE elem) {
		for (final NODE e : getAllElements()) {
			if (e.isDependentNonFunctionApplication() && e.getSupportingNodes().contains(elem)) {
				assert false;
				return false;
			}
		}
		return mCongruenceClosure.assertSimpleElementIsFullyRemoved(elem);
	}

	public Set<NODE> getAllElements() {
		return mCongruenceClosure.getAllElements();
	}

	public boolean assertSingleElementIsFullyRemoved(final NODE elem) {
		if (!getWeakEquivalenceGraph().assertElementIsFullyRemoved(elem)) {
			assert false;
			return false;
		}

		return mCongruenceClosure.assertSingleElementIsFullyRemoved(elem);
	}

	WeqCongruenceClosure<NODE> join(final WeqCongruenceClosure<NODE> other) {
		assert this.isClosed() && other.isClosed();
		assert !this.isInconsistent(false) && !other.isInconsistent(false) && !this.isTautological()
				&& !other.isTautological() : "catch this case in WeqCcManager";

		final WeqCongruenceClosure<NODE> result =
				mManager.getWeqCongruenceClosure(mManager.join(mCongruenceClosure, other.mCongruenceClosure, true),
						mManager.join(getWeakEquivalenceGraph(), other.getWeakEquivalenceGraph(), true), true);

		return result;
	}

	/**
	 * Note that this works inplace and changes "this"
	 *
	 * @param other
	 * @return
	 */
	WeqCongruenceClosure<NODE> meet(final WeqCongruenceClosure<NODE> other) {
		assert !this.getWeakEquivalenceGraph().hasConstraintsToReport();

		final WeqCongruenceClosure<NODE> result = meetRec(other);

		if (!CcSettings.DELAY_EXT_AND_DELTA_CLOSURE) {
			result.executeFloydWarshallAndReportResultToWeqCc(false);
		} else {
			mIsClosed = false;
		}
		result.reportAllConstraintsFromWeqGraph(false);

		assert result.sanityCheck();
		return result;
	}

	private WeqCongruenceClosure<NODE> meetRec(final WeqCongruenceClosure<NODE> other) {
		final WeqCongruenceClosure<NODE> result = this.meetWeqWithCc(other.mCongruenceClosure);

		// the contains constraints may have introduced constraints to be propagated
		this.reportAllConstraintsFromWeqGraph(false);

		assert mManager.getSettings().omitSanitycheckFineGrained1() || result.sanityCheck();

		if (result.isInconsistent(false)) {
			return result;
		}

		assert result.mCongruenceClosure.assertAtMostOneLiteralPerEquivalenceClass();
		assert !this.getWeakEquivalenceGraph().hasConstraintsToReport();

		/*
		 * strategy: conjoin all weq edges of otherCC to a copy of this's weq graph
		 */
		if (!mManager.getSettings().omitSanitycheckFineGrained1()) {
			assert result.sanityCheck();
			assert other.getWeakEquivalenceGraph().sanityCheck();
			assert other.sanityCheck();
		}

		if (mManager.getSettings().isDeactivateWeakEquivalences()) {
			return result;
		}

		// report all weq edges from other
		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE>> edge : other.getCcWeakEquivalenceGraph()
				.getEdges().entrySet()) {

			result.reportWeakEquivalenceDoOnlyRoweqPropagations(edge.getKey().getOneElement(),
					edge.getKey().getOtherElement(), edge.getValue(), true);
			assert result.sanityCheck();

			if (result.isInconsistent(false)) {
				return result;
			}
		}

		return result;
	}

	public void freezeIfNecessary() {
		if (!this.isFrozen()) {
			this.freezeOmitPropagations();
		} else {
			// nothing to do
		}
	}

	private WeqCongruenceClosure<NODE> meetWeqWithCc(final CongruenceClosure<NODE> other) {
		assert !this.isInconsistent(false) && !other.isInconsistent(false);

		WeqCongruenceClosure<NODE> thisAligned = mManager.addAllElements(this, other.getAllElements(), null, true);

		for (final Entry<NODE, NODE> eq : other.getSupportingElementEqualities().entrySet()) {
			if (thisAligned.isInconsistent(false)) {
				return this;
			}
			thisAligned = mManager.reportEquality(thisAligned, eq.getKey(), eq.getValue(), true);
		}
		for (final Entry<NODE, NODE> deq : other.getElementDisequalities()) {
			if (thisAligned.isInconsistent(false)) {
				return this;
			}
			thisAligned = mManager.reportDisequality(thisAligned, deq.getKey(), deq.getValue(), true);
		}
		for (final Entry<NODE, SetConstraintConjunction<NODE>> en : other.getLiteralSetConstraints().getConstraints()
				.entrySet()) {
			if (thisAligned.isInconsistent(false)) {
				return this;
			}
			thisAligned = mManager.reportContainsConstraint(en.getKey(), en.getValue().getSetConstraints(), thisAligned,
					true);
		}
		assert thisAligned.sanityCheck();
		return thisAligned;
	}

	@Override
	public boolean sanityCheck() {
		if (isInconsistent(false)) {
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

		if (!isInconsistent(false)
		// && !mIsWeqFatEdgeLabel
		// && mDiet != Diet.WEQCCFAT
		// && mDiet != Diet.TRANSITORY_THIN_TO_WEQCCFAT
		// && mDiet != Diet.TRANSITORY_WEQCCREFATTEN
		) {
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
		if (isInconsistent(false)) {
			return "False";
		}
		if (getAllElements().size() < mManager.getSettings().getMaxNoElementsForVerboseToString()) {
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
		if (isInconsistent(false)) {
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
	 *
	 * @return
	 */
	public boolean weqGraphFreeOfArrayEqualities() {
		if (getWeakEquivalenceGraph().hasConstraintsToReport()) {
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
		default:
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
		mManager.addNode(node, mCongruenceClosure, this, true, true);

		if (!newlyAdded) {
			return false;
		}
		registerNewElement(node);
		return true;
	}

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

	@Override
	public boolean isDebugMode() {
		return mLogger != null;
	}

	@Override
	public ILogger getLogger() {
		return mLogger;
	}

	public WeakEquivalenceGraph<NODE> getCcWeakEquivalenceGraph() {
		assert assertDietSanity();
		switch (mDiet) {
		case THIN:
		case TRANSITORY_THIN_TO_CCFAT:
			// case TRANSITORY_THIN_TO_WEQCCFAT:
			return mWeakEquivalenceGraphThin;
		case CCFAT:
		case TRANSITORY_CCREFATTEN:
			return mWeakEquivalenceGraphCcFat;
		// case WEQCCFAT:
		// throw new IllegalStateException();
		default:
			throw new AssertionError();
		}
	}

	public WeakEquivalenceGraph<NODE> getWeakEquivalenceGraph() {
		assert assertDietSanity();
		switch (mDiet) {
		case THIN:
		case TRANSITORY_THIN_TO_CCFAT:
			// case TRANSITORY_THIN_TO_WEQCCFAT:
			return mWeakEquivalenceGraphThin;
		case CCFAT:
		case TRANSITORY_CCREFATTEN:
			return mWeakEquivalenceGraphCcFat;
		// case WEQCCFAT:
		// case TRANSITORY_WEQCCREFATTEN:
		// return (WeakEquivalenceGraph<NODE>) mWeakEquivalenceGraphWeqCcFat;
		default:
			throw new AssertionError();
		}
	}

	private boolean assertDietSanity() {
		switch (mDiet) {
		case THIN:
		case TRANSITORY_THIN_TO_CCFAT:
			// case TRANSITORY_THIN_TO_WEQCCFAT:
			if (mWeakEquivalenceGraphThin == null) {
				assert false;
				return false;
			}
			if (mWeakEquivalenceGraphCcFat != null) {
				assert false;
				return false;
			}
			// if (mWeakEquivalenceGraphWeqCcFat != null) {
			// assert false;
			// return false;
			// }
			break;
		case CCFAT:
		case TRANSITORY_CCREFATTEN:
			if (mWeakEquivalenceGraphThin != null) {
				assert false;
				return false;
			}
			if (mWeakEquivalenceGraphCcFat == null) {
				assert false;
				return false;
			}
			// if (mWeakEquivalenceGraphWeqCcFat != null) {
			// assert false;
			// return false;
			// }
			break;
		// case WEQCCFAT:
		// case TRANSITORY_WEQCCREFATTEN:
		// if (mWeakEquivalenceGraphThin != null) {
		// assert false;
		// return false;
		// }
		// if (mWeakEquivalenceGraphCcFat != null) {
		// assert false;
		// return false;
		// }
		// if (mWeakEquivalenceGraphWeqCcFat == null) {
		// assert false;
		// return false;
		// }
		// break;
		}
		return true;
	}

	public boolean sanityCheckOnlyCc() {
		return mCongruenceClosure.sanityCheck();
	}

	public boolean sanityCheckOnlyCc(final IRemovalInfo<NODE> remInfo) {
		return mCongruenceClosure.sanityCheck(remInfo);
	}

	public void thin() {
		assert !mIsFrozen;
		assert mDiet != Diet.THIN;
		assert assertDietSanity();
		// if (mWeakEquivalenceGraphWeqCcFat != null) {
		// mWeakEquivalenceGraphThin = mWeakEquivalenceGraphWeqCcFat.thinLabels(this);
		// mWeakEquivalenceGraphWeqCcFat = null;
		// } else
		if (mWeakEquivalenceGraphCcFat != null) {
			mWeakEquivalenceGraphThin = mWeakEquivalenceGraphCcFat.thinLabels(this);
			mWeakEquivalenceGraphCcFat = null;
		} else {
			throw new AssertionError();
		}
		mDiet = Diet.THIN;
	}

	public Diet getDiet() {
		return mDiet;
	}

	public void setDiet(final Diet newDiet) {
		mDiet = newDiet;
	}

	public void setIsEdgeLabelDisjunct() {
		mIsWeqFatEdgeLabel = true;
	}

	public WeqCcManager<NODE> getManager() {
		return mManager;
	}

	public Set<NODE> getAllLiterals() {
		return mCongruenceClosure.getAllLiterals();
	}

	public Set<SetConstraint<NODE>> getContainsConstraintForElement(final NODE elem) {
		return mCongruenceClosure.getContainsConstraintForElement(elem);
	}

	public boolean isWeqFatEdgeLabel() {
		return mIsWeqFatEdgeLabel;
	}

	public boolean isClosed() {
		return mIsClosed;
	}

	@Override
	public boolean isConstrainedDirectly(final NODE elem) {
		throw new UnsupportedOperationException("we are not using weq fattening anymore, right? (otherwise: implement "
				+ "similarly as in CongruenceClosure..)");
	}
}

/**
 * Describes the state of the edge labels of the weq graph. (..)
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
enum Diet {
	THIN, CCFAT,
	/**
	 * state for the transition from thin to fat (relevant for sanity checks)
	 */
	TRANSITORY_THIN_TO_CCFAT, TRANSITORY_CCREFATTEN,;
}