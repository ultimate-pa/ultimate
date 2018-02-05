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
package de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.EqualityStatus;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ThreeValuedEquivalenceRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.IPartialComparator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.PartialOrderCache;

public class CcManager<ELEM extends ICongruenceClosureElement<ELEM>> {

	private final IPartialComparator<CongruenceClosure<ELEM>> mCcComparator;

	private final ILogger mLogger;

	private final CongruenceClosure<ELEM> mInconsistentCc;

	private final CongruenceClosure<ELEM> mEmptyFrozenCc;

	private final PartialOrderCache<CongruenceClosure<ELEM>> mPartialOrderCache;

	public CcManager(final ILogger logger, final IPartialComparator<CongruenceClosure<ELEM>> ccComparator) {
		mLogger = logger;
		mCcComparator = ccComparator;

		mInconsistentCc = new CongruenceClosure<>(true);
		mInconsistentCc.freeze();

		mEmptyFrozenCc = new CongruenceClosure<>(this);
		mEmptyFrozenCc.freeze();

		if (CcSettings.UNIFY_CCS) {
	 		mPartialOrderCache = new PartialOrderCache<>(mCcComparator);
	 	} else {
	 		mPartialOrderCache = null;
	 	}
	}

	public CongruenceClosure<ELEM> meet(final CongruenceClosure<ELEM> cc1, final CongruenceClosure<ELEM> cc2,
			final boolean inplace) {
		assert !CcSettings.FORBID_INPLACE || !inplace;
		CongruenceClosure<ELEM> result = meet(cc1, cc2, null, inplace);
		result = postProcessCcResult(result);
		return result;
	}

	private CongruenceClosure<ELEM> postProcessCcResult(CongruenceClosure<ELEM> result) {
		if (CcSettings.UNIFY_CCS) {
			assert result.isFrozen();
			result = mPartialOrderCache.addElement(result);
		}
		return result;
	}

	/**
	 *
	 * @param cc1
	 * @param cc2
	 * @param remInfo
	 * @param inplace the result is the same object as the first argument, with all constraints from the second argument
	 *  added
	 * @return
	 */
	public CongruenceClosure<ELEM> meet(final CongruenceClosure<ELEM> cc1, final CongruenceClosure<ELEM> cc2,
			final IRemovalInfo<ELEM> remInfo, final boolean inplace) {
		assert !CcSettings.FORBID_INPLACE || !inplace;
		if (!inplace) {
			freezeIfNecessary(cc1);
			freezeIfNecessary(cc2);
		}
		assert inplace != cc1.isFrozen();
		if (!CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_1) {
			assert cc1.sanityCheck();
			assert cc2.sanityCheck();
		}

		if (cc1.isTautological() && !inplace) {
//			assert cc1.isFrozen() && cc2.isFrozen() : "unforeseen case, when does this happen?";
			freezeIfNecessary(cc2);
			return cc2;
		}
		if (cc2.isTautological()) {
			return cc1;
		}
		if (cc1.isInconsistent()) {
			return cc1;
		}
		if (cc2.isInconsistent() && !inplace) {
			return getInconsistentCc();
		}

		final CongruenceClosure<ELEM> result;
		if (remInfo == null) {
			result = cc1.meetRec(cc2, inplace);
		} else {
			result = cc1.meetRec(cc2, remInfo, inplace);
		}

		assert CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_2 || result.sanityCheck();

		final CongruenceClosure<ELEM> resultPp = postProcessCcResult(result);
		return resultPp;
	}



	/**
	 * note: join always happens immutable/non-inplace style. Thus before a join everything has to be frozen.
	 * The result is not frozen by default (but guaranteed to be a fresh object).
	 *
	 * (even though not frozen, the result is probably always completely reduced/closed)
	 *
	 * @param cc1
	 * @param cc2
	 * @param modifiable result Cc should be modifiable or frozen?
	 * @return
	 */
	public CongruenceClosure<ELEM> join(final CongruenceClosure<ELEM> cc1, final CongruenceClosure<ELEM> cc2,
			final boolean modifiable) {
		/*
		 * Freeze-before-join politics.. -- might not be strictly necessary here, because CongruenceClosure-freeze
		 * triggers no propagations
		 */
		freezeIfNecessary(cc1);
		freezeIfNecessary(cc2);


		if (cc1.isInconsistent()) {
			return cc2;
		}
		if (cc2.isInconsistent()) {
			return cc1;
		}
		if (cc1.isTautological() || cc2.isTautological()) {
			return getEmptyCc(modifiable);
		}

		final CongruenceClosure<ELEM> result = cc1.join(cc2);

		if (!modifiable) {
			result.freeze();
		}
		assert modifiable != result.isFrozen();

		final CongruenceClosure<ELEM> resultPp = postProcessCcResult(result);
		return resultPp;
	}

//	public ComparisonResult compare(final CongruenceClosure<ELEM> cc1,
//			final CongruenceClosure<ELEM> cc2) {
//		if (CcSettings.UNIFY_CCS) {
//			return mPartialOrderCache.lowerEqual(elem1, elem2)
//		}
//		return mCcComparator.compare(cc1, cc2);
//	}

	/**
	 * The given list is implicitly a disjunction.
	 * If one element in the disjunction is stronger than another, we can drop it.
	 *
	 * TODO: poor man's solution, could be done much nicer with lattice representation..
	 *
	 * @param unionList
	 * @return
	 */
	public Set<CongruenceClosure<ELEM>> filterRedundantCcs(final Set<CongruenceClosure<ELEM>> unionList) {
		final PartialOrderCache<CongruenceClosure<ELEM>> poc = new PartialOrderCache<>(mCcComparator);
		return filterRedundantCcs(unionList, poc);
	}

	public  IPartialComparator<CongruenceClosure<ELEM>> getCcComparator() {
		return mCcComparator;
	}

	public Set<CongruenceClosure<ELEM>> filterRedundantCcs(final Set<CongruenceClosure<ELEM>> unionList,
			final PartialOrderCache<CongruenceClosure<ELEM>> ccPoCache) {
		final Set<CongruenceClosure<ELEM>> maxReps = ccPoCache.getMaximalRepresentatives(unionList);
		// some additional processing: if maxReps is {False}, return the empty set
		assert !maxReps.stream().anyMatch(cc -> cc.isInconsistent()) || maxReps.size() == 1;
		if (maxReps.iterator().next().isInconsistent()) {
			return Collections.emptySet();
		}

		return maxReps;
	}

	public CongruenceClosure<ELEM> reportEquality(final ELEM node1, final ELEM node2,
			final CongruenceClosure<ELEM> origCc, final boolean inplace) {
		assert !CcSettings.FORBID_INPLACE || !inplace;
		if (inplace) {
			origCc.reportEquality(node1, node2);
			return origCc;
		} else {
			final CongruenceClosure<ELEM> unfrozen = unfreeze(origCc);
			unfrozen.reportEquality(node1, node2);
			unfrozen.freeze();

			final CongruenceClosure<ELEM> resultPp = postProcessCcResult(unfrozen);
			return resultPp;
		}
	}

	public CongruenceClosure<ELEM> reportDisequality(final ELEM node1, final ELEM node2,
			final CongruenceClosure<ELEM> origCc, final boolean inplace) {
		assert !CcSettings.FORBID_INPLACE || !inplace;
		if (inplace) {
			origCc.reportDisequality(node1, node2);
			return origCc;
		} else {
			final CongruenceClosure<ELEM> unfrozen = unfreeze(origCc);
			unfrozen.reportDisequality(node1, node2);
			unfrozen.freeze();

			assert unfrozen.isInconsistent()
				|| unfrozen.getEqualityStatus(node1, node2) == EqualityStatus.NOT_EQUAL;
			final CongruenceClosure<ELEM> resultPp = postProcessCcResult(unfrozen);
			return resultPp;
		}
	}

//	public CongruenceClosure<ELEM> transformElementsAndFunctions(final Function<ELEM, ELEM> elemTransformer,
//			final CongruenceClosure<ELEM> origCc) {
//		final CongruenceClosure<ELEM> unfrozen = unfreeze(origCc);
//		unfrozen.transformElementsAndFunctions(elemTransformer);
//		unfrozen.freeze();
//		return unfrozen;
//	}

	public CongruenceClosure<ELEM> removeSimpleElement(final ELEM elem, final CongruenceClosure<ELEM> origCc,
			final boolean modifiable) {

		// freeze-before-.. politics
		freezeIfNecessary(origCc);

		final CongruenceClosure<ELEM> result = unfreeze(origCc);
		RemoveCcElement.removeSimpleElement(result, elem);
		if (!modifiable) {
		result.freeze();
		}
		assert modifiable != result.isFrozen();

		final CongruenceClosure<ELEM> resultPp = postProcessCcResult(result);
		return resultPp;
	}

	public CongruenceClosure<ELEM> removeSimpleElementDontIntroduceNewNodes(final ELEM elem,
			final CongruenceClosure<ELEM> origCc, final boolean modifiable) {

		// freeze-before-.. politics
		freezeIfNecessary(origCc);

		final CongruenceClosure<ELEM> result = unfreeze(origCc);
		RemoveCcElement.removeSimpleElementDontIntroduceNewNodes(result, elem);

		if (!modifiable) {
			result.freeze();
		}
		assert modifiable != result.isFrozen();

		final CongruenceClosure<ELEM> resultPp = postProcessCcResult(result);
		return resultPp;
	}

//	public Pair<CongruenceClosure<ELEM>, Set<ELEM>> removeSimpleElementDontUseWeqGpaTrackAddedNodes(final ELEM elem,
//			final CongruenceClosure<ELEM> origCc, final boolean modifiable) {
//
//		// freeze-before-.. politics
//		freezeIfNecessary(origCc);
//
//		final CongruenceClosure<ELEM> result = unfreeze(origCc);
//		final Set<ELEM> addedNodes = RemoveCcElement.removeSimpleElementDontUseWeqGpaTrackAddedNodes(result, elem);
//
//		if (!modifiable) {
//			result.freeze();
//		}
//		assert modifiable != result.isFrozen();
//
//		return new Pair<>(result, addedNodes);
//	}

	public CongruenceClosure<ELEM> unfreeze(final CongruenceClosure<ELEM> origCc) {
		assert origCc.isFrozen();
		return new CongruenceClosure<>(origCc);
	}

	private CongruenceClosure<ELEM> unfreeze(final CongruenceClosure<ELEM> cc, final IRemovalInfo<ELEM> remInfo) {
		assert cc.isFrozen();
		return new CongruenceClosure<>(cc, remInfo);
	}

	public CongruenceClosure<ELEM> addElement(final CongruenceClosure<ELEM> congruenceClosure, final ELEM elem,
			final boolean inplace, final boolean omitSanityCheck) {
		assert !CcSettings.FORBID_INPLACE || !inplace;
		return addElement(congruenceClosure, elem, congruenceClosure, inplace, omitSanityCheck);
	}


	public CongruenceClosure<ELEM> addElement(final CongruenceClosure<ELEM> congruenceClosure, final ELEM elem,
			final ICongruenceClosure<ELEM> newEqualityTarget,
			final boolean inplace, final boolean omitSanityCheck) {
		assert !CcSettings.FORBID_INPLACE || !inplace;
		assert inplace != congruenceClosure.isFrozen();
		if (inplace) {
			congruenceClosure.addElement(elem, newEqualityTarget, omitSanityCheck);
			return congruenceClosure;
		} else {
			final CongruenceClosure<ELEM> unfrozen = unfreeze(congruenceClosure);
			unfrozen.addElement(elem, newEqualityTarget, omitSanityCheck);
			unfrozen.freeze();

			final CongruenceClosure<ELEM> resultPp = postProcessCcResult(unfrozen);
			return resultPp;
		}
	}

//	public Pair<CongruenceClosure<ELEM>, HashRelation<ELEM, ELEM>> addElementAndGetNewEqualities(
//			final CongruenceClosure<ELEM> congruenceClosure, final ELEM elem, final boolean inplace,
//			final boolean omitSanityChecks) {
//		assert inplace != congruenceClosure.isFrozen();
//		if (inplace) {
//			final HashRelation<ELEM, ELEM> newEqualities = congruenceClosure.addElement(elem, omitSanityChecks);
//			return new Pair<>(congruenceClosure, newEqualities);
//		} else {
//			final CongruenceClosure<ELEM> unfrozen = unfreeze(congruenceClosure);
//			final HashRelation<ELEM, ELEM> newEqualities = unfrozen.addElement(elem, omitSanityChecks);
//			unfrozen.freeze();
//			return unfrozen;
//		}
//	}

	/**
	 * (always works in place)
	 *
	 * @param congruenceClosure
	 * @param elem1
	 * @param b
	 * @return
	 */
	public boolean addElementReportChange(final CongruenceClosure<ELEM> congruenceClosure, final ELEM elem,
			final boolean omitSanityCheck) {
		return congruenceClosure.addElement(elem, congruenceClosure, omitSanityCheck);
	}

	public boolean isDebugMode() {
		return true;
	}

	public ILogger getLogger() {
		return mLogger;
	}

	public CongruenceClosure<ELEM> getSingleEqualityCc(final ELEM node1, final ELEM node2, final boolean modifiable) {
		final CongruenceClosure<ELEM> cc = getEmptyCc(modifiable);
		final CongruenceClosure<ELEM> result = reportEquality(node1, node2, cc, modifiable);
		final CongruenceClosure<ELEM> resultPp = postProcessCcResult(result);
		return resultPp;
	}

	public CongruenceClosure<ELEM> getSingleDisequalityCc(final ELEM node1, final ELEM node2, final boolean modifiable) {
		final CongruenceClosure<ELEM> cc = getEmptyCc(modifiable);
		final CongruenceClosure<ELEM> result = reportDisequality(node1, node2, cc, modifiable);
		final CongruenceClosure<ELEM> resultPp = postProcessCcResult(result);
		return resultPp;
	}

	public CongruenceClosure<ELEM> getEmptyCc(final boolean modifiable) {
		if (modifiable) {
			return new CongruenceClosure<>(this);
	 	} else {
	 		return mEmptyFrozenCc;
	 	}
	}

	public CongruenceClosure<ELEM> getInconsistentCc() {
		return mInconsistentCc;
	}

	public CongruenceClosure<ELEM> getCongruenceClosureFromTver(final ThreeValuedEquivalenceRelation<ELEM> tver,
			final boolean modifiable) {
		final CongruenceClosure<ELEM> result = new CongruenceClosure<>(this, tver);
		if (!modifiable) {
			result.freeze();
		}
		return result;
	}

	public CongruenceClosure<ELEM> getCongruenceClosureFromTver(final ThreeValuedEquivalenceRelation<ELEM> tver,
			final IRemovalInfo<ELEM> removeElementInfo, final boolean modifiable) {
		final CongruenceClosure<ELEM> result = new CongruenceClosure<>(this, tver, removeElementInfo);
		if (!modifiable) {
			result.freeze();
		}
		return result;
	}

	public CongruenceClosure<ELEM> getCopyWithRemovalInfo(final CongruenceClosure<ELEM> cc,
			final IRemovalInfo<ELEM> remInfo) {
		return new CongruenceClosure<>(cc, remInfo);
	}

	public CongruenceClosure<ELEM> copyNoRemInfo(final CongruenceClosure<ELEM> cc) {
		if (cc.isInconsistent()) {
			// no need for a real copy, as there is no operation that changes an inconsistent cc anyway..
			return cc;
		}

		final CongruenceClosure<ELEM> result = new CongruenceClosure<>(cc);

		if (cc.isFrozen()) {
			result.freeze();
		}
//		assert result.isFrozen() == cc.isFrozen();
//		if (CcSettings.FREEZE_ALL_IN_MANAGER) {
//			result.freeze();
//		}
		return result;
	}

	public CongruenceClosure<ELEM> copyNoRemInfoUnfrozen(final CongruenceClosure<ELEM> cc) {
		return new CongruenceClosure<>(cc);
	}

	public CongruenceClosure<ELEM> transformElements(final CongruenceClosure<ELEM> cc,
			final Function<ELEM, ELEM> transformer, final boolean inplace) {
		assert !CcSettings.FORBID_INPLACE || !inplace;
		final CongruenceClosure<ELEM> result;
		if (inplace) {
//			assert false : "inplace does not seem to work, currently (problem with representatives...)";
			cc.transformElementsAndFunctions(transformer);
			result = cc;
		} else {
			final CongruenceClosure<ELEM> unfrozen = unfreezeIfNecessary(cc);
			unfrozen.transformElementsAndFunctions(transformer);
			unfrozen.freeze();
			// TODO: implement a result check here?
			result = unfrozen;
		}
		assert result.sanityCheck();
		final CongruenceClosure<ELEM> resultPp = postProcessCcResult(result);
		return resultPp;
	}

	public CongruenceClosure<ELEM> projectToElements(final CongruenceClosure<ELEM> cc, final Set<ELEM> nodesToKeep,
			final IRemovalInfo<ELEM> remInfo) {
		if (CcSettings.PROJECTTOELEMENTS_INPLACE) {
			assert false : "CongruenceClosure.projectToElements is currently not suited for inplace operation";
			return cc.projectToElements(nodesToKeep, remInfo);
		} else {
//			final CongruenceClosure<ELEM> result = cc.projectToElements(nodesToKeep, remInfo);
//			assert result.isFrozen();
//			return result;

			/* the operation might be lossy, but here we treat a CongruenceClosure, so freezing for closing is not
			 * needed */
			final CongruenceClosure<ELEM> unfrozen = unfreezeIfNecessary(cc);
			final CongruenceClosure<ELEM> result = unfrozen.projectToElements(nodesToKeep, remInfo);
			result.freeze();
			// TODO: implement a result check here?
			final CongruenceClosure<ELEM> resultPp = postProcessCcResult(result);
			return resultPp;
		}
	}

	public CongruenceClosure<ELEM> addAllElements(final CongruenceClosure<ELEM> cc, final Set<ELEM> elemsToAdd,
			final IRemovalInfo<ELEM> remInfo, final boolean inplace) {
		assert !CcSettings.FORBID_INPLACE || !inplace;
		assert !cc.isInconsistent();

		final CongruenceClosure<ELEM> result;
		if (inplace) {
			result = cc;
		} else {

			freezeIfNecessary(cc);

			// TODO: is it redundant to add remInfo to the result Cc and give it to addElementRec??
			result = unfreeze(cc, remInfo);
		}

		for (final ELEM elem : elemsToAdd) {
			addElement(result, elem, true, true);
		}

		if (!inplace) {
			result.freeze();
		}

		final CongruenceClosure<ELEM> resultPp = postProcessCcResult(result);
		return resultPp;
	}

	public CongruenceClosure<ELEM> unfreezeIfNecessary(final CongruenceClosure<ELEM> cc) {
		if (cc.isFrozen()) {
			return unfreeze(cc);
		} else {
			return cc;
		}
	}

	public void freezeIfNecessary(final CongruenceClosure<ELEM> cc) {
		if (!cc.isFrozen()) {
			cc.freeze();
		}
	}

	public CongruenceClosure<ELEM> getCopy(final CongruenceClosure<ELEM> congruenceClosure, final boolean modifiable) {
		final CongruenceClosure<ELEM> copy = new CongruenceClosure<>(congruenceClosure);
		/*
		 * remark: if there were any closure operations during a CongruenceClosure.freeze, we would have to trigger
		 *  them here.
		 */
		if (!modifiable) {
			copy.freeze();
		}
		return copy;
	}
//	public boolean isStrongerThan(final CongruenceClosure<ELEM> cc1, final CongruenceClosure<ELEM> cc2) {
//			final BiPredicate<CongruenceClosure<NODE>, CongruenceClosure<NODE>> lowerOrEqual) {

	public boolean isStrongerThan(final CongruenceClosure<ELEM> cc1, final CongruenceClosure<ELEM> cc2) {
		if (CcSettings.UNIFY_CCS) {
//			if (!mPartialOrderCache.knowsElement(cc1)) {
//				mPartialOrderCache.addElement(cc1);
//			}
			return mPartialOrderCache.lowerEqual(cc1, cc2);
		}

		if (cc1.isInconsistent()) {
			return true;
		}
		if (cc2.isInconsistent()) {
			// we know this != False, and other = False
			return false;
		}
		if (cc2.isTautological()) {
			return true;
		}
		if (cc1.isTautological()) {
			// we know other != True, and this = True
			return false;
		}
		final CongruenceClosure<ELEM> thisAligned = getCopy(cc1, true);
		addAllElements(thisAligned, cc2.getAllElements(), null, true);
		// freeze not necessary but to make clear that thisAligned is closed at this point
		thisAligned.freeze();

		assert assertElementsAreSuperset(thisAligned, cc2);
		final CongruenceClosure<ELEM> otherAligned = getCopy(cc2, true);
		addAllElements(otherAligned, cc1.getAllElements(), null, true);
		// freeze not necessary but to make clear that thisAligned is closed at this point
		otherAligned.freeze();

		assert assertElementsAreSuperset(thisAligned, otherAligned);
		assert assertElementsAreSuperset(otherAligned, thisAligned);

		return checkIsStrongerThan(thisAligned, otherAligned);
	}

	/**
	 * We check for each equivalence representative in "other" if its equivalence
	 * class is a subset of the equivalence class of the representative in "this".
	 *
	 * (going through the representatives in "this" would be unsound because we
	 * might not see all relevant equivalence classes in "other")
	 *
	 * assumes that this and other have the same elements and functions
	 *
	 * Induces a non-strict (antisymmetric) partial ordering of the CongruenceClosure instances.
	 */
	private boolean checkIsStrongerThan(final CongruenceClosure<ELEM> thisAligned,
			final CongruenceClosure<ELEM> otherAligned) {
		assert !thisAligned.isInconsistent() && !otherAligned.isInconsistent();

		assert assertElementsAreSuperset(thisAligned, otherAligned);
		assert assertElementsAreSuperset(otherAligned, thisAligned);

		if (!isPartitionStronger(thisAligned.mElementTVER, otherAligned.mElementTVER)) {
			return false;
		}

		/*
		 * We check if each disequality that holds in "other" also holds in "this".
		 */
//		if (!areDisequalitiesStrongerThan(thisAligned.mElementTVER, otherAligned.mElementTVER)) {
		if (!areDisequalitiesStrongerThan(thisAligned, otherAligned)) {
			return false;
		}
		return true;
	}

	public boolean isEquivalent(final CongruenceClosure<ELEM> cc1, final CongruenceClosure<ELEM> cc2) {
		if (cc1.isInconsistent() && cc2.isInconsistent()) {
			return true;
		}
		if (cc1.isTautological() && cc2.isTautological()) {
			return true;
		}
		if (cc2.isInconsistent() || cc1.isInconsistent()) {
			return false;
		}
		if (cc2.isTautological() || cc1.isTautological()) {
			return false;
		}

		final CongruenceClosure<ELEM> thisAligned =
				addAllElements(cc1, cc2.getAllElements(), null, false);
		final CongruenceClosure<ELEM> otherAligned =
				addAllElements(cc2, cc1.getAllElements(), null, false);
		return checkIsStrongerThan(thisAligned, otherAligned) && checkIsStrongerThan(otherAligned, thisAligned);
	}

//	private static <E> boolean areDisequalitiesStrongerThan(final ThreeValuedEquivalenceRelation<E> thisTVER,
//			final ThreeValuedEquivalenceRelation<E> otherTVER) {
	private static <E extends ICongruenceClosureElement<E>>
			boolean areDisequalitiesStrongerThan(final CongruenceClosure<E> left,
					final CongruenceClosure<E> right) {
		for (final E rep : right.getAllElementRepresentatives()) {
			for (final E disequalRep : right.getRepresentativesUnequalTo(rep)) {
				if (left.getEqualityStatus(rep, disequalRep) != EqualityStatus.NOT_EQUAL) {
					return false;
				}
			}
		}
		return true;
	}


	private boolean assertElementsAreSuperset(final Set<ELEM> a, final Set<ELEM> b) {
		final Set<ELEM> difference = DataStructureUtils.difference(b, a);
		if (!difference.isEmpty()) {
			assert false;
			return false;
		}
		return true;

	}

	/**
	 * check that elements in a are a superset of elements in b
	 * @param a
	 * @param b
	 * @return
	 */
	private boolean assertElementsAreSuperset(final CongruenceClosure<ELEM> a,
			final CongruenceClosure<ELEM> b) {
		final Set<ELEM> difference = DataStructureUtils.difference(b.getAllElements(), a.getAllElements());
		if (!difference.isEmpty()) {
			assert false;
			return false;
		}
		return true;
	}


		/**
	 *
	 * @param first
	 * @param second
	 * @return true if first is stronger/more constraining than second
	 */
	private static <E> boolean isPartitionStronger(final ThreeValuedEquivalenceRelation<E> first,
			final ThreeValuedEquivalenceRelation<E> second) {
		final Collection<E> representativesFromBoth = new ArrayList<>(first.getAllRepresentatives().size()
				+ second.getAllRepresentatives().size());
		representativesFromBoth.addAll(first.getAllRepresentatives());
		representativesFromBoth.addAll(second.getAllRepresentatives());

		for (final E rep : representativesFromBoth) {
			final Set<E> eqInOther = second.getEquivalenceClass(rep);
			final Set<E> eqInThis = first.getEquivalenceClass(rep);
			if (!eqInThis.containsAll(eqInOther)) {
				return false;
			}
		}
		return true;
	}
}
