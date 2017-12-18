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

import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ThreeValuedEquivalenceRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.IPartialComparator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.IPartialComparator.ComparisonResult;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.PartialOrderCache;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class CcManager<ELEM extends ICongruenceClosureElement<ELEM>> {

	private final IPartialComparator<CongruenceClosure<ELEM>> mCcComparator;

	private final ILogger mLogger;

	private final CongruenceClosure<ELEM> mInconsistentCc;

	private final CongruenceClosure<ELEM> mEmptyFrozenCc;

	public CcManager(final ILogger logger, final IPartialComparator<CongruenceClosure<ELEM>> ccComparator) {
		mLogger = logger;
		mCcComparator = ccComparator;

		mInconsistentCc = new CongruenceClosure<>(true);
		mInconsistentCc.freeze();

		mEmptyFrozenCc = new CongruenceClosure<>(this);
		mEmptyFrozenCc.freeze();
	}

//	public CongruenceClosure<ELEM> meet(final CongruenceClosure<ELEM> cc1, final CongruenceClosure<ELEM> cc2) {
//		final CongruenceClosure<ELEM> result = meet(cc1, cc2, null, false);
//		if (CcSettings.FREEZE_ALL_IN_MANAGER) {
//			if (!result.isFrozen()) {
//				result.freeze();
//			}
//		}
//		return result;
//	}
//
//	public CongruenceClosure<ELEM> meet(final CongruenceClosure<ELEM> cc1, final CongruenceClosure<ELEM> cc2,
//			final RemoveCcElement<ELEM> remInfo) {
//		return meet(cc1, cc2, remInfo, false);
//	}

	public CongruenceClosure<ELEM> meet(final CongruenceClosure<ELEM> cc1, final CongruenceClosure<ELEM> cc2,
			final boolean inplace) {
		return meet(cc1, cc2, null, inplace);
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
		assert !inplace || !cc1.isFrozen();
		assert cc1.sanityCheck();
		assert cc2.sanityCheck();

		if (cc1.isTautological() && !inplace) {
			assert cc1.isFrozen() && cc2.isFrozen() : "unforseen case, when does this happen?";
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

		assert result.sanityCheck();

		return result;
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

		return result;
	}

	public ComparisonResult compare(final CongruenceClosure<ELEM> cc1,
			final CongruenceClosure<ELEM> cc2) {
		return mCcComparator.compare(cc1, cc2);
	}

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
		return ccPoCache.getMaximalRepresentatives(unionList);
	}

	public CongruenceClosure<ELEM> reportEquality(final ELEM node1, final ELEM node2,
			final CongruenceClosure<ELEM> origCc, final boolean inplace) {
		if (inplace) {
			origCc.reportEquality(node1, node2);
			return origCc;
		} else {
			final CongruenceClosure<ELEM> unfrozen = unfreeze(origCc);
			unfrozen.reportEquality(node1, node2);
			unfrozen.freeze();
			return unfrozen;
		}
	}

	public CongruenceClosure<ELEM> reportDisequality(final ELEM node1, final ELEM node2,
			final CongruenceClosure<ELEM> origCc, final boolean inplace) {
		if (inplace) {
			origCc.reportDisequality(node1, node2);
			return origCc;
		} else {
			final CongruenceClosure<ELEM> unfrozen = unfreeze(origCc);
			unfrozen.reportDisequality(node1, node2);
			unfrozen.freeze();
			return unfrozen;
		}
	}

	public CongruenceClosure<ELEM> transformElementsAndFunctions(final Function<ELEM, ELEM> elemTransformer,
			final CongruenceClosure<ELEM> origCc) {
		final CongruenceClosure<ELEM> unfrozen = unfreeze(origCc);
		unfrozen.transformElementsAndFunctions(elemTransformer);
		unfrozen.freeze();
		return unfrozen;
	}

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

		return result;
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

		return result;
	}

	public Pair<CongruenceClosure<ELEM>, Set<ELEM>> removeSimpleElementDontUseWeqGpaTrackAddedNodes(final ELEM elem,
			final CongruenceClosure<ELEM> origCc, final boolean modifiable) {

		// freeze-before-.. politics
		freezeIfNecessary(origCc);

		final CongruenceClosure<ELEM> result = unfreeze(origCc);
		final Set<ELEM> addedNodes = RemoveCcElement.removeSimpleElementDontUseWeqGpaTrackAddedNodes(result, elem);

		if (!modifiable) {
			result.freeze();
		}
		assert modifiable != result.isFrozen();

		return new Pair<>(result, addedNodes);
	}

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
		if (inplace) {
			congruenceClosure.addElement(elem, omitSanityCheck);
			return congruenceClosure;
		} else {
			final CongruenceClosure<ELEM> unfrozen = unfreeze(congruenceClosure);
			unfrozen.addElement(elem, omitSanityCheck);
			unfrozen.freeze();
			return unfrozen;
		}
	}

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
		return congruenceClosure.addElement(elem, omitSanityCheck);
	}

	public boolean isDebugMode() {
		return true;
	}

	public ILogger getLogger() {
		return mLogger;
	}

	public CongruenceClosure<ELEM> getSingleEqualityCc(final ELEM node1, final ELEM node2, final boolean modifiable) {
		final CongruenceClosure<ELEM> cc = getEmptyCc(modifiable);
		return reportEquality(node1, node2, cc, modifiable);
	}

	public CongruenceClosure<ELEM> getSingleDisequalityCc(final ELEM node1, final ELEM node2, final boolean modifiable) {
		final CongruenceClosure<ELEM> cc = getEmptyCc(modifiable);
		return reportDisequality(node1, node2, cc, modifiable);
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
			final Function<ELEM, ELEM> transformer) {
		final CongruenceClosure<ELEM> unfrozen = unfreeze(cc);
		unfrozen.transformElementsAndFunctions(transformer);
		unfrozen.freeze();
		// TODO: implement a result check here?
		return unfrozen;
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
			final CongruenceClosure<ELEM> unfrozen = unfreeze(cc);
			unfrozen.projectToElements(nodesToKeep, remInfo);
			unfrozen.freeze();
			// TODO: implement a result check here?
			return unfrozen;
		}
	}

	public CongruenceClosure<ELEM> addAllElements(final CongruenceClosure<ELEM> cc, final Set<ELEM> elemsToAdd,
			final IRemovalInfo<ELEM> remInfo, final boolean inplace) {
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
//			result.addElementRec(elem, remInfo);
			addElement(result, elem, true, true);
		}

		if (!inplace) {
			result.freeze();
		}

		return result;
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
}
