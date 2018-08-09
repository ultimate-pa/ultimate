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
import java.util.HashSet;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.EqualityStatus;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ThreeValuedEquivalenceRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.IPartialComparator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.PartialOrderCache;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.statistics.BenchmarkWithCounters;

public class CcManager<ELEM extends ICongruenceClosureElement<ELEM>> {

	private final IPartialComparator<CongruenceClosure<ELEM>> mCcComparator;

	private final ILogger mLogger;

	private final CongruenceClosure<ELEM> mInconsistentCc;

	private final CongruenceClosure<ELEM> mEmptyFrozenCc;

	private final PartialOrderCache<CongruenceClosure<ELEM>> mPartialOrderCache;

	private final boolean mBenchmarkMode;
	private BenchmarkWithCounters mBenchmark;

	private final SetConstraintManager<ELEM> mSetConstraintManager;

	public CcManager(final ILogger logger, final IPartialComparator<CongruenceClosure<ELEM>> ccComparator) {
		mLogger = logger;
		mCcComparator = ccComparator;

		mSetConstraintManager = new SetConstraintManager<>();

		mInconsistentCc = new CongruenceClosure<>(true);
		mInconsistentCc.freeze();

		mEmptyFrozenCc = new CongruenceClosure<>(this);
		mEmptyFrozenCc.freeze();

		if (CcSettings.UNIFY_CCS) {
	 		mPartialOrderCache = new PartialOrderCache<>(mCcComparator);
	 	} else {
	 		mPartialOrderCache = null;
	 	}

		mBenchmarkMode = true;
		if (mBenchmarkMode) {
			mBenchmark = new BenchmarkWithCounters();
			mBenchmark.registerCountersAndWatches(CcBmNames.getNames());
		} else {
			mBenchmark = null;
		}
	}

	private CongruenceClosure<ELEM> addToPartialOrderCache(final CongruenceClosure<ELEM> cc) {
		assert mPartialOrderCache != null;
//		assert cc.isFrozen();
		freezeIfNecessary(cc);
		final CongruenceClosure<ELEM> result = mPartialOrderCache.addElement(cc);
		assert CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_1
			|| (result.isStrongerThanNoCaching(cc) && cc.isStrongerThanNoCaching(result));
		/*
		 *  TODO: we do not work with/return the representative here because it might have a different expset!
		 *   (should make this method void probably)
		 */
		return cc;
	}

	public CongruenceClosure<ELEM> meet(final CongruenceClosure<ELEM> cc1, final CongruenceClosure<ELEM> cc2,
			final boolean inplace) {
		assert !CcSettings.FORBID_INPLACE || !inplace;
		CongruenceClosure<ELEM> result = meet(cc1, cc2, null, inplace);
		result = postProcessCcResult(result);
		return result;
	}

	private CongruenceClosure<ELEM> postProcessCcResult(final CongruenceClosure<ELEM> cc) {
		CongruenceClosure<ELEM> result = cc;
		if (CcSettings.UNIFY_CCS) {
//			assert result.isFrozen();
			if (cc.isFrozen()) {
				result = addToPartialOrderCache(cc);
			}
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
		bmStart(CcBmNames.MEET);
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
			bmEnd(CcBmNames.MEET);
			return cc2;
		}
		if (cc2.isTautological()) {
			bmEnd(CcBmNames.MEET);
			return cc1;
		}
		if (cc1.isInconsistent()) {
			bmEnd(CcBmNames.MEET);
			return cc1;
		}
		if (cc2.isInconsistent() && !inplace) {
			bmEnd(CcBmNames.MEET);
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
		bmEnd(CcBmNames.MEET);
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
		bmStart(CcBmNames.JOIN);
		/*
		 * Freeze-before-join politics.. -- might not be strictly necessary here, because CongruenceClosure-freeze
		 * triggers no propagations
		 */
		freezeIfNecessary(cc1);
		freezeIfNecessary(cc2);


		if (cc1.isInconsistent()) {
			bmEnd(CcBmNames.JOIN);
			return cc2;
		}
		if (cc2.isInconsistent()) {
			bmEnd(CcBmNames.JOIN);
			return cc1;
		}
		if (cc1.isTautological() || cc2.isTautological()) {
			bmEnd(CcBmNames.JOIN);
			return getEmptyCc(modifiable);
		}

		final CongruenceClosure<ELEM> result = cc1.join(cc2);

		if (!modifiable) {
			result.freeze();
		}
		assert modifiable != result.isFrozen();

		final CongruenceClosure<ELEM> resultPp = postProcessCcResult(result);
		bmEnd(CcBmNames.JOIN);
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
		final Set<CongruenceClosure<ELEM>> result = filterRedundantCcs(unionList, poc);
		return result;

	}

	public  IPartialComparator<CongruenceClosure<ELEM>> getCcComparator() {
		return mCcComparator;
	}

	public Set<CongruenceClosure<ELEM>> filterRedundantCcs(final Set<CongruenceClosure<ELEM>> unionList,
			final PartialOrderCache<CongruenceClosure<ELEM>> ccPoCache) {
		bmStart(CcBmNames.FILTERREDUNDANT);
		final Set<CongruenceClosure<ELEM>> maxReps = ccPoCache.getMaximalRepresentatives(unionList);
		// some additional processing: if maxReps is {False}, return the empty set
		assert !maxReps.stream().anyMatch(cc -> cc.isInconsistent()) || maxReps.size() == 1;
		if (maxReps.iterator().next().isInconsistent()) {
			bmEnd(CcBmNames.FILTERREDUNDANT);
			return Collections.emptySet();
		}

		bmEnd(CcBmNames.FILTERREDUNDANT);
		return maxReps;
	}

	public CongruenceClosure<ELEM> reportEquality(final ELEM node1, final ELEM node2,
			final CongruenceClosure<ELEM> origCc, final boolean inplace) {
		bmStart(CcBmNames.REPORT_EQUALITY);
		assert !CcSettings.FORBID_INPLACE || !inplace;
		if (inplace) {
			origCc.reportEquality(node1, node2);
			bmEnd(CcBmNames.REPORT_EQUALITY);
			return origCc;
		} else {
			final CongruenceClosure<ELEM> unfrozen = unfreeze(origCc);
			unfrozen.reportEquality(node1, node2);
			unfrozen.freeze();

			final CongruenceClosure<ELEM> resultPp = postProcessCcResult(unfrozen);
			bmEnd(CcBmNames.REPORT_EQUALITY);
			return resultPp;
		}
	}

	public CongruenceClosure<ELEM> reportDisequality(final ELEM node1, final ELEM node2,
			final CongruenceClosure<ELEM> origCc, final boolean inplace) {
		bmStart(CcBmNames.REPORT_DISEQUALITY);
		assert !CcSettings.FORBID_INPLACE || !inplace;
		if (inplace) {
			origCc.reportDisequality(node1, node2);
			bmEnd(CcBmNames.REPORT_DISEQUALITY);
			return origCc;
		} else {
			final CongruenceClosure<ELEM> unfrozen = unfreeze(origCc);
			unfrozen.reportDisequality(node1, node2);
			unfrozen.freeze();

			assert unfrozen.isInconsistent()
				|| unfrozen.getEqualityStatus(node1, node2) == EqualityStatus.NOT_EQUAL;
			final CongruenceClosure<ELEM> resultPp = postProcessCcResult(unfrozen);
			bmEnd(CcBmNames.REPORT_DISEQUALITY);
			return resultPp;
		}
	}

	public CongruenceClosure<ELEM> reportContainsConstraint(final ELEM elem, final Collection<ELEM> elementSet,
			final CongruenceClosure<ELEM> origCc,
			final boolean inplace) {
		return reportContainsConstraint(elem, Collections.singleton(mSetConstraintManager.buildSetConstraint(elementSet)),
				origCc, inplace);
	}


	public CongruenceClosure<ELEM> reportContainsConstraint(final ELEM elem, final Set<SetConstraint<ELEM>> elementSet,
			final CongruenceClosure<ELEM> origCc,
			final boolean inplace) {
		bmStart(CcBmNames.REPORTCONTAINS);
		assert !CcSettings.FORBID_INPLACE || !inplace;
		if (inplace) {
//			final SetConstraintConjunction<ELEM> newSetCc = buildSetConstraintConjunction(
//					origCc.getLiteralSetConstraints(), elem,
//					elementSet);
//					Collections.singleton(SetConstraint.buildSetConstraint(elementSet)));
//			origCc.reportContainsConstraint(elem, newSetCc.getSetConstraints());
			origCc.reportContainsConstraint(elem, elementSet);
			bmEnd(CcBmNames.REPORTCONTAINS);
			return origCc;
		} else {
			final CongruenceClosure<ELEM> unfrozen = unfreeze(origCc);
//			final SetConstraintConjunction<ELEM> newSetCc = buildSetConstraintConjunction(
//					unfrozen.getLiteralSetConstraints(), elem,
//					elementSet);
////					Collections.singleton(SetConstraint.buildSetConstraint(elementSet)));
//			unfrozen.reportContainsConstraint(elem, newSetCc.getSetConstraints());
			unfrozen.reportContainsConstraint(elem, elementSet);
			unfrozen.freeze();

			final CongruenceClosure<ELEM> resultPp = postProcessCcResult(unfrozen);
			bmEnd(CcBmNames.REPORTCONTAINS);
			return resultPp;
		}
	}

//	public CongruenceClosure<ELEM> reportContainsConstraint(final ELEM element,
//			final SetConstraintConjunction<ELEM> containsConstraintRaw,
//			final CongruenceClosure<ELEM> origCc, final boolean inplace) {
//
//		final ELEM elementRep = origCc.getRepresentativeElement(element);
//
//		// we are reporting this SetCc into a possibly new constraint --> remove surrounding constraint
//		final SetConstraintConjunction<ELEM> setCc =
//				new SetConstraintConjunction<>(null, containsConstraintRaw);
//		setCc.resetConstrainedElement(elementRep);
//
//		bmStart(CcBmNames.REPORTCONTAINS);
//		assert !CcSettings.FORBID_INPLACE || !inplace;
//		if (inplace) {
//			origCc.reportContainsConstraint(elementRep, setCc.getSetConstraints());
//			bmEnd(CcBmNames.REPORTCONTAINS);
//			return origCc;
//		} else {
//			final CongruenceClosure<ELEM> unfrozen = unfreeze(origCc);
//			unfrozen.reportContainsConstraint(elementRep, setCc.getSetConstraints());
//			unfrozen.freeze();
//
//			final CongruenceClosure<ELEM> resultPp = postProcessCcResult(unfrozen);
//			bmEnd(CcBmNames.REPORTCONTAINS);
//			return resultPp;
//		}
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
//			final CCLiteralSetConstraints<ELEM> literalConstraints,
			final boolean modifiable) {
		final CongruenceClosure<ELEM> result = new CongruenceClosure<>(this, tver);//, literalConstraints);
		if (!modifiable) {
			result.freeze();
		}
		return result;
	}

	public CongruenceClosure<ELEM> getCongruenceClosureFromTver(final ThreeValuedEquivalenceRelation<ELEM> tver,
			final IRemovalInfo<ELEM> removeElementInfo,
			final CCLiteralSetConstraints<ELEM> literalConstraints,
			final boolean modifiable) {
		final CongruenceClosure<ELEM> result = new CongruenceClosure<>(this, tver, literalConstraints,
				removeElementInfo);
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
		assert CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_3 || result.sanityCheck();
		final CongruenceClosure<ELEM> resultPp = postProcessCcResult(result);
		return resultPp;
	}

	public CongruenceClosure<ELEM> projectToElements(final CongruenceClosure<ELEM> cc, final Set<ELEM> nodesToKeep,
			final IRemovalInfo<ELEM> remInfo) {
		bmStart(CcBmNames.PROJECT_TO_ELEMENTS);
		if (CcSettings.PROJECTTOELEMENTS_INPLACE) {
			throw new AssertionError("CongruenceClosure.projectToElements is currently not suited for inplace "
					+ "operation");
		} else {
			/* the operation might be lossy, but here we treat a CongruenceClosure, so freezing for closing is not
			 * needed */
			final CongruenceClosure<ELEM> unfrozen = unfreezeIfNecessary(cc);
			final CongruenceClosure<ELEM> result = unfrozen.projectToElements(nodesToKeep, remInfo);
			result.freeze();
			// TODO: implement a result check here?
			final CongruenceClosure<ELEM> resultPp = postProcessCcResult(result);
			bmEnd(CcBmNames.PROJECT_TO_ELEMENTS);
			return resultPp;
		}
	}

	public CongruenceClosure<ELEM> addAllElements(final CongruenceClosure<ELEM> cc, final Collection<ELEM> elemsToAdd,
			final IRemovalInfo<ELEM> remInfo, final boolean inplace) {
		bmStart(CcBmNames.ADD_ALL_ELEMENTS);
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
		bmEnd(CcBmNames.ADD_ALL_ELEMENTS);
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

	public boolean isStrongerThan(final CongruenceClosure<ELEM> cc1, final CongruenceClosure<ELEM> cc2) {
		if (CcSettings.UNIFY_CCS) {
			bmStart(CcBmNames.IS_STRONGER_THAN_W_CACHING);
			final CongruenceClosure<ELEM> cc1Cached = addToPartialOrderCache(cc1);
			final CongruenceClosure<ELEM> cc2Cached = addToPartialOrderCache(cc2);
			final boolean result = mPartialOrderCache.lowerEqual(cc1Cached, cc2Cached);
			bmEnd(CcBmNames.IS_STRONGER_THAN_W_CACHING);
			return result;
		}
		return isStrongerThanNoCaching(cc1, cc2);
	}

	/**
		 * This is the "base" isStrongerThan insofar it is the backend to the cache, and does not use the cache!
	 *
	 * @param cc1
	 * @param cc2
	 * @return
	 */
	public boolean isStrongerThanNoCaching(final CongruenceClosure<ELEM> cc1, final CongruenceClosure<ELEM> cc2) {
		bmStart(CcBmNames.IS_STRONGER_THAN_NO_CACHING);

		if (cc1.isInconsistent()) {
			bmEnd(CcBmNames.IS_STRONGER_THAN_NO_CACHING);
			return true;
		}
		if (cc2.isInconsistent()) {
			// we know this != False, and other = False
			bmEnd(CcBmNames.IS_STRONGER_THAN_NO_CACHING);
			return false;
		}
		if (cc2.isTautological()) {
			bmEnd(CcBmNames.IS_STRONGER_THAN_NO_CACHING);
			return true;
		}
		if (cc1.isTautological()) {
			// we know other != True, and this = True
			bmEnd(CcBmNames.IS_STRONGER_THAN_NO_CACHING);
			return false;
		}
		final Pair<CongruenceClosure<ELEM>, CongruenceClosure<ELEM>> aligned = alignElements(cc1, cc2,
				CcSettings.ALIGN_INPLACE && !cc1.isFrozen() && !cc2.isFrozen());
		final CongruenceClosure<ELEM> thisAligned = aligned.getFirst();
		final CongruenceClosure<ELEM> otherAligned = aligned.getSecond();


		assert assertElementsAreSuperset(thisAligned, otherAligned);
		assert assertElementsAreSuperset(otherAligned, thisAligned);

		final boolean result = checkIsStrongerThan(thisAligned, otherAligned);
		bmEnd(CcBmNames.IS_STRONGER_THAN_NO_CACHING);
		return result;
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
		if (!areDisequalitiesStrongerThan(thisAligned, otherAligned)) {
			return false;
		}


		if (!thisAligned.getLiteralSetConstraints().isStrongerThan(otherAligned.getLiteralSetConstraints())) {
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

		final Pair<CongruenceClosure<ELEM>, CongruenceClosure<ELEM>> aligned = alignElements(cc1, cc2,
				CcSettings.ALIGN_INPLACE && !cc1.isFrozen() && !cc2.isFrozen());
		final CongruenceClosure<ELEM> thisAligned = aligned.getFirst();
		final CongruenceClosure<ELEM> otherAligned = aligned.getSecond();
		return checkIsStrongerThan(thisAligned, otherAligned) && checkIsStrongerThan(otherAligned, thisAligned);
	}

	public Pair<CongruenceClosure<ELEM>, CongruenceClosure<ELEM>> alignElements(final CongruenceClosure<ELEM> cc1,
			final CongruenceClosure<ELEM> cc2, final boolean inplace) {
		assert !inplace || !cc1.isFrozen();
		assert !inplace || !cc2.isFrozen();
		if (inplace) {
			bmStart(CcBmNames.ALIGN_ELEMENTS);

			addAllElements(cc1, cc2.getAllElements(), null, true);
			addAllElements(cc2, cc1.getAllElements(), null, true);

			/* this single call is not enough for aligning because constant arrays may introduce elements when other
			 * elements are added based on equalities in that constraint
			 */
			while (!cc1.getAllElements().containsAll(cc2.getAllElements())
					|| !cc2.getAllElements().containsAll(cc1.getAllElements())) {
				addAllElements(cc1, cc2.getAllElements(), null, true);
				addAllElements(cc2, cc1.getAllElements(), null, true);
			}

			bmEnd(CcBmNames.ALIGN_ELEMENTS);
			return new Pair<>(cc1, cc2);
		} else {
			// not inplace

			bmStart(CcBmNames.ALIGN_ELEMENTS);

			final CongruenceClosure<ELEM> cc1Aligned = copyNoRemInfoUnfrozen(cc1);
			final CongruenceClosure<ELEM> cc2Aligned = copyNoRemInfoUnfrozen(cc2);

			addAllElements(cc1Aligned, cc2Aligned.getAllElements(), null, true);
			addAllElements(cc2Aligned, cc1Aligned.getAllElements(), null, true);

			/* this single call is not enough for aligning because constant arrays may introduce elements when other
			 * elements are added based on equalities in that constraint
			 */
			while (!cc1Aligned.getAllElements().containsAll(cc2Aligned.getAllElements())
					|| !cc2Aligned.getAllElements().containsAll(cc1Aligned.getAllElements())) {
				addAllElements(cc1Aligned, cc2Aligned.getAllElements(), null, true);
				addAllElements(cc2Aligned, cc1Aligned.getAllElements(), null, true);

			}

			cc1Aligned.freeze();
			cc2Aligned.freeze();

			bmEnd(CcBmNames.ALIGN_ELEMENTS);
			return new Pair<>(cc1Aligned, cc2Aligned);
		}
	}

	private static <E extends ICongruenceClosureElement<E>>
			boolean areDisequalitiesStrongerThan(final CongruenceClosure<E> left,
					final CongruenceClosure<E> right) {
		for (final E rep : right.getAllRepresentatives()) {
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
	static <E> boolean isPartitionStronger(final ThreeValuedEquivalenceRelation<E> first,
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

	/**
	 * Note this will throw out all singleton constraints assuming the corresponding equalities have been reported
	 * before!
	 *
	 * @param surroundingSetConstraints
	 * @param constrainedElement
	 * @param setConstraintsIn
	 * @return
	 */
	public SetConstraintConjunction<ELEM> buildSetConstraintConjunction(
			final CCLiteralSetConstraints<ELEM> surroundingSetConstraints,
			final ELEM constrainedElement,
			final Set<SetConstraint<ELEM>> setConstraintsIn) {
		bmStart(CcBmNames.BUILD_SET_CONSTRAINT_CONJUNCTION);

		final Set<SetConstraint<ELEM>> setConstraintsUpdRepr =
				mSetConstraintManager.updateOnChangedRepresentative(setConstraintsIn,
						surroundingSetConstraints.getCongruenceClosure());
//		assert setConstraintsUpdRepr == setConstraintsIn : "if this never fails, we can remove that updaterep operation";

		final Set<SetConstraint<ELEM>> filtered1 = normalizeSetConstraintConjunction(surroundingSetConstraints,
				setConstraintsUpdRepr);


		// throw away all singletons, as they were (must have been!) reported as equalities
		// throw away all tautological constraints
		final Set<SetConstraint<ELEM>> filtered2 = filtered1.stream()
				.filter(sc -> !sc.isSingleton())
				.filter(sc -> !SetConstraint.isTautological(constrainedElement, sc))
				.collect(Collectors.toSet());


		assert !filtered2.stream().anyMatch(sc -> sc.isInconsistent()) || filtered2.size() == 1
				: "not correctly normalized: there is a 'false' conjunct, but it is not the only conjunct";

		if (filtered2.size() == 1 && filtered2.iterator().next().isInconsistent()) {
			bmEnd(CcBmNames.BUILD_SET_CONSTRAINT_CONJUNCTION);
			return new SetConstraintConjunction<>(true);
		}

		final SetConstraintConjunction<ELEM> result =
				new SetConstraintConjunction<>(surroundingSetConstraints, constrainedElement, filtered2);

		bmEnd(CcBmNames.BUILD_SET_CONSTRAINT_CONJUNCTION);
		return  result;
	}

	/**
	 * Apply normalizations, e.g.,
	 *  <li> expansion of literals if possible according to surroundingSetConstraints
	 *
	 * note that this normalization is not wrt any constrained element! (e.g. the filtering for x in {x} must happen
	 * outside of this method)
	 *
	 * @param surroundingSetConstraints used to: expand literals, compute meet
	 * @param setConstraintsIn
	 * @return
	 */
	public Set<SetConstraint<ELEM>> normalizeSetConstraintConjunction(
			final CCLiteralSetConstraints<ELEM> surroundingSetConstraints,
			final Collection<SetConstraint<ELEM>> setConstraintsIn) {
		bmStart(CcBmNames.NORMALIZE_SET_CONSTRAINT_CONJUNCTION);

		// expand non-literals if possible (in-place on SetConstraints)
		final Set<SetConstraint<ELEM>> expanded = new HashSet<>(setConstraintsIn);
		{
			final HashRelation<ELEM, ELEM> elemToExpansion = surroundingSetConstraints.getElemToExpansion();

			for (final SetConstraint<ELEM> sc : setConstraintsIn) {
				for (final ELEM e : sc.getNonLiterals()) {
					final Set<ELEM> expansion = elemToExpansion.getImage(e);
					if (!expansion.isEmpty()) {
						expanded.add(mSetConstraintManager.expandNonLiteral(sc, e, expansion));
					}
				}
			}
		}


		//TODO: only instantiate SetConstraintComparator once??
		final PartialOrderCache<SetConstraint<ELEM>> poc1 = new PartialOrderCache<>(
				mSetConstraintManager.getSetConstraintComparator());
		final Set<SetConstraint<ELEM>> filtered1 = poc1.getMaximalRepresentatives(expanded);

		// check for inconsistency
		for (final SetConstraint<ELEM> sc : filtered1) {
			if (sc.isInconsistent()) {
				bmEnd(CcBmNames.NORMALIZE_SET_CONSTRAINT_CONJUNCTION);
				return Collections.singleton(sc);
			}
			// bs -- example: x in {1} /\ x in {0}
//			if (sc.isSingleton()) {
//				return Collections.singleton(sc);
//			}
		}

		// check for tautology
		if (filtered1.isEmpty()) {
			bmEnd(CcBmNames.NORMALIZE_SET_CONSTRAINT_CONJUNCTION);
			return Collections.emptySet();
		}

		final Set<SetConstraint<ELEM>> all = new HashSet<>();

		// introduce all the conjunctive constraints according to all the subsets..
		for (final Set<SetConstraint<ELEM>> subSet : DataStructureUtils.powerSet(filtered1)) {
			final SetConstraint<ELEM> meet = mSetConstraintManager.meet(surroundingSetConstraints, subSet);

			if (meet == null) {
				// "Top" constraint, represented by "null", no need to add to a conjunction
				continue;
			}

			if (meet.isInconsistent()) {
				// created inconsistent constraint
				bmEnd(CcBmNames.NORMALIZE_SET_CONSTRAINT_CONJUNCTION);
				return Collections.singleton(meet);
			}

			all.add(meet);
		}

		//TODO: only instantiate SetConstraintComparator once??
		final PartialOrderCache<SetConstraint<ELEM>> poc =
				new PartialOrderCache<>(mSetConstraintManager.getSetConstraintComparator());
		final Set<SetConstraint<ELEM>> filtered = poc.getMaximalRepresentatives(all);

		// check for tautology
		if (filtered.isEmpty()) {
			bmEnd(CcBmNames.NORMALIZE_SET_CONSTRAINT_CONJUNCTION);
			return null;
		}

		assert SetConstraintConjunction.sanityCheck(filtered);
		bmEnd(CcBmNames.NORMALIZE_SET_CONSTRAINT_CONJUNCTION);
		return filtered;
	}


	public BenchmarkWithCounters getBenchmark() {
		return mBenchmark;
	}

	private void bmStartOverall() {
		if (!mBenchmarkMode) {
			return;
		}
		mBenchmark.incrementCounter(CcBmNames.OVERALL.name());
		mBenchmark.unpauseWatch(CcBmNames.OVERALL.name());
	}

	private void bmEndOverall() {
		if (!mBenchmarkMode) {
			return;
		}
		mBenchmark.pauseWatch(CcBmNames.OVERALL.name());
	}

	private void bmStart(final CcBmNames watch) {
		if (!mBenchmarkMode) {
			return;
		}
		bmStartOverall();
		mBenchmark.incrementCounter(watch.name());
		mBenchmark.unpauseWatch(watch.name());
	}

	private void bmEnd(final CcBmNames watch) {
		if (!mBenchmarkMode) {
			return;
		}
		bmEndOverall();
		mBenchmark.pauseWatch(watch.name());
	}

	private static enum CcBmNames {

		FILTERREDUNDANT, UNFREEZE, COPY, MEET, JOIN, REMOVE, IS_STRONGER_THAN_NO_CACHING, ADDNODE, REPORTCONTAINS,
		REPORT_EQUALITY, REPORT_DISEQUALITY, PROJECT_TO_ELEMENTS, ADD_ALL_ELEMENTS, ALIGN_ELEMENTS, OVERALL,
		IS_STRONGER_THAN_W_CACHING, BUILD_SET_CONSTRAINT_CONJUNCTION, NORMALIZE_SET_CONSTRAINT_CONJUNCTION;

		static String[] getNames() {
			final String[] result = new String[values().length];
			for (int i = 0; i < values().length; i++) {
				result[i] = values()[i].name();
			}
			return result;
		}
	}

	public boolean hasPartialOrderCacheBenchmark() {
		if (mPartialOrderCache == null) {
			return false;
		}
		return mPartialOrderCache.hasBenchmark();
	}

	public BenchmarkWithCounters getPartialOrderCacheBenchmark() {
		return mPartialOrderCache.getBenchmark();
	}

	public SetConstraintManager<ELEM> getSetConstraintManager() {
		return mSetConstraintManager;
	}

	/**
	 *
	 * @param ccWithBroaderPartition (broader == stronger == more constraining)
	 * @param ccWithFinerPartition
	 * @return
	 */
	public static <ELEM extends ICongruenceClosureElement<ELEM>> HashRelation<ELEM, ELEM> computeSplitInfo(
			final CongruenceClosure<ELEM> ccWithBroaderPartition,
			final CongruenceClosure<ELEM> ccWithFinerPartition) {
		assert CcManager.isPartitionStronger(ccWithBroaderPartition.mElementTVER,
				ccWithFinerPartition.mElementTVER) : "assuming this has been checked already";

		final HashRelation<ELEM, ELEM> result = new HashRelation<>();

		for (final ELEM finerRep : ccWithFinerPartition.getAllRepresentatives()) {
			final ELEM broaderRep = ccWithBroaderPartition.getRepresentativeElement(finerRep);
			result.addPair(broaderRep, finerRep);
		}

		return result;
	}
}
