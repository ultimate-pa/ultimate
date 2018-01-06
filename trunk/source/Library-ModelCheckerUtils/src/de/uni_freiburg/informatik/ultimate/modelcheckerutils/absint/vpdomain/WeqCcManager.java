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
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.BiPredicate;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSort;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BidirectionalMap;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.CcManager;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.CongruenceClosure;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.ICongruenceClosure;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.IRemovalInfo;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.IPartialComparator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.PartialOrderCache;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

public class WeqCcManager<NODE extends IEqNodeIdentifier<NODE>> {

	private final IPartialComparator<WeqCongruenceClosure<NODE>> mWeqCcComparator;

	private final CcManager<NODE> mCcManager;
	private final ManagedScript mMgdScript;
	private final ILogger mLogger;

	private final WeqCongruenceClosure<NODE> mTautologicalWeqCc;
	private final WeqCongruenceClosure<NODE> mInconsistentWeqCc;

	private final NestedMap2<Sort, Integer, NODE> mDimensionToWeqVariableNode;
	private final BidirectionalMap<Term, Term> mWeqVarsToWeqPrimedVars;

	private final AbstractNodeAndFunctionFactory<NODE, Term> mNodeAndFunctionFactory;

	final boolean mDebug;
	final boolean mSkipSolverChecks = false;

	public WeqCcManager(final ILogger logger, final IPartialComparator<WeqCongruenceClosure<NODE>> weqCcComparator,
			final IPartialComparator<CongruenceClosure<NODE>> ccComparator, final ManagedScript mgdScript,
			final AbstractNodeAndFunctionFactory<NODE, Term> nodeAndFunctionFactory, final boolean debugMode) {
		mCcManager = new CcManager<>(logger, ccComparator);
		mMgdScript = mgdScript;
		mLogger = logger;
		mDebug = debugMode;

		mWeqCcComparator = weqCcComparator;

		mTautologicalWeqCc = new WeqCongruenceClosure<>(this);
		mTautologicalWeqCc.freeze();

		mInconsistentWeqCc = new WeqCongruenceClosure<>(true);

		mDimensionToWeqVariableNode = new NestedMap2<>();
		mWeqVarsToWeqPrimedVars = new BidirectionalMap<>();

		mNodeAndFunctionFactory = nodeAndFunctionFactory;
	}

	public WeqCongruenceClosure<NODE> getEmptyWeqCc(final boolean modifiable) {
		if (modifiable) {
			return new WeqCongruenceClosure<>(this);
		} else {
			return mTautologicalWeqCc;
		}
	}

	public WeqCongruenceClosure<NODE> getInconsistentWeqCc(final boolean modifiable) {
		if (modifiable) {
			return new WeqCongruenceClosure<>(true);
		} else {
			return mInconsistentWeqCc;
		}
	}

	WeqCongruenceClosure<NODE> getWeqMeet(final WeqCongruenceClosure<NODE> weqcc, final CongruenceClosure<NODE> cc,
			final IRemovalInfo<NODE> remInfo, final boolean inplace) {

		final WeqCongruenceClosure<NODE> result;
		if (remInfo == null) {
			result = weqcc.meetRec(cc, inplace);
		} else {
			assert false : "do we need this case?";
			result = null;
		}
		return result;
	}

	public WeqCongruenceClosure<NODE> getWeqMeet(final WeqCongruenceClosure<NODE> weqcc,
			final CongruenceClosure<NODE> cc, final boolean inplace) {
		return getWeqMeet(weqcc, cc, null, inplace);
	}

	public WeqCongruenceClosure<NODE> addNode(final NODE node, final WeqCongruenceClosure<NODE> origWeqCc,
			final boolean inplace, final boolean omitSanityChecks) {
		if (origWeqCc.hasElement(node)) {
			// node is already present --> nothing to do
			return origWeqCc;
		}

		final WeqCongruenceClosure<NODE> result;
		if (inplace) {
			origWeqCc.addElement(node, omitSanityChecks);
			result = origWeqCc;
		} else {
			final WeqCongruenceClosure<NODE> unfrozen = unfreeze(origWeqCc);
			unfrozen.addElement(node, omitSanityChecks);
			unfrozen.freeze();
			result = unfrozen;
		}

		assert omitSanityChecks || origWeqCc.sanityCheck();

		return result;
	}

	<DISJUNCT extends ICongruenceClosure<NODE>> DISJUNCT unfreeze(final DISJUNCT orig) {
		if (orig instanceof CongruenceClosure<?>) {
			return (DISJUNCT) mCcManager.unfreeze((CongruenceClosure<NODE>) orig);
		} else {
			return (DISJUNCT) unfreeze((WeqCongruenceClosure<NODE>) orig);

		}
	}


//	/**
//	 * Unfreezes the given weqcc and all of its components (transitively)
//	 *
//	 * @param origWeqCc
//	 * @return
//	 */
//	WeqCongruenceClosure<NODE> unfreezeDeep(final WeqCongruenceClosure<NODE> origWeqCc) {
//		assert origWeqCc.isFrozen();
////		final WeqCongruenceClosure<NODE> result = new WeqCongruenceClosure<>(origWeqCc, true);
//		final WeqCongruenceClosure<NODE> result = new WeqCongruenceClosure<>(origWeqCc);
//		assert !result.isFrozen();
//		assert result.sanityCheck();
//		assert !result.getCongruenceClosure().isFrozen();
//		assert result.getWeakEquivalenceGraph().assertLabelsAreUnfrozen();
//		return result;
//	}


	WeqCongruenceClosure<NODE> unfreeze(final WeqCongruenceClosure<NODE> origWeqCc) {
		assert origWeqCc.isFrozen();
//		final WeqCongruenceClosure<NODE> result = new WeqCongruenceClosure<>(origWeqCc);
		final WeqCongruenceClosure<NODE> result = copyWeqCc(origWeqCc, true);
		assert !result.isFrozen();
		assert result.sanityCheck();
//		assert !result.getCongruenceClosure().isFrozen();
//		assert result.getWeakEquivalenceGraph().assertLabelsAreUnfrozen();
		return result;
	}


	public <DISJUNCT extends ICongruenceClosure<NODE>> WeakEquivalenceEdgeLabel<NODE, DISJUNCT> filterRedundantICcs(
			final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> label) {
		return new WeakEquivalenceEdgeLabel<>(label.getWeqGraph(), filterRedundantICcs(label.getDisjuncts()));
	}

	public <DISJUNCT extends ICongruenceClosure<NODE>> Set<DISJUNCT> filterRedundantICcs(final Set<DISJUNCT> ccs,
			final PartialOrderCache<DISJUNCT> ccPoCache) {
		if (ccs.isEmpty()) {
			return ccs;
		}
		final DISJUNCT sample = ccs.iterator().next();
		if (sample instanceof CongruenceClosure<?>) {
			return (Set<DISJUNCT>) filterRedundantCcs((Set<CongruenceClosure<NODE>>) ccs,
					(PartialOrderCache<CongruenceClosure<NODE>>) ccPoCache);
		} else {
			throw new AssertionError();
		}
	}

	public WeakEquivalenceEdgeLabel<NODE, CongruenceClosure<NODE>> filterRedundantCcs(
			final WeakEquivalenceEdgeLabel<NODE, CongruenceClosure<NODE>> label) {
		final Set<CongruenceClosure<NODE>> filtered = mCcManager.filterRedundantCcs(label.getDisjuncts());
		return new WeakEquivalenceEdgeLabel<>(label.getWeqGraph(), filtered);
	}

	public <DISJUNCT extends ICongruenceClosure<NODE>> Set<DISJUNCT> filterRedundantICcs(final Set<DISJUNCT> ccs) {
		if (ccs.isEmpty()) {
			return ccs;
		}
		final DISJUNCT sample = ccs.iterator().next();
		Set<DISJUNCT> result;
		if (sample instanceof CongruenceClosure<?>) {
			result = (Set<DISJUNCT>) filterRedundantCcs((Set<CongruenceClosure<NODE>>) ccs);
		} else {
			result = (Set<DISJUNCT>) filterRedundantWeqCcs((Set<WeqCongruenceClosure<NODE>>) ccs);
		}
		assert checkFilterDisjunctionResult(ccs, result);
		return result;
	}

	private Set<WeqCongruenceClosure<NODE>> filterRedundantWeqCcs(final Set<WeqCongruenceClosure<NODE>> ccs) {
		final PartialOrderCache<WeqCongruenceClosure<NODE>> poc = new PartialOrderCache<>(mWeqCcComparator);
		return poc.getMaximalRepresentatives(ccs);
	}

	public Set<CongruenceClosure<NODE>> filterRedundantCcs(final Set<CongruenceClosure<NODE>> ccs) {
		return mCcManager.filterRedundantCcs(ccs);
	}

	public Set<CongruenceClosure<NODE>> filterRedundantCcs(final Set<CongruenceClosure<NODE>> ccs,
			final PartialOrderCache<CongruenceClosure<NODE>> ccPoCache) {
		return mCcManager.filterRedundantCcs(ccs, ccPoCache);
	}

	public IPartialComparator<CongruenceClosure<NODE>> getCcComparator() {
		return mCcManager.getCcComparator();
	}

	public <DISJUNCT extends ICongruenceClosure<NODE>> IPartialComparator<DISJUNCT> getICcComparator(
			final DISJUNCT emptyDisjunct) {
		if (emptyDisjunct instanceof CongruenceClosure<?>) {
			return (IPartialComparator<DISJUNCT>) getCcComparator();
		} else {
			throw new AssertionError();
		}
	}

	public WeqCongruenceClosure<NODE> reportEquality(final WeqCongruenceClosure<NODE> origWeqCc, final NODE node1,
			final NODE node2, final boolean inplace) {
		if (inplace) {
			origWeqCc.reportEquality(node1, node2, false);
			return origWeqCc;
		} else {
			final WeqCongruenceClosure<NODE> unfrozen = unfreeze(origWeqCc);
			unfrozen.reportEquality(node1, node2, false);
			unfrozen.freeze();
			assert checkReportEqualityResult(origWeqCc, node1, node2, unfrozen);
			return unfrozen;
		}
	}

	private CongruenceClosure<NODE> reportEquality(final CongruenceClosure<NODE> origCc, final NODE node1,
			final NODE node2, final boolean inplace) {
		final CongruenceClosure<NODE> result = mCcManager.reportEquality(node1, node2, origCc, inplace);
		assert checkReportEqualityResult(origCc, node1, node2, result);
		return result;
	}

	public WeqCongruenceClosure<NODE> reportDisequality(final WeqCongruenceClosure<NODE> origWeqCc, final NODE node1,
			final NODE node2, final boolean inplace) {
		if (inplace) {
			origWeqCc.reportDisequality(node1, node2);
			return origWeqCc;
		} else {
			final WeqCongruenceClosure<NODE> unfrozen = unfreeze(origWeqCc);
			unfrozen.reportDisequality(node1, node2);
			unfrozen.freeze();
			assert checkReportDisequalityResult(origWeqCc, node1, node2, unfrozen);
			return unfrozen;
		}
	}

	public WeqCongruenceClosure<NODE> reportWeakEquivalence(final WeqCongruenceClosure<NODE> origWeqCc,
			final NODE array1, final NODE array2, final NODE storeIndex, final boolean inplace) {
		if (inplace) {
			origWeqCc.reportWeakEquivalence(array1, array2, storeIndex, false);
			return origWeqCc;
		} else {
			final WeqCongruenceClosure<NODE> unfrozen = unfreeze(origWeqCc);
			unfrozen.reportWeakEquivalence(array1, array2, storeIndex, false);
			unfrozen.freeze();
			assert checkReportWeakEquivalenceResult(origWeqCc, array1, array2, storeIndex, unfrozen);
			return unfrozen;
		}
	}

	public WeqCongruenceClosure<NODE> projectAway(final WeqCongruenceClosure<NODE> origWeqCc, final NODE node) {
		// TODO: unsure about this freezing -- is there a more efficient solution?
		freezeIfNecessary(origWeqCc);

		final WeqCongruenceClosure<NODE> unfrozen = unfreeze(origWeqCc);
		RemoveWeqCcElement.removeSimpleElement(unfrozen, node);
		unfrozen.freeze();
		assert checkProjectAwayResult(origWeqCc, node, unfrozen);
		return unfrozen;
	}

	public <DISJUNCT extends ICongruenceClosure<NODE>> WeakEquivalenceGraph<NODE, DISJUNCT> flattenWeqLabels(
			final WeakEquivalenceGraph<NODE, DISJUNCT> origWeqGraph, final WeqCongruenceClosure<NODE> baseWeqCc) {

		final WeakEquivalenceGraph<NODE, DISJUNCT> result =
				new WeakEquivalenceGraph<>(baseWeqCc, this, origWeqGraph.getEmptyDisjunct());

		for (final Entry<Doubleton<NODE>, WeakEquivalenceEdgeLabel<NODE, DISJUNCT>> weqEdge
				: origWeqGraph.getEdges().entrySet()) {

			// make sure that the representatives in pArr and in our new weq edges are compatible
			final Doubleton<NODE> newSourceAndTarget = new Doubleton<>(
					baseWeqCc.getRepresentativeElement(weqEdge.getKey().getOneElement()),
					baseWeqCc.getRepresentativeElement(weqEdge.getKey().getOtherElement()));

			final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> flattenedEdgeLabel = weqEdge.getValue().flatten(result);
			result.putEdgeLabel(newSourceAndTarget, flattenedEdgeLabel);
		}
		return result;
	}

	public WeqCongruenceClosure<NODE> makeCopyForWeqMeet(final WeqCongruenceClosure<NODE> originalPa,
			final boolean modifiable) {
		if (WeqSettings.SANITYCHECK_FINE_GRAINED) {
			assert originalPa.sanityCheck();
		}

		// note that we use the old WeqCc here as parameter, the field in WeqGraph will be reset by getWeqCongruenceCl..
		final WeakEquivalenceGraph<NODE, CongruenceClosure<NODE>> newWeqGraph =
				WeqSettings.FLATTEN_WEQ_EDGES_BEFORE_JOIN ?
				flattenWeqLabels(originalPa.getWeakEquivalenceGraph(), originalPa) :
					copy(originalPa.getWeakEquivalenceGraph());

		final WeqCongruenceClosure<NODE> result = getWeqCongruenceClosure(originalPa.getCongruenceClosure(),
				newWeqGraph, true);
		result.setDiet(Diet.TRANSITORY_THIN_TO_WEQCCFAT);
		result.setIsEdgeLabelDisjunct();

		if (!modifiable) {
			result.freeze();
		}
		assert result.sanityCheck();
		return result;
	}

	private <DISJUNCT extends ICongruenceClosure<NODE>> WeakEquivalenceGraph<NODE, DISJUNCT> copy(
			final WeakEquivalenceGraph<NODE, DISJUNCT> weakEquivalenceGraph) {
		return new WeakEquivalenceGraph<>(weakEquivalenceGraph.getBaseWeqCc(), weakEquivalenceGraph);
	}

//	/**
//	 * Could also be called "makeSnapshot"
//	 * Used when we want to use a WeqCc but also want to remember its original state.
//	 * This is called when we need a copy in any case (roughly..)
//	 * If we are doing things inplace, we may need a copy from time to time, that is the purpose of this method.
//	 * If the manager freezes everything before returning it, and the original is frozen, we don't need to make a copy
//	 * here.
//	 * TODO: not entirely clear.. think through..
//	 * @param original
//	 * @return
//	 */
//	public WeqCongruenceClosure<NODE> getFrozenCopy(final WeqCongruenceClosure<NODE> original) {
//		if (WeqSettings.FREEZE_ALL_IN_MANAGER && original.isFrozen()) {
//			// original is frozen --> a copy should not be necessary (use unfreeze if an
//			// unfrozen copy is needed)
//			return original;
//		}
//		final WeqCongruenceClosure<NODE> copy = new WeqCongruenceClosure<>(original, false);
//		if (WeqSettings.FREEZE_ALL_IN_MANAGER) {
//			copy.freeze();
//		}
//		return copy;
//	}

	public <DISJUNCT extends ICongruenceClosure<NODE>> DISJUNCT meet(final DISJUNCT icc1,
			final DISJUNCT icc2, final IRemovalInfo<NODE> remInfo, final boolean inplace) {
		assert icc1.getClass().equals(icc2.getClass());
		if (icc1.getClass().equals(CongruenceClosure.class)) {
			return (DISJUNCT) meet((CongruenceClosure<NODE>) icc1, (CongruenceClosure<NODE>) icc2, remInfo, inplace);
		} else {
			throw new AssertionError("unexpected, does this happen??");
//			assert icc1.getClass().equals(WeqCongruenceClosure.class);
//			return meet((WeqCongruenceClosure<NODE>) icc1, (WeqCongruenceClosure<NODE>) icc2, inplace);
		}
	}

	public <DISJUNCT extends ICongruenceClosure<NODE>> DISJUNCT meet(final DISJUNCT icc1, final DISJUNCT icc2,
			final boolean inplace) {
		if (!inplace) {
			freezeIfNecessary(icc1);
			freezeIfNecessary(icc2);
		}

//		assert icc1.isFrozen() != inplace;
		assert !inplace || !icc1.isFrozen();
		assert icc2.isFrozen() == icc1.isFrozen();
		assert icc1.getClass().equals(icc2.getClass());
		if (icc1.getClass().equals(CongruenceClosure.class)) {
			return (DISJUNCT) meet((CongruenceClosure<NODE>) icc1, (CongruenceClosure<NODE>) icc2, inplace);
		} else {
			assert icc1.getClass().equals(WeqCongruenceClosure.class);
			return (DISJUNCT) meet((WeqCongruenceClosure<NODE>) icc1, (WeqCongruenceClosure<NODE>) icc2, inplace);
		}
	}

	public WeqCongruenceClosure<NODE> meet(final WeqCongruenceClosure<NODE> weqcc1,
			final WeqCongruenceClosure<NODE> weqcc2, final boolean inplace) {
		if (inplace) {
			WeqCongruenceClosure<NODE> weqcc1_old = null;
			if (mDebug) {
//				weqcc1_old = getFrozenCopy(weqcc1);
				weqcc1_old = copyWeqCc(weqcc1, false);
			}
			weqcc1.meet(weqcc2, true);
			if (mDebug) {
				assert checkMeetResult(weqcc1_old, weqcc2, weqcc1);
			}
			return weqcc1;
		} else {
			freezeIfNecessary(weqcc1);
			final WeqCongruenceClosure<NODE> result = weqcc1.meet(weqcc2, false);

			freezeIfNecessary(result);

			assert checkMeetResult(weqcc1, weqcc2, result);
			return result;
		}
	}


	public CongruenceClosure<NODE> meet(final CongruenceClosure<NODE> cc1, final CongruenceClosure<NODE> cc2,
			final boolean inplace) {
		return meet(cc1, cc2, null, inplace);
	}

	public CongruenceClosure<NODE> meet(final CongruenceClosure<NODE> cc1, final CongruenceClosure<NODE> cc2,
			final IRemovalInfo<NODE> elementCurrentlyBeingRemoved, final boolean inplace) {
		// (just passing it through to CcManager)
		CongruenceClosure<NODE> cc1_old = null;
		if (mDebug && inplace) {
			cc1_old = mCcManager.copyNoRemInfo(cc1);
		} else if (mDebug && !inplace) {
			cc1_old = cc1;
		}

		final CongruenceClosure<NODE> result = mCcManager.meet(cc1, cc2, elementCurrentlyBeingRemoved, inplace);

		if (mDebug) {
				assert checkMeetResult(cc1_old, cc2, result);
		}

		return result;
	}

	public <DISJUNCT extends ICongruenceClosure<NODE>> DISJUNCT join(final DISJUNCT icc1,
			final DISJUNCT icc2, final boolean modifiable) {
		assert icc1.getClass().equals(icc2.getClass());
		if (icc1.getClass().equals(CongruenceClosure.class)) {
			return (DISJUNCT) join((CongruenceClosure<NODE>) icc1, (CongruenceClosure<NODE>) icc2, modifiable);
		} else {
			assert icc1.getClass().equals(WeqCongruenceClosure.class);
			return (DISJUNCT) join((WeqCongruenceClosure<NODE>) icc1, (WeqCongruenceClosure<NODE>) icc2, modifiable);
		}
	}

	public CongruenceClosure<NODE> join(final CongruenceClosure<NODE> cc1, final CongruenceClosure<NODE> cc2,
			final boolean modifiable) {
		// (just passing it through to CcManager)
		final CongruenceClosure<NODE> result = mCcManager.join(cc1, cc2, modifiable);
		assert checkJoinResult(cc1, cc2, result);
		return result;
	}

	public WeqCongruenceClosure<NODE> join(final WeqCongruenceClosure<NODE> weqcc1,
			final WeqCongruenceClosure<NODE> weqcc2, final boolean modifiable) {
		freezeIfNecessary(weqcc1);
		freezeIfNecessary(weqcc2);

		if (weqcc1.isInconsistent()) {
			return weqcc2;
		}
		if (weqcc2.isInconsistent()) {
			return weqcc1;
		}
		if (weqcc1.isTautological() || weqcc2.isTautological()) {
			return getEmptyWeqCc(modifiable);
		}

		final WeqCongruenceClosure<NODE> result = weqcc1.join(weqcc2);
		assert result != weqcc1 && result != weqcc2 : "join should construct a new object";
		if (!modifiable) {
			result.freeze();
		}
		assert checkJoinResult(weqcc1, weqcc2, result);
		return result;
	}

	private void freezeIfNecessary(final WeqCongruenceClosure<NODE> weqcc) {
		if (!weqcc.isFrozen()) {
			weqcc.freeze();
		}
	}

	public CongruenceClosure<NODE> renameVariablesCc(final CongruenceClosure<NODE> weqCc,
			final Map<Term, Term> substitutionMapping, final boolean inplace) {
		return mCcManager.transformElements(weqCc, e -> e.renameVariables(substitutionMapping), inplace);
	}

	public WeqCongruenceClosure<NODE> renameVariables(final WeqCongruenceClosure<NODE> weqCc,
			final Map<Term, Term> substitutionMapping, final boolean inplace) {
		assert DataStructureUtils.intersection(new HashSet<>(substitutionMapping.values()),
				new HashSet<>(weqCc.getCongruenceClosure().getAllElements())).isEmpty();

		if (inplace) {
			assert !weqCc.isFrozen();
			weqCc.transformElementsAndFunctions(e -> e.renameVariables(substitutionMapping));
			return weqCc;
		} else {
			final WeqCongruenceClosure<NODE> unfrozen = unfreeze(weqCc);
			unfrozen.transformElementsAndFunctions(e -> e.renameVariables(substitutionMapping));
			unfrozen.freeze();
			// TODO: implement a result check here?
			return unfrozen;
		}
	}

	public <DISJUNCT extends ICongruenceClosure<NODE>> DISJUNCT renameVariablesICc(final DISJUNCT labelCopy,
			final Map<Term, Term> substitutionMapping, final boolean inplace) {
		if (labelCopy instanceof CongruenceClosure<?>) {
			return (DISJUNCT) renameVariablesCc((CongruenceClosure<NODE>) labelCopy, substitutionMapping, inplace);
		} else {
			return (DISJUNCT) renameVariables((WeqCongruenceClosure<NODE>) labelCopy, substitutionMapping, inplace);
		}
	}

	public <DISJUNCT extends ICongruenceClosure<NODE>> boolean isStrongerThan(final DISJUNCT d1, final DISJUNCT d2) {
		assert d1.getClass().equals(d2.getClass());
		if (d1 instanceof CongruenceClosure<?>) {
			return isStrongerThan((CongruenceClosure<NODE>) d1, (CongruenceClosure<NODE>) d2);
		} else {
			return isStrongerThan((WeqCongruenceClosure<NODE>) d1, (WeqCongruenceClosure<NODE>) d2);
		}
	}

	public boolean isStrongerThan(final WeqCongruenceClosure<NODE> weqcc1, final WeqCongruenceClosure<NODE> weqcc2) {
		final WeqCongruenceClosure<NODE> weqcc1Copy = copyWeqCc(weqcc1, true);
		final WeqCongruenceClosure<NODE> weqcc2Copy = copyWeqCc(weqcc2, true);;

		freezeIfNecessary(weqcc1Copy);
		freezeIfNecessary(weqcc2Copy);

		return weqcc1Copy.isStrongerThan(weqcc2Copy);
	}

	public <DISJUNCT extends ICongruenceClosure<NODE>> DISJUNCT getEmptyIcc(final DISJUNCT lab, final boolean modifiable) {
		if (lab instanceof CongruenceClosure<?>) {
			return (DISJUNCT) getEmptyCc(modifiable);
		} else {
			assert lab instanceof WeqCongruenceClosure<?>;
			return (DISJUNCT) getEmptyWeqCc(modifiable);
		}
	}

	public CongruenceClosure<NODE> getEmptyCc(final boolean modifiable) {
		return mCcManager.getEmptyCc(modifiable);
	}

	public <DISJUNCT extends ICongruenceClosure<NODE>> WeakEquivalenceEdgeLabel<NODE, DISJUNCT> getSingletonEdgeLabel(
			final WeakEquivalenceGraph<NODE, DISJUNCT> weakEquivalenceGraph,
			final DISJUNCT disjunct) {
		return new WeakEquivalenceEdgeLabel<>(weakEquivalenceGraph, Collections.singleton(disjunct));
	}

	public CongruenceClosure<NODE> addNode(final NODE node, final CongruenceClosure<NODE> congruenceClosure,
			final WeqCongruenceClosure<NODE> newEqualityTarget,
			final boolean inplace, final boolean omitSanityChecks) {
		return mCcManager.addElement(congruenceClosure, node, newEqualityTarget, inplace, omitSanityChecks);
	}

//	public Pair<CongruenceClosure<NODE>, HashRelation<NODE, NODE>>
//			addNodeAndGetNewEqualities(final NODE node, final CongruenceClosure<NODE> congruenceClosure,
//					final boolean inplace, final boolean omitSanityChecks) {
//		return mCcManager.addElementAndGetNewEqualities(congruenceClosure, node, inplace, omitSanityChecks);
//	}

	public List<NODE> getAllWeqVarsNodeForFunction(final NODE func) {
		if (!func.getSort().isArraySort()) {
			return Collections.emptyList();
		}
		final MultiDimensionalSort mdSort = new MultiDimensionalSort(func.getSort());
		final List<Sort> indexSorts = mdSort.getIndexSorts();
		final List<NODE> result = new ArrayList<>(mdSort.getDimension());
		for (int i = 0; i < mdSort.getDimension(); i++) {
			result.add(this.getWeqVariableNodeForDimension(i, indexSorts.get(i)));
		}
		return result;
	}

	public Map<Term, Term> getWeqPrimedVarsToWeqVars() {
		return mWeqVarsToWeqPrimedVars.inverse();
	}

	public Map<Term, Term> getWeqVarsToWeqPrimedVars() {
		return mWeqVarsToWeqPrimedVars;
	}

	public Set<NODE> getAllWeqPrimedAndUnprimedNodes() {
		return DataStructureUtils.union(getAllWeqNodes(), getAllWeqPrimedNodes());
	}

	public Set<NODE> getAllWeqPrimedNodes() {
		final Set<NODE> result = new HashSet<>();
		for (final Triple<Sort, Integer, NODE> en : mDimensionToWeqVariableNode.entrySet()) {
			result.add(mNodeAndFunctionFactory.getExistingNode(mWeqVarsToWeqPrimedVars.get(en.getThird().getTerm())));
		}
		return result;
	}

	public NODE getWeqVariableNodeForDimension(final int dimensionNumber, final Sort sort) {
		NODE result = mDimensionToWeqVariableNode.get(sort, dimensionNumber);
		if (result == null) {
			final TermVariable weqVar = mMgdScript.constructFreshTermVariable("weq" + dimensionNumber, sort);
			final TermVariable weqPrimedVar = mMgdScript.constructFreshTermVariable("weqPrime" + dimensionNumber, sort);
			mWeqVarsToWeqPrimedVars.put(weqVar, weqPrimedVar);
			result = getEqNodeAndFunctionFactory().getOrConstructNode(weqVar);
			mDimensionToWeqVariableNode.put(sort, dimensionNumber, result);
		}
		return result;
	}

	public TermVariable getWeqVariableForDimension(final int dimensionNumber, final Sort sort) {
		return (TermVariable) getWeqVariableNodeForDimension(dimensionNumber, sort).getTerm();
	}

	public Set<TermVariable> getAllWeqVariables() {
		final Set<TermVariable> result = new HashSet<>();
		mDimensionToWeqVariableNode.entrySet().forEach(en -> result.add((TermVariable) en.getThird().getTerm()));
		return result;
	}

	public Set<NODE> getAllWeqNodes() {
		final Set<NODE> result = new HashSet<>();
		for (final Triple<Sort, Integer, NODE> en : mDimensionToWeqVariableNode.entrySet()) {
			result.add(en.getThird());
		}
		return result;
	}

	public ILogger getLogger() {
		return mLogger;
	}

	public AbstractNodeAndFunctionFactory<NODE, Term> getEqNodeAndFunctionFactory() {
		return mNodeAndFunctionFactory;
	}

	private boolean checkReportWeakEquivalenceResult(final WeqCongruenceClosure<NODE> origWeqCc, final NODE array1,
			final NODE array2, final NODE storeIndex, final WeqCongruenceClosure<NODE> unfrozen) {
		// TODO Auto-generated method stub
		return true;
	}

	private boolean checkReportEqualityResult(final CongruenceClosure<NODE> origCc, final NODE node1, final NODE node2,
			final CongruenceClosure<NODE> result) {
		return checkReportEqualityResult(
				CongruenceClosureSmtUtils.congruenceClosureToTerm(mMgdScript.getScript(), origCc), node1.getTerm(),
				node2.getTerm(), CongruenceClosureSmtUtils.congruenceClosureToTerm(mMgdScript.getScript(), result));
	}

	private boolean checkReportEqualityResult(final WeqCongruenceClosure<NODE> origCc, final NODE node1,
			final NODE node2, final WeqCongruenceClosure<NODE> result) {
		return checkReportEqualityResult(weqCcToTerm(mMgdScript.getScript(), origCc), node1.getTerm(), node2.getTerm(),
				weqCcToTerm(mMgdScript.getScript(), result));
	}

	private boolean checkReportEqualityResult(final Term original, final Term node1, final Term node2,
			final Term result) {
		// check that "origCc && node1 = node2 <-> result"
		mMgdScript.lock(this);
		final Script script = mMgdScript.getScript();

		final Term originalAndEquality = SmtUtils.and(script, original, mMgdScript.term(this, "=", node1, node2));

		final boolean res = checkImplicationHolds(script, originalAndEquality, result)
				&& checkImplicationHolds(script, result, originalAndEquality);
		mMgdScript.unlock(this);
		return res;
	}

	private boolean checkReportDisequalityResult(final CongruenceClosure<NODE> origCc, final NODE node1,
			final NODE node2, final CongruenceClosure<NODE> result) {
		return checkReportDisequalityResult(
				CongruenceClosureSmtUtils.congruenceClosureToTerm(mMgdScript.getScript(), origCc), node1.getTerm(),
				node2.getTerm(), CongruenceClosureSmtUtils.congruenceClosureToTerm(mMgdScript.getScript(), result));
	}

	private boolean checkReportDisequalityResult(final WeqCongruenceClosure<NODE> origCc, final NODE node1,
			final NODE node2, final WeqCongruenceClosure<NODE> result) {
		return checkReportDisequalityResult(weqCcToTerm(mMgdScript.getScript(), origCc), node1.getTerm(),
				node2.getTerm(), weqCcToTerm(mMgdScript.getScript(), result));
	}

	private boolean checkReportDisequalityResult(final Term original, final Term node1, final Term node2,
			final Term result) {
		// check that "origCc && node1 != node2 <-> result"
		mMgdScript.lock(this);
		final Script script = mMgdScript.getScript();

		final Term originalAndEquality = SmtUtils.and(script, original,
				mMgdScript.term(this, "distinct", node1, node2));

		final boolean res = checkImplicationHolds(script, originalAndEquality, result)
				&& checkImplicationHolds(script, result, originalAndEquality);
		mMgdScript.unlock(this);
		return res;
	}

	private boolean checkProjectAwayResult(final WeqCongruenceClosure<NODE> original, final NODE nodeToProjectAway,
			final WeqCongruenceClosure<NODE> result) {
		return checkProjectAwayResult(weqCcToTerm(mMgdScript.getScript(), original), nodeToProjectAway.getTerm(),
				weqCcToTerm(mMgdScript.getScript(), result));
	}

	private boolean checkProjectAwayResult(final Term original, final Term projectedVar, final Term result) {
		// check that "(exists projectedVar. original) -> result"
		mMgdScript.lock(this);
		final Script script = mMgdScript.getScript();

		final Term originalProjected;
		if (projectedVar instanceof TermVariable) {
			originalProjected = SmtUtils.quantifier(script, QuantifiedFormula.EXISTS,
					Collections.singleton((TermVariable) projectedVar), original);
		} else {
			throw new AssertionError("this actually occurs?.. just omit quantification then?");
		}

		final boolean res = checkImplicationHolds(script, originalProjected, result);
		mMgdScript.unlock(this);
		return res;
	}

	private boolean checkMeetResult(final CongruenceClosure<NODE> cc1, final CongruenceClosure<NODE> cc2,
			final CongruenceClosure<NODE> result) {
		return checkMeetResult(CongruenceClosureSmtUtils.congruenceClosureToTerm(mMgdScript.getScript(), cc1),
				CongruenceClosureSmtUtils.congruenceClosureToTerm(mMgdScript.getScript(), cc2),
				CongruenceClosureSmtUtils.congruenceClosureToTerm(mMgdScript.getScript(), result));
	}

	boolean checkMeetResult(final WeqCongruenceClosure<NODE> weqcc1, final WeqCongruenceClosure<NODE> weqcc2,
			final WeqCongruenceClosure<NODE> result) {
		return checkMeetResult(weqCcToTerm(mMgdScript.getScript(), weqcc1), weqCcToTerm(mMgdScript.getScript(), weqcc2),
				weqCcToTerm(mMgdScript.getScript(), result));
	}

	private boolean checkMeetResult(final Term cc1, final Term cc2, final Term resultTerm) {
		// check that "(cc1 /\ cc2) <-> result" (our meet is precise, right?)
		mMgdScript.lock(this);
		final Script script = mMgdScript.getScript();
		final Term cc1AndCc2Term = SmtUtils.and(script, cc1, cc2);
		final boolean res = checkImplicationHolds(script, cc1AndCc2Term, resultTerm)
				&& checkImplicationHolds(script, resultTerm, cc1AndCc2Term);
		mMgdScript.unlock(this);
		return res;
	}

	private boolean checkJoinResult(final CongruenceClosure<NODE> cc1, final CongruenceClosure<NODE> cc2,
			final CongruenceClosure<NODE> result) {
		return checkJoinResult(CongruenceClosureSmtUtils.congruenceClosureToTerm(mMgdScript.getScript(), cc1),
				CongruenceClosureSmtUtils.congruenceClosureToTerm(mMgdScript.getScript(), cc2),
				CongruenceClosureSmtUtils.congruenceClosureToTerm(mMgdScript.getScript(), result));
	}

	private boolean checkJoinResult(final WeqCongruenceClosure<NODE> weqcc1, final WeqCongruenceClosure<NODE> weqcc2,
			final WeqCongruenceClosure<NODE> result) {
		return checkJoinResult(weqCcToTerm(mMgdScript.getScript(), weqcc1), weqCcToTerm(mMgdScript.getScript(), weqcc2),
				weqCcToTerm(mMgdScript.getScript(), result));
	}

	private boolean checkJoinResult(final Term cc1, final Term cc2, final Term resultTerm) {
		// check that "(cc1 \/ cc2) -> result" holds
		mMgdScript.lock(this);
		mMgdScript.echo(this, new QuotedObject("WeqCcManager.checkJoinResult (begin)"));

		final Script script = mMgdScript.getScript();
		final Term cc1OrCc2Term = SmtUtils.or(script, cc1, cc2);
		final boolean res = checkImplicationHolds(script, cc1OrCc2Term, resultTerm);

		mMgdScript.echo(this, new QuotedObject("WeqCcManager.checkJoinResult (end)"));
		mMgdScript.unlock(this);
		return res;
	}

	/**
	 * like isStrongerThan(..Term..) but used for assertions
	 * @param script
	 * @param ante
	 * @param succ
	 * @return
	 */
	private boolean checkImplicationHolds(final Script script, final Term ante, final Term succ) {
		if (mSkipSolverChecks) {
			return true;
		}
		return isStrongerThan(script, ante, succ);
	}

	/**
	 * like checkImplicationHolds(..Term..) but can be used outside assertions (no breakout-flag)
	 *
	 * @param script
	 * @param ante
	 * @param succ
	 * @return
	 */
	private boolean isStrongerThan(final Script script, final Term ante, final Term succ) {

		assert mMgdScript.isLockOwner(this);

		mMgdScript.push(this, 1);

		/*
		 * declare a constant for each variable and substitute the variables
		 */
		final Set<TermVariable> freeVars = new HashSet<>();
		freeVars.addAll(Arrays.asList(ante.getFreeVars()));
		freeVars.addAll(Arrays.asList(succ.getFreeVars()));

		final Map<Term, Term> subsMap = new HashMap<>();
		for (final TermVariable fv : freeVars) {
			// assuming the constant is already declared..
			mMgdScript.declareFun(this, fv.getName(), new Sort[0], fv.getSort());
			final Term cons = mMgdScript.term(this, fv.getName());
			subsMap.put(fv, cons);
		}

		final Substitution substitution = new Substitution(mMgdScript, subsMap);

		/*
		 * check the implication
		 */
		mMgdScript.assertTerm(this, substitution.transform(ante));

		mMgdScript.assertTerm(this, SmtUtils.not(script, substitution.transform(succ)));

		final LBool satResult = mMgdScript.checkSat(this);

		mMgdScript.pop(this, 1);

//		assert satResult == LBool.UNSAT;
		return satResult == LBool.UNSAT;
	}

	private <DISJUNCT extends ICongruenceClosure<NODE>> boolean checkFilterDisjunctionResult(final Set<DISJUNCT> ccs1,
			final Set<DISJUNCT> ccs2) {
		mMgdScript.lock(this);
		mMgdScript.echo(this, new QuotedObject("WeqCcManager.checkFilterDisjunctionResult (begin)"));
		final Term term1 = disjunctionToTerm(mMgdScript.getScript(), ccs1);
		final Term term2 = disjunctionToTerm(mMgdScript.getScript(), ccs2);
		final boolean res = checkImplicationHolds(mMgdScript.getScript(), term1, term2)
				&& checkImplicationHolds(mMgdScript.getScript(), term2, term1);

		mMgdScript.echo(this, new QuotedObject("WeqCcManager.checkFilterDisjunctionResult (end)"));
		mMgdScript.unlock(this);
		return res;

	}

	private static <NODE extends IEqNodeIdentifier<NODE> , DISJUNCT extends ICongruenceClosure<NODE>>
			Term disjunctionToTerm(final Script script, final Set<DISJUNCT> ccs) {
		if (ccs.isEmpty()) {
			return script.term("false");
		}
		final DISJUNCT sample = ccs.iterator().next();
		final Set<Term> disjunctTerms = new HashSet<>();
		if (sample instanceof CongruenceClosure<?>) {
			for (final DISJUNCT cc : ccs) {
				disjunctTerms.add(CongruenceClosureSmtUtils.congruenceClosureToTerm(script,
						(CongruenceClosure<NODE>) cc));
			}
		} else {
			for (final DISJUNCT weqcc : ccs) {
				disjunctTerms.add(weqCcToTerm(script, (WeqCongruenceClosure<NODE>) weqcc));
			}
		}
		return SmtUtils.or(script, disjunctTerms);
	}

	public static <NODE extends IEqNodeIdentifier<NODE>> Term weqCcToTerm(final Script script,
			final WeqCongruenceClosure<NODE> weqCc) {
		if (weqCc.isInconsistent()) {
			return script.term("false");
		}

		final List<Term> allConjuncts = new ArrayList<>();
		// allConjuncts.addAll(EqConstraint.partialArrangementToCube(script, this));
		allConjuncts.addAll(CongruenceClosureSmtUtils.congruenceClosureToCube(script, weqCc.getCongruenceClosure()));

		final List<Term> weakEqConstraints = weqCc.getWeakEquivalenceGraph()
				.getWeakEquivalenceConstraintsAsTerms(script);
		allConjuncts.addAll(weakEqConstraints);

		final Term result = SmtUtils.and(script, allConjuncts.toArray(new Term[allConjuncts.size()]));
		return result;
	}

	public WeqCongruenceClosure<NODE> getWeqCongruenceClosure(final CongruenceClosure<NODE> cc,
			final WeakEquivalenceGraph<NODE, CongruenceClosure<NODE>> weqGraph, final boolean modifiable) {
		final CongruenceClosure<NODE> ccUnfrozen = mCcManager.unfreezeIfNecessary(cc);
		addAllElementsCc(ccUnfrozen, weqGraph.getAppearingNonWeqVarNodes(), null, true);
		final WeqCongruenceClosure<NODE> result = new WeqCongruenceClosure<>(ccUnfrozen, weqGraph, this);

		if (!modifiable) {
			result.freeze();
		}
		return result;
	}

	public <DISJUNCT extends ICongruenceClosure<NODE>> DISJUNCT getSingleEqualityCc(final NODE node1, final NODE node2,
			final boolean modifiable, final DISJUNCT dummyDisjunct) {
		if (dummyDisjunct instanceof CongruenceClosure<?>)  {
			return (DISJUNCT) mCcManager.getSingleEqualityCc(node1, node2, modifiable);
		} else {
			throw new AssertionError();
		}
	}

	public <DISJUNCT extends ICongruenceClosure<NODE>> DISJUNCT getSingleDisequalityCc(final NODE node1,
			final NODE node2, final boolean modifiable, final DISJUNCT dummyDisjunct) {
		if (dummyDisjunct instanceof CongruenceClosure<?>)  {
			return (DISJUNCT) mCcManager.getSingleDisequalityCc(node1, node2, modifiable);
		} else {
			throw new AssertionError();
		}
	}

	public CongruenceClosure<NODE> getSingleEqualityCc(final NODE node1, final NODE node2, final boolean modifiable) {
		return mCcManager.getSingleEqualityCc(node1, node2, modifiable);
	}

	public CongruenceClosure<NODE> getSingleDisequalityCc(final NODE node1, final NODE node2, final boolean modifiable) {
		return mCcManager.getSingleDisequalityCc(node1, node2, modifiable);
	}

	/**
	 * (keeps isFrozen()-status)
	 *
	 * @param cc
	 * @return
	 */
	public CongruenceClosure<NODE> copyCcNoRemInfo(final CongruenceClosure<NODE> cc) {
		final CongruenceClosure<NODE> result = mCcManager.copyNoRemInfo(cc);
		assert result.isFrozen() == cc.isFrozen();
//		if (WeqSettings.FREEZE_ALL_IN_MANAGER) {
//			if (!result.isFrozen()) {
//				result.freeze();
//			}
//		}
		return result;
	}

	public CongruenceClosure<NODE> copyCcNoRemInfoUnfrozen(final CongruenceClosure<NODE> cc) {
		return mCcManager.copyNoRemInfoUnfrozen(cc);
	}

	public <DISJUNCT extends ICongruenceClosure<NODE>> DISJUNCT projectToElements(final DISJUNCT cc,
			final Set<NODE> nodesToKeep, final IRemovalInfo<NODE> remInfo, final boolean modifiable) {
		assert !cc.isInconsistent() : "catch this outside";
		if (cc.getClass().equals(CongruenceClosure.class)) {
			return (DISJUNCT) projectToElements((CongruenceClosure<NODE>) cc, nodesToKeep, remInfo, modifiable);
		} else {
			throw new AssertionError();
		}
	}

	public CongruenceClosure<NODE> projectToElements(final CongruenceClosure<NODE> cc, final Set<NODE> nodesToKeep,
			final IRemovalInfo<NODE> remInfo, final boolean modifiable) {
		assert !cc.isInconsistent() : "catch this outside";
		CongruenceClosure<NODE> result = mCcManager.projectToElements(cc, nodesToKeep, remInfo);
		assert result.isFrozen() : "projectToElements always freezes, right?.. (because it cannot work inplace)";
		if (modifiable) {
			result = unfreeze(result);
		}
		return result;
	}

	public WeqCongruenceClosure<NODE> addAllElements(final WeqCongruenceClosure<NODE> weqcc,
			final Set<NODE> nodesToAdd, final IRemovalInfo<NODE> remInfo, final boolean inplace) {
		if (inplace) {
			for (final NODE e : nodesToAdd) {
				if (weqcc.isInconsistent()) {
					return weqcc;
				}
				addNode(e, weqcc, true, false);
			}
			return weqcc;
		} else {
			WeqCongruenceClosure<NODE> result = unfreeze(weqcc);
			for (final NODE e : nodesToAdd) {
				if (weqcc.isInconsistent()) {
					return weqcc;
				}
				result = addNode(e, weqcc, false, false);
			}
			assert result.isFrozen();
			return result;
		}
	}

	public CongruenceClosure<NODE> addAllElementsCc(final CongruenceClosure<NODE> cc,
			final Set<NODE> elemsToAdd, final IRemovalInfo<NODE> remInfo, final boolean inplace) {
		return mCcManager.addAllElements(cc, elemsToAdd, remInfo, inplace);
	}

	/**
	 * Given a (multidimensional) index, compute the corresponding annotation for a
	 * weak equivalence edge.
	 *
	 * Example: for (i1, .., in), this should return (q1 = i1, ..., qn = in) as a
	 * list of CongruenceClosures. (where qi is the variable returned by
	 * getWeqVariableForDimension(i))
	 *
	 * Always returns a frozen constraint (as of now..).
	 *
	 * @param nodes
	 * @return
	 */
	CongruenceClosure<NODE> computeWeqConstraintForIndex(final List<NODE> nodes, final boolean modifiable) {
		final CongruenceClosure<NODE> result = getEmptyCc(true);
		for (int i = 0; i < nodes.size(); i++) {
			final NODE ithNode = nodes.get(i);
			final NODE weqVarNode = getWeqVariableNodeForDimension(i, ithNode.getTerm().getSort());
			reportEquality(result, weqVarNode, ithNode, true);
		}
		if (!modifiable) {
			result.freeze();
		}
		return result;
	}

	/**
	 * Obtain edge label of the form "q0 = i" where i is the parameter storeIndex.
	 *
	 * @param weakEquivalenceGraph
	 * @param storeIndex
	 * @return
	 */
	public WeakEquivalenceEdgeLabel<NODE, CongruenceClosure<NODE>> getEdgeLabelForIndex(
			final WeakEquivalenceGraph<NODE, CongruenceClosure<NODE>> weakEquivalenceGraph,
			final NODE storeIndex) {
		return getSingletonEdgeLabel(weakEquivalenceGraph,
				computeWeqConstraintForIndex(Collections.singletonList(storeIndex), !weakEquivalenceGraph.isFrozen()));
	}

	public <DISJUNCT extends ICongruenceClosure<NODE>> WeakEquivalenceEdgeLabel<NODE, DISJUNCT>
		meetEdgeLabels( final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> l1,
			final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> l2, final boolean inplace) {

//		WeakEquivalenceEdgeLabel<NODE, DISJUNCT> originalL1 = null;
//		if (areAssertsEnabled() && inplace) {
//			originalL1 = copy(l1, true, true);
//		} else if (areAssertsEnabled() && !inplace) {
//			originalL1 = l1;
//		}

		final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> result = l1.meet(l2, inplace);

		assert !inplace || result == l1 : "if inplace is set, we must return the original object";

//		assert checkMeetWeqLabels(originalL1, l2, result);
		assert inplace || isStrongerThanPrecise(result, l1);
		assert inplace || isStrongerThanPrecise(result, l2);

		return result;
	}

	/**
	 * Checks if "(l1 /\ l2) <-> result)" holds.
	 * (Simply takes the ground formulas of the weq labels, which should be what we want..)
	 *
	 * @param l1
	 * @param l2
	 * @param result
	 * @return
	 */
	<DISJUNCT extends ICongruenceClosure<NODE>> boolean checkMeetWeqLabels(
					final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> l1,
					final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> l2,
					final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> result) {

		final Script script = mMgdScript.getScript();

		mMgdScript.lock(this);

		final List<Term> l1Dnf = l1.toDnf(script);
		final Term l1Term = SmtUtils.or(script, l1Dnf);

		final List<Term> l2Dnf = l2.toDnf(script);
		final Term l2Term = SmtUtils.or(script, l2Dnf);

		final List<Term> resultDnf = result.toDnf(script);
		final Term resultTerm = SmtUtils.or(script, resultDnf);

		final Term l1AndL2 = SmtUtils.and(script, l1Term, l2Term);

		final boolean oneImpliesTwo = checkImplicationHolds(script, l1AndL2, resultTerm);
		assert oneImpliesTwo;

		final boolean twoImpliesOne = checkImplicationHolds(script, resultTerm, l1AndL2);
		assert twoImpliesOne;

		mMgdScript.unlock(this);

		return oneImpliesTwo && twoImpliesOne;
	}

	public void freezeIfNecessary(final CongruenceClosure<NODE> cc) {
		mCcManager.freezeIfNecessary(cc);
	}

	/**
	 * rule:  Disjunction A isStrongerThan disjunction B
	 *     iff
	 *   forall ai exists bi. ai subseteq bi
	 * @param ccPoCache
	 * @param value
	 * @return
	 */
	public <DISJUNCT extends ICongruenceClosure<NODE>> boolean isStrongerThan(
			final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> label1,
			final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> label2) {
		final boolean result;
		if (WeqSettings.PRECISE_WEQ_LABEL_COMPARISON) {
			result = isStrongerThanPrecise(label1, label2);
		} else {
			result = isStrongerThan(label1, label2, this::isStrongerThan);
		}
		assert checkIsStrongerThanResult(label1, label2, result);
		return result;
	}

	<DISJUNCT extends ICongruenceClosure<NODE>> boolean isStrongerThanPrecise(
			final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> label1,
			final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> label2) {
		final Script script = mMgdScript.getScript();

		mMgdScript.lock(this);

		final Term label1Term = SmtUtils.or(script, label1.toDnf(script));
		final Term label2Term = SmtUtils.or(script, label2.toDnf(script));

		final boolean implicationHolds = isStrongerThan(script, label1Term, label2Term);

		mMgdScript.unlock(this);
		return implicationHolds;
	}

	private <DISJUNCT extends ICongruenceClosure<NODE>> boolean checkIsStrongerThanResult(
			final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> label1,
			final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> label2, final boolean impCheckResult) {

		final Script script = mMgdScript.getScript();

		mMgdScript.lock(this);

		final Term label1Term = SmtUtils.or(script, label1.toDnf(script));
		final Term label2Term = SmtUtils.or(script, label2.toDnf(script));

		final boolean implicationHolds = checkImplicationHolds(script, label1Term, label2Term);

		final boolean result;
		if (label2.getDisjuncts().size() <= 1) {
			// special case where our implication check is conceptually precise
			result = implicationHolds == impCheckResult;
			assert result;
		} else {
			/*
			 * in general our implication check approximates: If its says the implication holds, it holds, but it may
			 *  not detect a valid implication  in all cases.
			 */
			result = !impCheckResult || implicationHolds;
			assert result;
		}

		mMgdScript.unlock(this);
		return result;
	}

	public <DISJUNCT extends ICongruenceClosure<NODE>> boolean isStrongerThan(
			final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> label1,
			final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> label2,
			final BiPredicate<DISJUNCT, DISJUNCT> lowerOrEqual) {
		for (final DISJUNCT label1disjunct : label1.getDisjuncts()) {
			boolean existsWeaker = false;
			for (final DISJUNCT label2disjunct : label2.getDisjuncts()) {
				if (lowerOrEqual.test(label1disjunct, label2disjunct)) {
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

	public boolean isStrongerThan(final CongruenceClosure<NODE> paThis, final CongruenceClosure<NODE> paOther) {
		return mCcManager.isStrongerThan(paThis, paOther);
	}

	public boolean isEquivalentCc(final WeakEquivalenceEdgeLabel<NODE, CongruenceClosure<NODE>> label1,
			final WeakEquivalenceEdgeLabel<NODE, CongruenceClosure<NODE>> label2) {
		return isStrongerThan(label1, label2) && isStrongerThan(label2, label1);
	}

	public <DISJUNCT extends ICongruenceClosure<NODE>> boolean isEquivalentICc(
			final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> label1,
			final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> label2) {
		return isStrongerThan(label1, label2) && isStrongerThan(label2, label1);
	}

	public <DISJUNCT extends ICongruenceClosure<NODE>> boolean isStrongerThan(
			final WeakEquivalenceGraph<NODE, DISJUNCT> weakEquivalenceGraph,
			final WeakEquivalenceGraph<NODE, DISJUNCT> weakEquivalenceGraph2) {
		// freezing ensures closure
		freezeIfNecessary(weakEquivalenceGraph);
		freezeIfNecessary(weakEquivalenceGraph2);

		return weakEquivalenceGraph.isStrongerThan(weakEquivalenceGraph2);
	}

	private <DISJUNCT extends ICongruenceClosure<NODE>> void freezeIfNecessary(
			final WeakEquivalenceGraph<NODE, DISJUNCT> weakEquivalenceGraph) {
		if (!weakEquivalenceGraph.isFrozen()) {
			weakEquivalenceGraph.freeze();
		}
	}

	/**
	 *
	 * note: the resulting Weq graph has null as its WeqCc, it will be set to the correct WeqCc by copying it, later.
	 *
	 * @param weakEquivalenceGraph
	 * @param weakEquivalenceGraph2
	 * @param modifiable
	 * @return
	 */
	public <DISJUNCT extends ICongruenceClosure<NODE>> WeakEquivalenceGraph<NODE, DISJUNCT> join(
			final WeakEquivalenceGraph<NODE, DISJUNCT> weakEquivalenceGraph,
			final WeakEquivalenceGraph<NODE, DISJUNCT> weakEquivalenceGraph2,
			final boolean modifiable) {
		freezeIfNecessary(weakEquivalenceGraph);
		freezeIfNecessary(weakEquivalenceGraph2);

		final WeakEquivalenceGraph<NODE, DISJUNCT> result = weakEquivalenceGraph.join(weakEquivalenceGraph2);

		if (!modifiable) {
			result.freeze();
		}

		return result;
	}

	public <DISJUNCT extends ICongruenceClosure<NODE>> DISJUNCT copyICc(final DISJUNCT icc,
			final boolean modifiable) {
		if (icc.getClass().equals(CongruenceClosure.class)) {
			return (DISJUNCT) copyCc((CongruenceClosure<NODE>) icc, modifiable);
		} else {
			return (DISJUNCT) copyWeqCc((WeqCongruenceClosure<NODE>) icc, modifiable);
		}
	}

	public WeqCongruenceClosure<NODE> copyWeqCc(final WeqCongruenceClosure<NODE> original, final boolean modifiable) {
//		final WeqCongruenceClosure<NODE> result = new WeqCongruenceClosure<>(original, true);
		final WeqCongruenceClosure<NODE> result = new WeqCongruenceClosure<>(original);
		if (!modifiable) {
			result.freeze();
		}
		return result;
	}

	/**
	 * If icc is a CongruenceClosure return a copy of it. If icc is a WeqCongruenceClosure return a copy of its
	 * CongruenceClosure.
	 *
	 * @param icc
	 * @param modifiable
	 * @return
	 */
	public CongruenceClosure<NODE> copyCcOnly(final ICongruenceClosure<NODE> icc, final boolean modifiable) {
		if (icc.getClass().equals(CongruenceClosure.class)) {
			return copyCc((CongruenceClosure<NODE>) icc, modifiable);
		} else {
			return copyCc(((WeqCongruenceClosure<NODE>) icc).getCongruenceClosure(), modifiable);
		}
	}

	public CongruenceClosure<NODE> copyCc(final CongruenceClosure<NODE> icc, final boolean modifiable) {
		return mCcManager.getCopy(icc, modifiable);
	}

	public <DISJUNCT extends ICongruenceClosure<NODE>> WeakEquivalenceEdgeLabel<NODE, DISJUNCT>
			copy(final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> original, final boolean omitSanityCheck,
					final boolean modifiable) {
		return copy(original, original.getWeqGraph(), omitSanityCheck, modifiable);
	}

	public <DISJUNCT extends ICongruenceClosure<NODE>> WeakEquivalenceEdgeLabel<NODE, DISJUNCT>
			copy(final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> original, final boolean modifiable) {
//		return new WeakEquivalenceEdgeLabel<>(original.getWeqGraph(), original);
		return copy(original, original.getWeqGraph(), modifiable);
	}

	public <DISJUNCT extends ICongruenceClosure<NODE>> void freezeIfNecessary(final DISJUNCT disjunct) {
		if (disjunct instanceof CongruenceClosure<?>) {
			freezeIfNecessary((CongruenceClosure<NODE>) disjunct);
		} else {
			throw new AssertionError("implement");
		}
	}

	public <DISJUNCT extends ICongruenceClosure<NODE>> DISJUNCT unfreezeIfNecessary(final DISJUNCT disjunct) {
		if (disjunct instanceof CongruenceClosure<?>) {
			return (DISJUNCT) mCcManager.unfreezeIfNecessary((CongruenceClosure<NODE>) disjunct);
		} else {
			throw new AssertionError("implement");
		}
	}

	public <DISJUNCT extends ICongruenceClosure<NODE>> WeakEquivalenceEdgeLabel<NODE, DISJUNCT> copy(
			final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> value,
			final WeakEquivalenceGraph<NODE, DISJUNCT> weakEquivalenceGraph,
			final boolean modifiable) {
		return copy(value, weakEquivalenceGraph, false, modifiable);
	}


	public <DISJUNCT extends ICongruenceClosure<NODE>> WeakEquivalenceEdgeLabel<NODE, DISJUNCT> copy(
			final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> value,
			final WeakEquivalenceGraph<NODE, DISJUNCT> weakEquivalenceGraph,
			final boolean omitSanityCheck,
			final boolean modifiable) {
		final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> result = new WeakEquivalenceEdgeLabel<>(weakEquivalenceGraph,
				value, omitSanityCheck);
		if (!modifiable) {
			result.freeze();
		}
		return result;
	}

//	public WeakEquivalenceGraph<NODE, CongruenceClosure<NODE>> unfreezeDeep(
//			WeakEquivalenceGraph<NODE, CongruenceClosure<NODE>> weakEquivalenceGraphThin,
//			WeqCongruenceClosure<NODE> weqCongruenceClosure) {
//		return new WeakEquivalenceGraph<>(pArr, weakEquivalenceGraph);
//	}

	public <DISJUNCT extends ICongruenceClosure<NODE>> WeakEquivalenceGraph<NODE, DISJUNCT> unfreeze(
			final WeakEquivalenceGraph<NODE, DISJUNCT> weqGraph) {
		return new WeakEquivalenceGraph<>(weqGraph.getBaseWeqCc(), weqGraph);
	}

	public <DISJUNCT extends ICongruenceClosure<NODE>> WeakEquivalenceEdgeLabel<NODE, DISJUNCT>
			unfreeze(final WeakEquivalenceEdgeLabel<NODE, DISJUNCT> value) {
		return copy(value, true);
	}


	/**
	 * Solution from StackOverflow (apparently quoting http://docs.oracle.com/javase/1.4.2/docs/guide/lang/assert.html)
	 * to detect if asserts are enabled.
	 * @return true iff Java is running with assertions enabled
	 */
	public static boolean areAssertsEnabled() {
		boolean assertsEnabled = false;
		assert assertsEnabled = true; // Intentional side effect!!!
		return assertsEnabled;
	}

	public boolean checkEquivalence(final WeqCongruenceClosure<NODE> weqcc1,
			final WeqCongruenceClosure<NODE> weqcc2) {
		if (mSkipSolverChecks) {
			return true;
		}

		mMgdScript.lock(this);

		final Term term1 = weqCcToTerm(mMgdScript.getScript(), weqcc1);
		final Term term2 = weqCcToTerm(mMgdScript.getScript(), weqcc2);

		final boolean oneImpliesTwo = checkImplicationHolds(mMgdScript.getScript(), term1, term2);
		assert oneImpliesTwo;

		final boolean twoImpliesOne = checkImplicationHolds(mMgdScript.getScript(), term2, term1);
		assert twoImpliesOne;

		mMgdScript.unlock(this);

		return oneImpliesTwo && twoImpliesOne;
	}
}
