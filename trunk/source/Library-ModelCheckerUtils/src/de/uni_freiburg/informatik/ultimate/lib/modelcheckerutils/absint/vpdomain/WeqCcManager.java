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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.BiPredicate;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.MultiDimensionalSort;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BidirectionalMap;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.CcManager;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.CcSettings;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.CongruenceClosure;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.IRemovalInfo;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.SetConstraint;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.IPartialComparator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.PartialOrderCache;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;
import de.uni_freiburg.informatik.ultimate.util.statistics.BenchmarkWithCounters;

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

	private final WeqSettings mSettings;

	private final boolean mBenchmarkMode = !true;
	private BenchmarkWithCounters mBenchmark;

	final boolean mDebug;
	final boolean mSkipSolverChecks = true;

	private final Set<NODE> mNonTheoryLiteralNodes;

	/**
	 *
	 * @param logger
	 * @param weqCcComparator
	 * @param ccComparator
	 * @param mgdScript
	 * @param nodeAndFunctionFactory
	 * @param settings
	 * @param debugMode
	 * @param nonTheoryLiteralNodes
	 * 			must be added to each state upon creation
	 */
	public WeqCcManager(final ILogger logger, final IPartialComparator<WeqCongruenceClosure<NODE>> weqCcComparator,
			final IPartialComparator<CongruenceClosure<NODE>> ccComparator, final ManagedScript mgdScript,
			final AbstractNodeAndFunctionFactory<NODE, Term> nodeAndFunctionFactory, final WeqSettings settings,
			final boolean debugMode, final Set<NODE> nonTheoryLiteralNodes) {
		mCcManager = new CcManager<>(logger, ccComparator);
		mMgdScript = mgdScript;
		mLogger = logger;
		mDebug = debugMode;

		mSettings = settings;

		mWeqCcComparator = weqCcComparator;

		mDimensionToWeqVariableNode = new NestedMap2<>();
		mWeqVarsToWeqPrimedVars = new BidirectionalMap<>();

		mNodeAndFunctionFactory = nodeAndFunctionFactory;
		mNonTheoryLiteralNodes = nonTheoryLiteralNodes;

		if (mBenchmarkMode) {
			mBenchmark = new BenchmarkWithCounters();
			mBenchmark.registerCountersAndWatches(WeqCcBmNames.getNames());
		} else {
			mBenchmark = null;
		}


		mTautologicalWeqCc = new WeqCongruenceClosure<>(this);
		nonTheoryLiteralNodes.forEach(mTautologicalWeqCc::addElementRec);
		mTautologicalWeqCc.freezeAndClose();

		mInconsistentWeqCc = new WeqCongruenceClosure<>(true);

	}

	public WeqCongruenceClosure<NODE> getEmptyWeqCc(final boolean modifiable) {
		if (modifiable) {
			final WeqCongruenceClosure<NODE> result = new WeqCongruenceClosure<>(this);
			mNonTheoryLiteralNodes.forEach(n -> result.addElement(n, false));
			return result;
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
			unfrozen.freezeAndClose();
			result = unfrozen;
		}

		assert omitSanityChecks || origWeqCc.sanityCheck();

		return result;
	}

	public CongruenceClosure<NODE> addNode(final NODE node, final CongruenceClosure<NODE> congruenceClosure,
			final WeqCongruenceClosure<NODE> newEqualityTarget,
			final boolean inplace, final boolean omitSanityChecks) {
		return mCcManager.addElement(congruenceClosure, node, newEqualityTarget, inplace, omitSanityChecks);
	}

	WeqCongruenceClosure<NODE> unfreeze(final WeqCongruenceClosure<NODE> origWeqCc) {
		bmStart(WeqCcBmNames.UNFREEZE);
		assert origWeqCc.isFrozen();
		final WeqCongruenceClosure<NODE> result = copyWeqCc(origWeqCc, true);
		assert !result.isFrozen();
		assert result.sanityCheck();
		bmEnd(WeqCcBmNames.UNFREEZE);
		return result;
	}


	void bmStart(final WeqCcBmNames watch) {
		if (!mBenchmarkMode) {
			return;
		}
		mBenchmark.incrementCounter(watch.name());
		mBenchmark.unpauseWatch(watch.name());
	}

	void bmEnd(final WeqCcBmNames watch) {
		if (!mBenchmarkMode) {
			return;
		}
		mBenchmark.pauseWatch(watch.name());
	}

	public  WeakEquivalenceEdgeLabel<NODE> filterRedundantICcs(
			final WeakEquivalenceEdgeLabel<NODE> label) {
		final WeakEquivalenceEdgeLabel<NODE> result =
				new WeakEquivalenceEdgeLabel<>(label.getWeqGraph(), filterRedundantCcs(label.getDisjuncts()));
//		assert !result.isTautological() || result.getDisjuncts().size() == 1;
		return result;
	}

	public WeakEquivalenceEdgeLabel<NODE> filterRedundantCcs(
			final WeakEquivalenceEdgeLabel<NODE> label) {
		final Set<CongruenceClosure<NODE>> filtered = mCcManager.filterRedundantCcs(label.getDisjuncts());
		return new WeakEquivalenceEdgeLabel<>(label.getWeqGraph(), filtered);
	}

	private Set<WeqCongruenceClosure<NODE>> filterRedundantWeqCcs(final Set<WeqCongruenceClosure<NODE>> ccs) {
		bmStart(WeqCcBmNames.FILTERREDUNDANT);
		final PartialOrderCache<WeqCongruenceClosure<NODE>> poc = new PartialOrderCache<>(mWeqCcComparator);
		final Set<WeqCongruenceClosure<NODE>> result = poc.getMaximalRepresentatives(ccs);
		bmEnd(WeqCcBmNames.FILTERREDUNDANT);
		return result;
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

	public WeqCongruenceClosure<NODE> reportEquality(final WeqCongruenceClosure<NODE> origWeqCc, final NODE node1,
			final NODE node2, final boolean inplace) {
		bmStart(WeqCcBmNames.REPORTEQUALITY);
		if (inplace) {
			origWeqCc.reportEquality(node1, node2, false);
			bmEnd(WeqCcBmNames.REPORTEQUALITY);
			return origWeqCc;
		} else {
			final WeqCongruenceClosure<NODE> unfrozen = unfreeze(origWeqCc);
			unfrozen.reportEquality(node1, node2, false);
			unfrozen.freezeAndClose();
			assert checkReportEqualityResult(origWeqCc, node1, node2, unfrozen,
					getNonTheoryLiteralDisequalitiesIfNecessary());
			bmEnd(WeqCcBmNames.REPORTEQUALITY);
			return unfrozen;
		}
	}

	private CongruenceClosure<NODE> reportEquality(final CongruenceClosure<NODE> origCc, final NODE node1,
			final NODE node2, final boolean inplace) {
		final CongruenceClosure<NODE> result = mCcManager.reportEquality(node1, node2, origCc, inplace);
		assert checkReportEqualityResult(origCc, node1, node2, result,
					getNonTheoryLiteralDisequalitiesIfNecessary());
		return result;
	}

	public WeqCongruenceClosure<NODE> reportDisequality(final WeqCongruenceClosure<NODE> origWeqCc, final NODE node1,
			final NODE node2, final boolean inplace) {
		bmStart(WeqCcBmNames.REPORTDISEQUALITY);
		if (inplace) {
			origWeqCc.reportDisequality(node1, node2);
			bmEnd(WeqCcBmNames.REPORTDISEQUALITY);
			return origWeqCc;
		} else {
			final WeqCongruenceClosure<NODE> unfrozen = unfreeze(origWeqCc);
			unfrozen.reportDisequality(node1, node2);
			unfrozen.freezeAndClose();
			assert checkReportDisequalityResult(origWeqCc, node1, node2, unfrozen,
					getNonTheoryLiteralDisequalitiesIfNecessary());
			bmEnd(WeqCcBmNames.REPORTDISEQUALITY);
			return unfrozen;
		}
	}

	public WeqCongruenceClosure<NODE> reportWeakEquivalence(final WeqCongruenceClosure<NODE> origWeqCc,
			final NODE array1, final NODE array2, final NODE storeIndex, final boolean inplace) {
//		updateTrackingStatusOnReporWeq(array1, array2);

		if (mSettings.isDeactivateWeakEquivalences() || array1.dependsOnUntrackedArray() || array2.dependsOnUntrackedArray()) {
			assert origWeqCc.getWeakEquivalenceGraph().getNumberOfEdgesStatistic() == 0;
			return origWeqCc;
		}
		bmStart(WeqCcBmNames.REPORTWEQ);
		if (inplace) {
			origWeqCc.reportWeakEquivalence(array1, array2, storeIndex, false);
			bmEnd(WeqCcBmNames.REPORTWEQ);
			return origWeqCc;
		} else {
			final WeqCongruenceClosure<NODE> unfrozen = unfreeze(origWeqCc);
			unfrozen.reportWeakEquivalence(array1, array2, storeIndex, false);
			unfrozen.freezeAndClose();
			assert checkReportWeakEquivalenceResult(origWeqCc, array1, array2, storeIndex, unfrozen);
			bmEnd(WeqCcBmNames.REPORTWEQ);
			return unfrozen;
		}
	}

	public WeqCongruenceClosure<NODE> reportContainsConstraint(final NODE elem, final Set<NODE> literalSet,
			final WeqCongruenceClosure<NODE> origWeqCc,
			final boolean inplace) {
		bmStart(WeqCcBmNames.REPORTCONTAINS);
		if (inplace) {
			origWeqCc.reportContainsConstraint(elem, literalSet);
			bmEnd(WeqCcBmNames.REPORTCONTAINS);
			return origWeqCc;
		} else {
			final WeqCongruenceClosure<NODE> unfrozen = unfreeze(origWeqCc);
			unfrozen.reportContainsConstraint(elem, literalSet);
			unfrozen.freezeAndClose();
//			assert checkReportDisequalityResult(origWeqCc, node1, node2, unfrozen,
//					getNonTheoryLiteralDisequalitiesIfNecessary());
			bmEnd(WeqCcBmNames.REPORTCONTAINS);
			return unfrozen;
		}
	}

	public WeqCongruenceClosure<NODE> reportContainsConstraint(final NODE elem,
			final Collection<SetConstraint<NODE>> containsConstraint,
			final WeqCongruenceClosure<NODE> origWeqCc,
			final boolean inplace) {

//		// we are reporting this SetCc into a possibly new constraint --> remove surrounding constraint
//		final SetConstraintConjunction<NODE> containsConstraint =
//				new SetConstraintConjunction<>(null, containsConstraintRaw);

		bmStart(WeqCcBmNames.REPORTCONTAINS);
		if (inplace) {
			origWeqCc.reportContainsConstraint(elem, containsConstraint);
			bmEnd(WeqCcBmNames.REPORTCONTAINS);
			return origWeqCc;
		} else {
			final WeqCongruenceClosure<NODE> unfrozen = unfreeze(origWeqCc);
			unfrozen.reportContainsConstraint(elem, containsConstraint);
			unfrozen.freezeAndClose();
//			assert checkReportDisequalityResult(origWeqCc, node1, node2, unfrozen,
//					getNonTheoryLiteralDisequalitiesIfNecessary());
			bmEnd(WeqCcBmNames.REPORTCONTAINS);
			return unfrozen;
		}
	}

	public WeqCongruenceClosure<NODE> projectAway(final WeqCongruenceClosure<NODE> origWeqCc, final NODE node) {
		bmStart(WeqCcBmNames.PROJECTAWAY);
		// TODO: unsure about this freezing -- is there a more efficient solution?
//		origWeqCc.freezeIfNecessary(true);
//		origWeqCc.extAndTriangleClosure(false);
		final WeqCongruenceClosure<NODE> closed = closeIfNecessary(origWeqCc);

		final WeqCongruenceClosure<NODE> unfrozen = unfreezeIfNecessary(closed);

		assert unfrozen.isClosed();

		RemoveWeqCcElement.removeSimpleElement(unfrozen, node);
		unfrozen.freezeAndClose();
		assert checkProjectAwayResult(origWeqCc, node, unfrozen,
					getNonTheoryLiteralDisequalitiesIfNecessary());
		bmEnd(WeqCcBmNames.PROJECTAWAY);
		return unfrozen;
	}

	public WeqCongruenceClosure<NODE> closeIfNecessary(final WeqCongruenceClosure<NODE> origWeqCc) {
		if (origWeqCc.isClosed()) {
			return origWeqCc;
		}
		if (origWeqCc.isFrozen()) {
			final WeqCongruenceClosure<NODE> unfrozen = unfreeze(origWeqCc);
			unfrozen.extAndTriangleClosure(false);
			return unfrozen;
		} else {
			origWeqCc.extAndTriangleClosure(false);
			return origWeqCc;
		}
	}

	/**
	 * Note that this is asymmetrical, in particular in the inplace case, the first argument is updated with the
	 * constraints in the second.
	 *
	 * Also note this triggers no closure operation.
	 *
	 * @param weqcc1
	 * @param weqcc2
	 * @param inplace
	 * @return
	 */
	public WeqCongruenceClosure<NODE> meet(final WeqCongruenceClosure<NODE> weqcc1,
			final WeqCongruenceClosure<NODE> weqcc2, final boolean inplace) {
		bmStart(WeqCcBmNames.MEET);
		if (inplace) {
			WeqCongruenceClosure<NODE> weqcc1_old = null;
			if (mDebug) {
				weqcc1_old = copyWeqCc(weqcc1, false);
			}
			weqcc1.meet(weqcc2);
			if (mDebug) {
				assert checkMeetResult(weqcc1_old, weqcc2, weqcc1,
						getNonTheoryLiteralDisequalitiesIfNecessary());
			}
			bmEnd(WeqCcBmNames.MEET);
			return weqcc1;
		} else {
			final WeqCongruenceClosure<NODE> unfrozen = unfreeze(weqcc1);

			final WeqCongruenceClosure<NODE> meetResult = unfrozen.meet(weqcc2);

			WeqCongruenceClosure<NODE> result;
			if (mSettings.closeAllEqConstraints() || mSettings.closeAfterInplaceMeet()) {
				result = closeIfNecessary(meetResult);
			} else {
				result = meetResult;
			}
			result.freezeIfNecessary();

			assert checkMeetResult(weqcc1, weqcc2, result, getNonTheoryLiteralDisequalitiesIfNecessary());
			bmEnd(WeqCcBmNames.MEET);
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
			assert checkMeetResult(cc1_old, cc2, result, getNonTheoryLiteralDisequalitiesIfNecessary());
		}

		return result;
	}

	public CongruenceClosure<NODE> join(final CongruenceClosure<NODE> cc1, final CongruenceClosure<NODE> cc2,
			final boolean modifiable) {
		// (just passing it through to CcManager)
		final CongruenceClosure<NODE> result = mCcManager.join(cc1, cc2, modifiable);
		assert checkJoinResult(cc1, cc2, result, getNonTheoryLiteralDisequalitiesIfNecessary());
		return result;
	}

	public WeqCongruenceClosure<NODE> join(final WeqCongruenceClosure<NODE> weqcc1Raw,
			final WeqCongruenceClosure<NODE> weqcc2Raw, final boolean modifiable) {
		bmStart(WeqCcBmNames.JOIN);

		final WeqCongruenceClosure<NODE> weqcc1 = closeIfNecessary(weqcc1Raw);
		weqcc1.freezeIfNecessary();

		final WeqCongruenceClosure<NODE> weqcc2 = closeIfNecessary(weqcc2Raw);
		weqcc2.freezeIfNecessary();

		if (weqcc1.isInconsistent(false)) {
			bmEnd(WeqCcBmNames.JOIN);
			return weqcc2;
		}
		if (weqcc2.isInconsistent(false)) {
			bmEnd(WeqCcBmNames.JOIN);
			return weqcc1;
		}
		if (weqcc1.isTautological() || weqcc2.isTautological()) {
			bmEnd(WeqCcBmNames.JOIN);
			return getEmptyWeqCc(modifiable);
		}

		final WeqCongruenceClosure<NODE> result = weqcc1.join(weqcc2);
		assert result != weqcc1 && result != weqcc2 : "join should construct a new object";
		if (!modifiable) {
			result.freezeAndClose();
		}
		assert checkJoinResult(weqcc1, weqcc2, result, getNonTheoryLiteralDisequalitiesIfNecessary());
		bmEnd(WeqCcBmNames.JOIN);
		return result;
	}

	public CongruenceClosure<NODE> renameVariablesCc(final CongruenceClosure<NODE> weqCc,
			final Map<Term, Term> substitutionMapping, final boolean inplace) {
		return mCcManager.transformElements(weqCc, e -> e.renameVariables(substitutionMapping), inplace);
	}

	public WeqCongruenceClosure<NODE> renameVariables(final WeqCongruenceClosure<NODE> weqCc,
			final Map<Term, Term> substitutionMapping, final boolean inplace) {
		bmStart(WeqCcBmNames.RENAMEVARS);
		assert DataStructureUtils.intersection(new HashSet<>(substitutionMapping.values()),
				new HashSet<>(weqCc.getCongruenceClosure().getAllElements())).isEmpty();

		if (inplace) {
			assert !weqCc.isFrozen();
			weqCc.transformElementsAndFunctions(e -> e.renameVariables(substitutionMapping));
			bmEnd(WeqCcBmNames.RENAMEVARS);
			return weqCc;
		} else {
			final WeqCongruenceClosure<NODE> unfrozen = unfreeze(weqCc);
			unfrozen.transformElementsAndFunctions(e -> e.renameVariables(substitutionMapping));
			unfrozen.freezeOmitPropagations();
			// TODO: implement a result check here?
			bmEnd(WeqCcBmNames.RENAMEVARS);
			return unfrozen;
		}
	}

	public boolean isStrongerThan(final WeqCongruenceClosure<NODE> weqcc1, final WeqCongruenceClosure<NODE> weqcc2) {
		bmStart(WeqCcBmNames.ISSTRONGERTHAN);
		if (CcSettings.ALIGN_INPLACE && !weqcc1.isFrozen() && !weqcc2.isFrozen()) {

			alignElements(weqcc1, weqcc2, true);

			closeIfNecessary(weqcc1);
			closeIfNecessary(weqcc2);

			final boolean result = weqcc1.isStrongerThan(weqcc2);
			bmEnd(WeqCcBmNames.ISSTRONGERTHAN);
			return result;
		} else {
			final WeqCongruenceClosure<NODE> weqcc1Copy = copyWeqCc(weqcc1, true);
			final WeqCongruenceClosure<NODE> weqcc2Copy = copyWeqCc(weqcc2, true);

			alignElements(weqcc1Copy, weqcc2Copy, true);

			WeqCongruenceClosure<NODE> weqcc1CopyClosed = closeIfNecessary(weqcc1Copy);
			WeqCongruenceClosure<NODE> weqcc2CopyClosed = closeIfNecessary(weqcc2Copy);

			//TODO: not that happy with this loop
			int counter = 0;
			while (!weqcc1Copy.getAllElements().equals(weqcc2Copy.getAllElements())) {
				if (++counter > 2) {
					throw new AssertionError("not expecting to do many iterations here --> check");
				}
				alignElements(weqcc1Copy, weqcc2Copy, true);
				weqcc1CopyClosed = closeIfNecessary(weqcc1Copy);
				weqcc2CopyClosed = closeIfNecessary(weqcc2Copy);
			}

			weqcc1CopyClosed.freezeIfNecessary();
			weqcc2CopyClosed.freezeIfNecessary();

			final boolean result = weqcc1Copy.isStrongerThan(weqcc2Copy);
			bmEnd(WeqCcBmNames.ISSTRONGERTHAN);
			return result;
		}
	}

	public Pair<WeqCongruenceClosure<NODE>, WeqCongruenceClosure<NODE>> alignElements(
			final WeqCongruenceClosure<NODE> cc1, final WeqCongruenceClosure<NODE> cc2, final boolean inplace) {
		assert !inplace || !cc1.isFrozen();
		assert !inplace || !cc2.isFrozen();
		if (inplace) {
			bmStart(WeqCcBmNames.ALIGN_ELEMENTS);

			/* this single call is not enough for aligning because constant arrays may introduce elements when other
			 * elements are added based on equalities in that constraint
			 */
			while (!cc1.getAllElements().containsAll(cc2.getAllElements())
					|| !cc2.getAllElements().containsAll(cc1.getAllElements())) {
				addAllElements(cc1, cc2.getAllElements(), null, true);
				addAllElements(cc2, cc1.getAllElements(), null, true);
			}

			bmEnd(WeqCcBmNames.ALIGN_ELEMENTS);
			return new Pair<>(cc1, cc2);
		} else {
			// not inplace

			bmStart(WeqCcBmNames.ALIGN_ELEMENTS);

			final WeqCongruenceClosure<NODE> cc1Aligned = copyWeqCc(cc1, true);
			final WeqCongruenceClosure<NODE> cc2Aligned = copyWeqCc(cc2, true);


			/* this single call is not enough for aligning because constant arrays may introduce elements when other
			 * elements are added based on equalities in that constraint
			 */
			while (!cc1Aligned.getAllElements().containsAll(cc2Aligned.getAllElements())
					|| !cc2Aligned.getAllElements().containsAll(cc1Aligned.getAllElements())) {
				addAllElements(cc1Aligned, cc2Aligned.getAllElements(), null, true);
				addAllElements(cc2Aligned, cc1Aligned.getAllElements(), null, true);

			}

			cc1.freezeIfNecessary();
			cc2.freezeIfNecessary();

			bmEnd(WeqCcBmNames.ALIGN_ELEMENTS);
			return new Pair<>(cc1Aligned, cc2Aligned);
		}
	}

	public CongruenceClosure<NODE> getEmptyCc(final boolean modifiable) {
		return mCcManager.getEmptyCc(modifiable);
	}

	public  WeakEquivalenceEdgeLabel<NODE> getSingletonEdgeLabel(
			final WeakEquivalenceGraph<NODE> weakEquivalenceGraph,
			final CongruenceClosure<NODE> disjunct) {
		return new WeakEquivalenceEdgeLabel<>(weakEquivalenceGraph, Collections.singleton(disjunct));
	}

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
			final CongruenceClosure<NODE> result, final Term literalDisequalities) {
		return checkReportEqualityResult(
				CongruenceClosureSmtUtils.congruenceClosureToTerm(mMgdScript.getScript(), origCc, literalDisequalities),
				node1.getTerm(), node2.getTerm(),
				CongruenceClosureSmtUtils.congruenceClosureToTerm(mMgdScript.getScript(), result,
						literalDisequalities));
	}

	private boolean checkReportEqualityResult(final WeqCongruenceClosure<NODE> origCc, final NODE node1,
			final NODE node2, final WeqCongruenceClosure<NODE> result, final Term literalDisequalities) {
		return checkReportEqualityResult(weqCcToTerm(mMgdScript.getScript(), origCc, literalDisequalities),
				node1.getTerm(), node2.getTerm(), weqCcToTerm(mMgdScript.getScript(), result, literalDisequalities));
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
			final NODE node2, final CongruenceClosure<NODE> result, final Term literalDisequalities) {
		return checkReportDisequalityResult(
				CongruenceClosureSmtUtils.congruenceClosureToTerm(mMgdScript.getScript(), origCc, literalDisequalities),
				node1.getTerm(),
				node2.getTerm(),
				CongruenceClosureSmtUtils.congruenceClosureToTerm(mMgdScript.getScript(), result, literalDisequalities));
	}

	private boolean checkReportDisequalityResult(final WeqCongruenceClosure<NODE> origCc, final NODE node1,
			final NODE node2, final WeqCongruenceClosure<NODE> result, final Term literalDisequalities) {
		return checkReportDisequalityResult(
				weqCcToTerm(mMgdScript.getScript(), origCc, literalDisequalities),
				node1.getTerm(),
				node2.getTerm(),
				weqCcToTerm(mMgdScript.getScript(), result, literalDisequalities));
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
			final WeqCongruenceClosure<NODE> result, final Term literalDisequalities) {
		return checkProjectAwayResult(
				weqCcToTerm(mMgdScript.getScript(), original, literalDisequalities),
				nodeToProjectAway.getTerm(),
				weqCcToTerm(mMgdScript.getScript(), result, literalDisequalities));
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
			// do nothing??
//			throw new AssertionError("this actually occurs?.. just omit quantification then?");
			originalProjected = original;
		}

		final boolean res = checkImplicationHolds(script, originalProjected, result);
		mMgdScript.unlock(this);
		return res;
	}

	private boolean checkMeetResult(final CongruenceClosure<NODE> cc1, final CongruenceClosure<NODE> cc2,
			final CongruenceClosure<NODE> result, final Term literalDisequalities) {
		return checkMeetResult(
				CongruenceClosureSmtUtils.congruenceClosureToTerm(mMgdScript.getScript(), cc1, literalDisequalities),
				CongruenceClosureSmtUtils.congruenceClosureToTerm(mMgdScript.getScript(), cc2, literalDisequalities),
				CongruenceClosureSmtUtils.congruenceClosureToTerm(mMgdScript.getScript(), result, literalDisequalities)
				);
	}

	boolean checkMeetResult(final WeqCongruenceClosure<NODE> weqcc1, final WeqCongruenceClosure<NODE> weqcc2,
			final WeqCongruenceClosure<NODE> result, final Term literalDisequalities) {
		return checkMeetResult(
				weqCcToTerm(mMgdScript.getScript(), weqcc1, literalDisequalities),
				weqCcToTerm(mMgdScript.getScript(), weqcc2, literalDisequalities),
				weqCcToTerm(mMgdScript.getScript(), result, literalDisequalities));
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
			final CongruenceClosure<NODE> result, final Term literalDisequalities) {
		return checkJoinResult(
				CongruenceClosureSmtUtils.congruenceClosureToTerm(mMgdScript.getScript(), cc1, literalDisequalities),
				CongruenceClosureSmtUtils.congruenceClosureToTerm(mMgdScript.getScript(), cc2, literalDisequalities),
				CongruenceClosureSmtUtils.congruenceClosureToTerm(mMgdScript.getScript(), result, literalDisequalities)
				);
	}

	private boolean checkJoinResult(final WeqCongruenceClosure<NODE> weqcc1, final WeqCongruenceClosure<NODE> weqcc2,
			final WeqCongruenceClosure<NODE> result, final Term literalDisequalities) {
		return checkJoinResult(
				weqCcToTerm(mMgdScript.getScript(), weqcc1, literalDisequalities),
				weqCcToTerm(mMgdScript.getScript(), weqcc2, literalDisequalities),
				weqCcToTerm(mMgdScript.getScript(), result, literalDisequalities));
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
		return LBool.SAT != isStrongerThan(script, ante, succ);
	}

	/**
	 * like checkImplicationHolds(..Term..) but can be used outside assertions (no breakout-flag)
	 *
	 * @param script
	 * @param ante
	 * @param succ
	 * @return
	 */
	private LBool isStrongerThan(final Script script, final Term ante, final Term succ) {

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
//		assert satResult != LBool.UNKNOWN;
//		return satResult == LBool.UNSAT;
		return satResult;
	}

	private  boolean checkFilterDisjunctionResult(final Set<CongruenceClosure<NODE>> input,
			final Set<CongruenceClosure<NODE>> result, final Term literalDisequalities) {

		{
			if (!input.stream().anyMatch(d -> d.isInconsistent(false))
					&& !result.stream().anyMatch(d -> d.isInconsistent(false))) {
				// the result may not contain any nodes that the input does not
				final Set<NODE> nodesInput = new HashSet<>();
				input.stream().forEach(d -> nodesInput.addAll(d.getAllElements()));
				final Set<NODE> nodesResult = new HashSet<>();
				result.stream().forEach(d -> nodesResult.addAll(d.getAllElements()));
				final Set<NODE> difference = DataStructureUtils.difference(nodesResult, nodesInput);
				if (!difference.isEmpty()) {
					assert false;
					return false;
				}
			}
		}

		if (mSkipSolverChecks) {
			return true;
		}
		/*
		 * check that the filtering is an equivalence transformation
		 */
		mMgdScript.lock(this);
		mMgdScript.echo(this, new QuotedObject("WeqCcManager.checkFilterDisjunctionResult (begin)"));
		final Term term1 = disjunctionToTerm(mMgdScript.getScript(), input, literalDisequalities);
		final Term term2 = disjunctionToTerm(mMgdScript.getScript(), result, literalDisequalities);
		final boolean oneImpliesTwo = checkImplicationHolds(mMgdScript.getScript(), term1, term2);
		assert oneImpliesTwo;
		final boolean twoImpliesOne = checkImplicationHolds(mMgdScript.getScript(), term2, term1);
		assert twoImpliesOne;

		mMgdScript.echo(this, new QuotedObject("WeqCcManager.checkFilterDisjunctionResult (end)"));
		mMgdScript.unlock(this);
		return oneImpliesTwo && twoImpliesOne;

	}

	private static <NODE extends IEqNodeIdentifier<NODE>>
			Term disjunctionToTerm(final Script script, final Set<CongruenceClosure<NODE>> ccs,
					final Term literalDisequalities) {
		if (ccs.isEmpty()) {
			return script.term("false");
		}
		final Set<Term> disjunctTerms = new HashSet<>();
		for (final CongruenceClosure<NODE> cc : ccs) {
			disjunctTerms.add(CongruenceClosureSmtUtils.congruenceClosureToTerm(script,
					cc, literalDisequalities));
		}
		return SmtUtils.or(script, disjunctTerms);
	}

	public static <NODE extends IEqNodeIdentifier<NODE>> Term weqCcToTerm(final Script script,
			final WeqCongruenceClosure<NODE> weqCc, final Term literalDisequalities) {
		if (weqCc.isInconsistent(false)) {
			return script.term("false");
		}

		final List<Term> allConjuncts = new ArrayList<>();
		allConjuncts.addAll(CongruenceClosureSmtUtils.congruenceClosureToCube(script, weqCc.getCongruenceClosure(),
				literalDisequalities));

		final List<Term> weakEqConstraints = weqCc.getWeakEquivalenceGraph()
				.getWeakEquivalenceConstraintsAsTerms(script);
		allConjuncts.addAll(weakEqConstraints);

		final Term result = SmtUtils.and(script, allConjuncts.toArray(new Term[allConjuncts.size()]));
		assert weqCc.getManager().getSettings().omitSanitycheckFineGrained1() ||
			weqCc.getManager().getAllWeqVariables().stream()
				.allMatch(weqvar -> !Arrays.asList(result.getFreeVars()).contains(weqvar));
		return result;
	}

	public WeqCongruenceClosure<NODE> getWeqCongruenceClosure(final CongruenceClosure<NODE> cc,
			final WeakEquivalenceGraph<NODE> weqGraph, final boolean modifiable) {
		final CongruenceClosure<NODE> ccUnfrozen = mCcManager.unfreezeIfNecessary(cc);
		addAllElementsCc(ccUnfrozen, weqGraph.getAppearingNonWeqVarNodes(), null, true);
		final WeqCongruenceClosure<NODE> result = new WeqCongruenceClosure<>(ccUnfrozen, weqGraph, this);

		// just to be safe..n
		mNonTheoryLiteralNodes.forEach(n -> result.addElement(n, false));

		if (!modifiable) {
			result.freezeAndClose();
		}
		return result;
	}

	public  CongruenceClosure<NODE> getSingleEqualityCc(final NODE node1, final NODE node2,
			final boolean modifiable, final CongruenceClosure<NODE> dummyDisjunct) {
		return mCcManager.getSingleEqualityCc(node1, node2, modifiable);
	}

	public  CongruenceClosure<NODE> getSingleDisequalityCc(final NODE node1,
			final NODE node2, final boolean modifiable, final CongruenceClosure<NODE> dummyDisjunct) {
		return mCcManager.getSingleDisequalityCc(node1, node2, modifiable);
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
		return result;
	}

	public CongruenceClosure<NODE> copyCcNoRemInfoUnfrozen(final CongruenceClosure<NODE> cc) {
		return mCcManager.copyNoRemInfoUnfrozen(cc);
	}

	public CongruenceClosure<NODE> projectToElements(final CongruenceClosure<NODE> cc, final Set<NODE> nodesToKeep,
			final IRemovalInfo<NODE> remInfo, final boolean modifiable) {
		assert !cc.isInconsistent(false) : "catch this outside";
		CongruenceClosure<NODE> result = mCcManager.projectToElements(cc, nodesToKeep, remInfo);
		assert result.isFrozen() : "projectToElements always freezes, right?.. (because it cannot work inplace)";
		if (modifiable) {
			result = mCcManager.unfreeze(result);
		}
		return result;
	}

	public WeqCongruenceClosure<NODE> addAllElements(final WeqCongruenceClosure<NODE> weqcc,
			final Set<NODE> nodesToAdd, final IRemovalInfo<NODE> remInfo, final boolean inplace) {
		bmStart(WeqCcBmNames.ADDALLNODES);
		if (inplace) {
			for (final NODE e : nodesToAdd) {
				if (weqcc.isInconsistent(false)) {
					return weqcc;
				}
				addNode(e, weqcc, true, false);
			}
			bmEnd(WeqCcBmNames.ADDALLNODES);
			return weqcc;
		} else {
			WeqCongruenceClosure<NODE> result = unfreeze(weqcc);
			for (final NODE e : nodesToAdd) {
				if (weqcc.isInconsistent(false)) {
					return weqcc;
				}
				result = addNode(e, weqcc, false, false);
			}
			assert result.isFrozen();
			bmEnd(WeqCcBmNames.ADDALLNODES);
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
			result.freezeAndClose();
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
	public WeakEquivalenceEdgeLabel<NODE> getEdgeLabelForIndex(
			final WeakEquivalenceGraph<NODE> weakEquivalenceGraph,
			final NODE storeIndex) {
		return getSingletonEdgeLabel(weakEquivalenceGraph,
				computeWeqConstraintForIndex(Collections.singletonList(storeIndex), !weakEquivalenceGraph.isFrozen()));
	}

	public  WeakEquivalenceEdgeLabel<NODE>
		meetEdgeLabels( final WeakEquivalenceEdgeLabel<NODE> l1,
			final WeakEquivalenceEdgeLabel<NODE> l2, final boolean inplace) {
		bmStart(WeqCcBmNames.MEETEDGELABELS);

		final WeakEquivalenceEdgeLabel<NODE> result = l1.meet(l2, inplace);

		assert !inplace || result == l1 : "if inplace is set, we must return the original object";

		assert inplace || isStrongerThanPrecise(result, l1);
		assert inplace || isStrongerThanPrecise(result, l2);

		bmEnd(WeqCcBmNames.MEETEDGELABELS);
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
	 boolean checkMeetWeqLabels(
					final WeakEquivalenceEdgeLabel<NODE> l1,
					final WeakEquivalenceEdgeLabel<NODE> l2,
					final WeakEquivalenceEdgeLabel<NODE> result) {

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
	public  boolean isStrongerThan(
			final WeakEquivalenceEdgeLabel<NODE> label1,
			final WeakEquivalenceEdgeLabel<NODE> label2) {
		final boolean result;
		if (mSettings.isPreciseWeqLabelComparison()) {
			result = isStrongerThanPrecise(label1, label2);
		} else {
			result = isStrongerThan(label1, label2, this::isStrongerThan);
		}
		assert checkIsStrongerThanResult(label1, label2, result);
		return result;
	}

	 boolean isStrongerThanPrecise(
			final WeakEquivalenceEdgeLabel<NODE> label1,
			final WeakEquivalenceEdgeLabel<NODE> label2) {
		final Script script = mMgdScript.getScript();

		mMgdScript.lock(this);

		Term label1Term = SmtUtils.or(script, label1.toDnf(script));
		if (CcSettings.IMPLICIT_LITERAL_DISEQUALITIES) {
			label1Term = SmtUtils.and(script, label1Term, getNonTheoryLiteralDisequalitiesIfNecessary());
		}
		final Term label2Term = SmtUtils.or(script, label2.toDnf(script));

		final LBool satResult = isStrongerThan(script, label1Term, label2Term);
		assert satResult != LBool.UNKNOWN : "TODO: solve this problem.. implement a fallback??";
		final boolean implicationHolds = satResult == LBool.UNSAT;

		mMgdScript.unlock(this);
		return implicationHolds;
	}

	private  boolean checkIsStrongerThanResult(
			final WeakEquivalenceEdgeLabel<NODE> label1,
			final WeakEquivalenceEdgeLabel<NODE> label2, final boolean impCheckResult) {

		if (mSkipSolverChecks) {
			return true;
		}

		final Script script = mMgdScript.getScript();

		mMgdScript.lock(this);

		final Term label1Term = SmtUtils.or(script, label1.toDnf(script));
		final Term label2Term = SmtUtils.or(script, label2.toDnf(script));

		final LBool satResult = isStrongerThan(script, label1Term, label2Term);

		mMgdScript.unlock(this);

		if (satResult == LBool.UNKNOWN) {
			return true;
		}

		final boolean implicationHolds = satResult == LBool.UNSAT;

		final boolean result;
//		if (label2.getDisjuncts().size() <= 1) {
//			// special case where our implication check is conceptually precise
//			result = implicationHolds == impCheckResult;
//			assert result;
//		} else {
			/*
			 * in general our implication check approximates: If its says the implication holds, it holds, but it may
			 *  not detect a valid implication  in all cases.
			 */
			result = !impCheckResult || implicationHolds;
			assert result;
//		}

		return result;
	}

	public  boolean isStrongerThan(
			final WeakEquivalenceEdgeLabel<NODE> label1,
			final WeakEquivalenceEdgeLabel<NODE> label2,
			final BiPredicate<CongruenceClosure<NODE>, CongruenceClosure<NODE>> lowerOrEqual) {
		bmStart(WeqCcBmNames.ISLABELSTRONGERTHAN);
		for (final CongruenceClosure<NODE> label1disjunct : label1.getDisjuncts()) {
			boolean existsWeaker = false;
			for (final CongruenceClosure<NODE> label2disjunct : label2.getDisjuncts()) {
				if (lowerOrEqual.test(label1disjunct, label2disjunct)) {
					existsWeaker = true;
					break;
				}
			}
			if (!existsWeaker) {
				bmEnd(WeqCcBmNames.ISLABELSTRONGERTHAN);
				return false;
			}
		}
		bmEnd(WeqCcBmNames.ISLABELSTRONGERTHAN);
		return true;
	}

	public boolean isStrongerThan(final CongruenceClosure<NODE> paThis, final CongruenceClosure<NODE> paOther) {
		return mCcManager.isStrongerThan(paThis, paOther);
	}

	public boolean isEquivalentCc(final WeakEquivalenceEdgeLabel<NODE> label1,
			final WeakEquivalenceEdgeLabel<NODE> label2) {
		return isStrongerThan(label1, label2) && isStrongerThan(label2, label1);
	}

	public  boolean isStrongerThan(
			final WeakEquivalenceGraph<NODE> weakEquivalenceGraph,
			final WeakEquivalenceGraph<NODE> weakEquivalenceGraph2) {
		bmStart(WeqCcBmNames.ISWEQGRAPHSTRONGERTHAN);

		assert weakEquivalenceGraph.getBaseWeqCc().isClosed() && weakEquivalenceGraph2.getBaseWeqCc().isClosed();

		final boolean result = weakEquivalenceGraph.isStrongerThan(weakEquivalenceGraph2);
		bmEnd(WeqCcBmNames.ISWEQGRAPHSTRONGERTHAN);
		return result;
	}

	private  void freezeIfNecessary(
			final WeakEquivalenceGraph<NODE> weakEquivalenceGraph) {
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
	public  WeakEquivalenceGraph<NODE> join(
			final WeakEquivalenceGraph<NODE> weakEquivalenceGraph,
			final WeakEquivalenceGraph<NODE> weakEquivalenceGraph2,
			final boolean modifiable) {
		bmStart(WeqCcBmNames.WEQGRAPHJOIN);
		freezeIfNecessary(weakEquivalenceGraph);
		freezeIfNecessary(weakEquivalenceGraph2);

		final WeakEquivalenceGraph<NODE> result = weakEquivalenceGraph.join(weakEquivalenceGraph2);

		if (!modifiable) {
			result.freeze();
		}

		bmEnd(WeqCcBmNames.WEQGRAPHJOIN);
		return result;
	}

	public WeqCongruenceClosure<NODE> copyWeqCc(final WeqCongruenceClosure<NODE> original, final boolean modifiable) {
		final WeqCongruenceClosure<NODE> result = new WeqCongruenceClosure<>(original);
		if (!modifiable) {
			result.freezeAndClose();
		}
		return result;
	}

	public CongruenceClosure<NODE> copyCc(final CongruenceClosure<NODE> icc, final boolean modifiable) {
		return mCcManager.getCopy(icc, modifiable);
	}

	public  WeakEquivalenceEdgeLabel<NODE>
			copy(final WeakEquivalenceEdgeLabel<NODE> original, final boolean omitSanityCheck,
					final boolean modifiable) {
		return copy(original, original.getWeqGraph(), omitSanityCheck, modifiable);
	}

	public  WeakEquivalenceEdgeLabel<NODE>
			copy(final WeakEquivalenceEdgeLabel<NODE> original, final boolean modifiable) {
		return copy(original, original.getWeqGraph(), modifiable);
	}

	public WeqCongruenceClosure<NODE> unfreezeIfNecessary(final WeqCongruenceClosure<NODE> weqcc) {
		if (weqcc.isFrozen()) {
			return unfreeze(weqcc);
		} else {
			return weqcc;
		}
	}


	public  WeakEquivalenceEdgeLabel<NODE> copy(
			final WeakEquivalenceEdgeLabel<NODE> value,
			final WeakEquivalenceGraph<NODE> weakEquivalenceGraph,
			final boolean modifiable) {
		return copy(value, weakEquivalenceGraph, false, modifiable);
	}


	public  WeakEquivalenceEdgeLabel<NODE> copy(
			final WeakEquivalenceEdgeLabel<NODE> value,
			final WeakEquivalenceGraph<NODE> weakEquivalenceGraph,
			final boolean omitSanityCheck,
			final boolean modifiable) {
		final WeakEquivalenceEdgeLabel<NODE> result = new WeakEquivalenceEdgeLabel<>(weakEquivalenceGraph,
				value, omitSanityCheck);
		if (!modifiable) {
			result.freeze();
		}
		return result;
	}


	public  WeakEquivalenceGraph<NODE> unfreeze(
			final WeakEquivalenceGraph<NODE> weqGraph) {
		return new WeakEquivalenceGraph<>(weqGraph.getBaseWeqCc(), weqGraph);
	}

	public  WeakEquivalenceEdgeLabel<NODE>
			unfreeze(final WeakEquivalenceEdgeLabel<NODE> value) {
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

		final Term term1 = weqCcToTerm(mMgdScript.getScript(), weqcc1,
				getNonTheoryLiteralDisequalitiesIfNecessary());
		final Term term2 = weqCcToTerm(mMgdScript.getScript(), weqcc2,
				getNonTheoryLiteralDisequalitiesIfNecessary());

		final boolean oneImpliesTwo = checkImplicationHolds(mMgdScript.getScript(), term1, term2);
		assert oneImpliesTwo;

		final boolean twoImpliesOne = checkImplicationHolds(mMgdScript.getScript(), term2, term1);
		assert twoImpliesOne;

		mMgdScript.unlock(this);

		return oneImpliesTwo && twoImpliesOne;
	}

	public Term getNonTheoryLiteralDisequalitiesIfNecessary() {
		if (CcSettings.ADD_NON_THEORYlITERAL_DISEQUALITIES_FOR_CHECKS) {
			return mNodeAndFunctionFactory.getNonTheoryLiteralDisequalities();
		} else {
			return mMgdScript.getScript().term("true");
		}
	}

	public WeqSettings getSettings() {
		return mSettings;
	}

	public int getDimensionOfWeqVar(final NODE weqVarNode) {
		for (final Triple<Sort, Integer, NODE> en : mDimensionToWeqVariableNode.entrySet()) {
			if (en.getThird().equals(weqVarNode)) {
				return en.getSecond();
			}
		}
		throw new AssertionError("weq var unknown: " + weqVarNode);
	}

	public BenchmarkWithCounters getBenchmark() {
		return mBenchmark;
	}

	public CcManager<NODE> getCcManager() {
		return mCcManager;
	}

	static enum WeqCcBmNames {

		FILTERREDUNDANT, UNFREEZE, COPY, MEET, JOIN, ISSTRONGERTHAN, ADDNODE, REPORTEQUALITY,
		REPORTDISEQUALITY, REPORTWEQ, REPORTCONTAINS, PROJECTAWAY, RENAMEVARS, ADDALLNODES,
		MEETEDGELABELS, ISLABELSTRONGERTHAN, ISWEQGRAPHSTRONGERTHAN, WEQGRAPHJOIN, FREEZE_AND_CLOSE, FREEZEONLY,
		EXT_AND_TRIANGLE_CLOSURE, ALIGN_ELEMENTS;

		static String[] getNames() {
			final String[] result = new String[values().length];
			for (int i = 0; i < values().length; i++) {
				result[i] = values()[i].name();
			}
			return result;
		}
	}

	public  void replaceElement(final WeakEquivalenceEdgeLabel<NODE> aToB, final NODE replacer, final NODE replacee) {
		final Function<NODE, NODE> transformer = n -> n.equals(replacee) ? replacer : n;
		aToB.transformElements(transformer);
	}

	public  WeakEquivalenceEdgeLabel<NODE> reportEquality(
			final WeakEquivalenceEdgeLabel<NODE> label, final NODE n1, final NODE n2,
			final boolean inplace) {
		if (inplace) {
			for (final CongruenceClosure<NODE> d : label.getDisjuncts()) {
				reportEquality(d, n1, n2, true);
			}
			return label;
		} else {
			final Set<CongruenceClosure<NODE>> newDisjuncts = new HashSet<>();
			for (final CongruenceClosure<NODE> d : label.getDisjuncts()) {
				freezeIfNecessary(d);
				final CongruenceClosure<NODE> newD = reportEquality(d, n1, n2, false);
				if (!newD.isInconsistent()) {
					newDisjuncts.add(newD);
				}
			}
			return new WeakEquivalenceEdgeLabel<>(label.getWeqGraph(), newDisjuncts);
		}

	}

	public boolean isDebugMode() {
		return mDebug;
	}
}
