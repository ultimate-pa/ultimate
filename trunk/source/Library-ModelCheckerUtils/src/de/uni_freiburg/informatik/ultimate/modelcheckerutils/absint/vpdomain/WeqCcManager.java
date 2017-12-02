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
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.CongruenceClosure;
import de.uni_freiburg.informatik.ultimate.util.datastructures.RemoveCcElement;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.IPartialComparator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.PartialOrderCache;

public class WeqCcManager<NODE extends IEqNodeIdentifier<NODE>> {

	private final CcManager<NODE> mCcManager;
	private final ManagedScript mMgdScript;

	public WeqCcManager(final IPartialComparator<CongruenceClosure<NODE>> ccComparator, final ManagedScript mgdScript) {
		mCcManager = new CcManager<>(ccComparator, mgdScript);
		mMgdScript = mgdScript;
	}

	WeqCongruenceClosure<NODE> getWeqMeet(final CongruenceClosure<NODE> cc,
			final WeqCongruenceClosure<NODE> weqcc, final RemoveCcElement<NODE> remInfo) {

		final WeqCongruenceClosure<NODE> result;
		if (remInfo == null) {
			result = weqcc.meetRec(cc);
		} else {
			assert false : "do we need this case?";
			result = null;
		}
		if (result.isInconsistent()) {
			return result;
		}
		return result;
	}

	public WeqCongruenceClosure<NODE> getWeqMeet(final CongruenceClosure<NODE> cc,
			final WeqCongruenceClosure<NODE> weqcc) {
		return getWeqMeet(cc, weqcc, null);
	}

	public WeqCongruenceClosure<NODE> addNode(final NODE node, final WeqCongruenceClosure<NODE> origWeqCc) {
		if (origWeqCc.hasElement(node)) {
			// node is already present --> nothing to do
			return origWeqCc;
		}

		final WeqCongruenceClosure<NODE> unfrozen = unfreeze(origWeqCc);
		unfrozen.addElement(node);
		unfrozen.freeze();
		return unfrozen;
	}

	private WeqCongruenceClosure<NODE> unfreeze(final WeqCongruenceClosure<NODE> origWeqCc) {
		assert origWeqCc.isFrozen();
		return new WeqCongruenceClosure<>(origWeqCc);
	}

	public WeakEquivalenceEdgeLabel<NODE> filterRedundantCcs(final WeakEquivalenceEdgeLabel<NODE> label) {
		final Set<CongruenceClosure<NODE>> filtered = mCcManager.filterRedundantCcs(label.getLabelContents());
		return new WeakEquivalenceEdgeLabel<>(label.getWeqGraph(), filtered);
	}

	public Set<CongruenceClosure<NODE>> filterRedundantCcs(final Set<CongruenceClosure<NODE>> ccs) {
		return mCcManager.filterRedundantCcs(ccs);
	}

	public IPartialComparator<CongruenceClosure<NODE>> getCcComparator() {
		return mCcManager.getCcComparator();
	}

	public Set<CongruenceClosure<NODE>> filterRedundantCcs(final Set<CongruenceClosure<NODE>> ccs,
			final PartialOrderCache<CongruenceClosure<NODE>> ccPoCache) {
		return mCcManager.filterRedundantCcs(ccs, ccPoCache);
	}


	public WeqCongruenceClosure<NODE> reportEquality(final WeqCongruenceClosure<NODE> origWeqCc, final NODE node1,
			final NODE node2) {
		if (WeqSettings.REPORT_EQ_DEQ_INPLACE) {
			origWeqCc.reportEquality(node1, node2);
			return origWeqCc;
		} else {
			final WeqCongruenceClosure<NODE> unfrozen = unfreeze(origWeqCc);
			unfrozen.reportEquality(node1, node2);
			unfrozen.freeze();
			return unfrozen;
		}
	}

	public WeqCongruenceClosure<NODE> reportDisequality(final WeqCongruenceClosure<NODE> origWeqCc, final NODE node1,
			final NODE node2) {
		if (WeqSettings.REPORT_EQ_DEQ_INPLACE) {
			origWeqCc.reportDisequality(node1, node2);
			return origWeqCc;
		} else {
			final WeqCongruenceClosure<NODE> unfrozen = unfreeze(origWeqCc);
			unfrozen.reportDisequality(node1, node2);
			unfrozen.freeze();
			return unfrozen;
		}
	}

	public WeqCongruenceClosure<NODE> makeCopyForWeqMeet(final WeqCongruenceClosure<NODE> originalPa) {
		final WeqCongruenceClosure<NODE> result = new WeqCongruenceClosure<>(originalPa, true);
		if (!WeqSettings.REPORT_EQ_DEQ_INPLACE) {
			result.freeze();
		}
		return result;
	}

	public WeqCongruenceClosure<NODE> makeCopy(final WeqCongruenceClosure<NODE> original) {
		if (original.isFrozen()) {
			// original is frozen --> a copy should not be necessary (use unfreeze if an unfrozen copy is needed)
			return original;
		}
		return new WeqCongruenceClosure<>(original, false);
	}

	public WeqCongruenceClosure<NODE> meet(final WeqCongruenceClosure<NODE> weqcc1,
			final WeqCongruenceClosure<NODE> weqcc2) {
		return weqcc1.meet(weqcc2);
	}

	public CongruenceClosure<NODE> meet(final CongruenceClosure<NODE> cc1, final CongruenceClosure<NODE> cc2,
			final RemoveCcElement<NODE> elementCurrentlyBeingRemoved) {
		// (just passing it through to CcManager)
		final CongruenceClosure<NODE> result = mCcManager.meet(cc1, cc2, elementCurrentlyBeingRemoved);
		assert checkMeetResult(cc1, cc2, result);
		return result;
	}

	public CongruenceClosure<NODE> join(final CongruenceClosure<NODE> cc1, final CongruenceClosure<NODE> cc2,
			final RemoveCcElement<NODE> elementCurrentlyBeingRemoved) {
		// (just passing it through to CcManager)
		final CongruenceClosure<NODE> result = mCcManager.join(cc1, cc2);
		assert checkJoinResult(cc1, cc2, result);
		return result;
	}

	public WeqCongruenceClosure<NODE> join(final WeqCongruenceClosure<NODE> weqcc1,
			final WeqCongruenceClosure<NODE> weqcc2) {
		final WeqCongruenceClosure<NODE> result = weqcc1.join(weqcc2);
		assert checkJoinResult(weqcc1, weqcc2, result);
		return result;
	}

	public boolean isStrongerThan(final WeqCongruenceClosure<NODE> partialArrangement,
			final WeqCongruenceClosure<NODE> partialArrangement2) {
		return partialArrangement.isStrongerThan(partialArrangement2);
	}

	public WeakEquivalenceEdgeLabel<NODE> getSingletonEdgeLabel(final WeakEquivalenceGraph<NODE> weakEquivalenceGraph,
			final CongruenceClosure<NODE> newConstraint) {
		return new WeakEquivalenceEdgeLabel<>(weakEquivalenceGraph, Collections.singleton(newConstraint));
	}

	public WeakEquivalenceEdgeLabel<NODE> getSingletonEdgeLabel(final WeakEquivalenceGraph<NODE> weakEquivalenceGraph,
			final Set<CongruenceClosure<NODE>> constraints) {
		return new WeakEquivalenceEdgeLabel<>(weakEquivalenceGraph, constraints);
	}

	public CongruenceClosure<NODE> addNode(final NODE storeIndex, final CongruenceClosure<NODE> congruenceClosure) {
		return mCcManager.addElement(congruenceClosure, storeIndex);
	}



	public static <NODE extends IEqNodeIdentifier<NODE>> Term weqCcToTerm(final Script script,
			final WeqCongruenceClosure<NODE> weqCc) {
		final List<Term> allConjuncts = new ArrayList<>();
//		allConjuncts.addAll(EqConstraint.partialArrangementToCube(script, this));
		allConjuncts.addAll(CcManager.congruenceClosureToCube(script, weqCc.getCongruenceClosure()));

		final List<Term> weakEqConstraints = weqCc.getWeakEquivalenceGraph()
				.getWeakEquivalenceConstraintsAsTerms(script);
		allConjuncts.addAll(weakEqConstraints);

		final Term result = SmtUtils.and(script, allConjuncts.toArray(new Term[allConjuncts.size()]));
		return result;
	}

	private boolean checkMeetResult(final CongruenceClosure<NODE> cc1, final CongruenceClosure<NODE> cc2,
			final CongruenceClosure<NODE> result) {
		return checkMeetResult(
				CcManager.congruenceClosureToTerm(mMgdScript.getScript(), cc1),
				CcManager.congruenceClosureToTerm(mMgdScript.getScript(), cc2),
				CcManager.congruenceClosureToTerm(mMgdScript.getScript(), result));
	}

	private boolean checkJoinResult(final CongruenceClosure<NODE> cc1, final CongruenceClosure<NODE> cc2,
			final CongruenceClosure<NODE> result) {
		return checkJoinResult(
				CcManager.congruenceClosureToTerm(mMgdScript.getScript(), cc1),
				CcManager.congruenceClosureToTerm(mMgdScript.getScript(), cc2),
				CcManager.congruenceClosureToTerm(mMgdScript.getScript(), result));
	}

	private boolean checkJoinResult(final WeqCongruenceClosure<NODE> cc1, final WeqCongruenceClosure<NODE> cc2,
			final WeqCongruenceClosure<NODE> result) {
		return checkJoinResult(
				weqCcToTerm(mMgdScript.getScript(), cc1),
				weqCcToTerm(mMgdScript.getScript(), cc2),
				weqCcToTerm(mMgdScript.getScript(), result));
	}

	private boolean checkMeetResult(final Term cc1, final Term cc2,
			final Term resultTerm) {
		// check that cc1 /\ cc2 -> result
		mMgdScript.lock(this);
		final Script script = mMgdScript.getScript();
		final Term cc1AndCc2Term = SmtUtils.and(script, cc1, cc2);
		final boolean res = checkImplicationHolds(script, cc1AndCc2Term, resultTerm);
		mMgdScript.unlock(this);
		return res;
	}

	private boolean checkJoinResult(final Term cc1, final Term cc2,
			final Term resultTerm) {
		// check that cc1 /\ cc2 -> result
		mMgdScript.lock(this);
		final Script script = mMgdScript.getScript();
		final Term cc1AndCc2Term = SmtUtils.or(script, cc1, cc2);
		final boolean res = checkImplicationHolds(script, cc1AndCc2Term, resultTerm);
		mMgdScript.unlock(this);
		return res;
	}

	private boolean checkImplicationHolds(final Script script, final Term ante, final Term succ) {
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

		assert satResult == LBool.UNSAT;
		return satResult == LBool.UNSAT;
	}


}
