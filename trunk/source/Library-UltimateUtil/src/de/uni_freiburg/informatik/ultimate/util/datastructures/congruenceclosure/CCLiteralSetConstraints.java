/*
 * Copyright (C) 2018 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE Util Library.
 *
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Util Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Handles "literal set" constraints. In addition to equalities and disequalities, A CongruenceClosure may have
 * constraints of the form "l in L", where l is a literal and L is a set of literals.
 * These constraints are handled through an instance of this class.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class CCLiteralSetConstraints<ELEM extends ICongruenceClosureElement<ELEM>> {

	private final CcManager<ELEM> mCcManager;
	SetConstraintManager<ELEM> mSetConstraintManager;

	private CongruenceClosure<ELEM> mCongruenceClosure;

	private Map<ELEM, SetConstraintConjunction<ELEM>> mContainsConstraints;

	private boolean mIsInconsistent;

	public CCLiteralSetConstraints(final CcManager<ELEM> manager, final CongruenceClosure<ELEM> congruenceClosure) {
		mCcManager = manager;
		mCongruenceClosure = congruenceClosure;
		mSetConstraintManager = manager.getSetConstraintManager();

		mContainsConstraints = new HashMap<>();
		mIsInconsistent = false;
//		assert CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_3 || sanityCheck();
	}

	/**
	 * copy constructor
	 * @param manager
	 * @param congruenceClosure
	 * @param containsConstraints
	 */
	CCLiteralSetConstraints(final CcManager<ELEM> manager, final CongruenceClosure<ELEM> congruenceClosure,
			final CCLiteralSetConstraints<ELEM> litSetConstraints) {
		assert !litSetConstraints.isInconsistent();
		mCcManager = manager;
		mCongruenceClosure = congruenceClosure;
		mSetConstraintManager = manager.getSetConstraintManager();

		mContainsConstraints = new HashMap<>();
		// deep copy
		for (final Entry<ELEM, SetConstraintConjunction<ELEM>> en : litSetConstraints.getConstraints().entrySet()) {
			mContainsConstraints.put(en.getKey(), new SetConstraintConjunction<>(this, en.getValue()));
		}
		mIsInconsistent = false;
//		assert CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_3 || sanityCheck();
	}

	public HashRelation<ELEM, ELEM> reportContains(final ELEM element, final Set<SetConstraint<ELEM>> constraintRaw) {
		assert CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_3 || sanityCheck();


		final ELEM elementRep = mCongruenceClosure.getRepresentativeElement(element);

		final Set<SetConstraint<ELEM>> constraintUpdRep =
				mSetConstraintManager.updateOnChangedRepresentative(constraintRaw, mCongruenceClosure);


		final Set<SetConstraint<ELEM>> oldConstraint = getConstraint(element);
		// just for analogy to reportEquality
		mContainsConstraints.remove(elementRep);

		Set<SetConstraint<ELEM>> newConstraint;
		if (oldConstraint != null) {
			newConstraint = DataStructureUtils.union(oldConstraint, constraintUpdRep);
		} else {
			newConstraint = constraintUpdRep;
		}

		HashRelation<ELEM, ELEM> equalitiesToPropagate = null;
		if (newConstraint != null) {
			equalitiesToPropagate = updateContainsConstraintApplyPropagations(elementRep, newConstraint);
		}
		return equalitiesToPropagate;
	}

	public HashRelation<ELEM, ELEM> reportContains(final ELEM element, final Collection<ELEM> elements) {
		assert CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_3 || sanityCheck();

		if (isInconsistent()) {
			// nothing to do
			return null;
		}


		mCcManager.addElement(mCongruenceClosure, element, true, false);
		mCcManager.addAllElements(mCongruenceClosure, elements, null, true);

		final ELEM elementRep = mCongruenceClosure.getRepresentativeElement(element);

		return reportContains(elementRep, Collections.singleton(mSetConstraintManager.buildSetConstraint(elements)));// additionalConstraint);
	}

	/**
	 *
	 * @param constrainedElemRep
	 * @param newConstraint
	 * @return a pair of elements whose equality should be propagated, or null
	 */
	private HashRelation<ELEM, ELEM> updateContainsConstraintApplyPropagations(final ELEM constrainedElemRep,
			final Set<SetConstraint<ELEM>> newConstraint) {
		assert !mContainsConstraints.containsKey(constrainedElemRep) : "assuming this has been removed before";
		assert mCongruenceClosure.isRepresentative(constrainedElemRep);
		assert CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_3 || sanityCheck();

		final HashRelation<ELEM, ELEM> result = new HashRelation<>();

		final Set<SetConstraint<ELEM>> newConstraintFiltered =
				mSetConstraintManager.filterWithDisequalities(mCongruenceClosure, constrainedElemRep, newConstraint);

		/*
		 * rule: e in {} --> \bot
		 */
		if (newConstraintFiltered.stream().anyMatch(SetConstraint::isInconsistent)) {
			reportInconsistency();
			return result;
		}

		final Set<SetConstraint<ELEM>> newConstraint1 =
				mCcManager.normalizeSetConstraintConjunction(this, newConstraintFiltered);


		/*
		 * rule: e in {l} --> e ~ l
		 * (containsConstraint is implicit in this case)
		 */
		for (final ELEM sv : mSetConstraintManager.getSingletonValues(newConstraint1)) {
			if (!constrainedElemRep.equals(sv)) {
				result.addPair(constrainedElemRep, sv);
			}
		}

		final SetConstraintConjunction<ELEM> newConstraint2 =
				mCcManager.buildSetConstraintConjunction(this, constrainedElemRep, newConstraint1);

		if (!newConstraint2.isTautological()) {
			// not tautological, not a singeton --> save the new constraint
			putContainsConstraint(constrainedElemRep, newConstraint2);
		}

		assert CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_3 || sanityCheck();
		return result;
	}

	private void reportInconsistency() {
		mIsInconsistent = true;
		mContainsConstraints = null;
	}

	/**
	 * Call this when an equality is reported in mCongruenceClosure
	 * <li> updates representatives
	 * <li> applies the rule "e ~ l --> e in {l}" (if one of the elements is a literal)
	 *    EDIT: this rule is automatically dealt with because we only store representatives here and literals are always
	 *      the representatives of their equivalence class. We leave the containments l in {l} implicit.
	 *
	 * <li> EDIT (may18): what was not dealt with before:
	 *   updating representatives may not be enough, because some propagation rules might trigger:
	 *     e.g., if one of the newly equated elements has a disequality constraint, and one has a set constraint, they
	 *      might interact
	 *      (example: e1 in {l1, l2}, e2 != l1, e2 != l2 && e1 = e2 --> bottom)
	 *
	 * @param elem1OldRep
	 * @param elem2OldRep
	 * @param newRep
	 * @return
	 */
	public HashRelation<ELEM, ELEM> reportEquality(final ELEM elem1OldRep, final ELEM elem2OldRep, final ELEM newRep) {
		assert mCongruenceClosure.getRepresentativeElement(elem1OldRep) == newRep;
		assert mCongruenceClosure.getRepresentativeElement(elem2OldRep) == newRep;

		if (isInconsistent()) {
			// nothing to do
			return null;
		}

		Set<SetConstraint<ELEM>> elem1LiteralSet = getConstraint(elem1OldRep);
		Set<SetConstraint<ELEM>> elem2LiteralSet = getConstraint(elem2OldRep);
		mContainsConstraints.remove(elem1OldRep);
		mContainsConstraints.remove(elem2OldRep);

		if (elem1LiteralSet != null) {
			elem1LiteralSet =
					mSetConstraintManager.updateOnChangedRepresentative(elem1LiteralSet, elem1OldRep, elem2OldRep, newRep);
		}
		if (elem2LiteralSet != null) {
			elem2LiteralSet =
					mSetConstraintManager.updateOnChangedRepresentative(elem2LiteralSet, elem1OldRep, elem2OldRep, newRep);
		}

		Set<SetConstraint<ELEM>> newConstraint = null;
		if (elem1LiteralSet != null && elem2LiteralSet != null)  {
			newConstraint =
					mSetConstraintManager.meet(this, elem1LiteralSet, elem2LiteralSet);
		} else if (elem1LiteralSet != null) {
			newConstraint = elem1LiteralSet;
		} else if (elem2LiteralSet != null) {
			newConstraint = elem2LiteralSet;
		} else {
			// no contains-constraints on either element present --> nothing to do
		}

		// update the other set constraints according to the change in representatives
		for (final Entry<ELEM, SetConstraintConjunction<ELEM>> en : new HashSet<>(mContainsConstraints.entrySet())) {
			final Set<SetConstraint<ELEM>> oldSc = en.getValue().getSetConstraints();
			final Set<SetConstraint<ELEM>> newSc =
					mSetConstraintManager.updateOnChangedRepresentative(oldSc, elem1OldRep, elem2OldRep, newRep);

			assert newSc == oldSc || mSetConstraintManager.getSingletonValues(newSc).isEmpty();
			final SetConstraintConjunction<ELEM> updated = newSc == oldSc ? en.getValue() :
					mCcManager.buildSetConstraintConjunction(this, en.getKey(), newSc);
			mContainsConstraints.put(en.getKey(), updated);
		}

		HashRelation<ELEM, ELEM> eqToProp = null;
		if (newConstraint != null) {
			eqToProp = updateContainsConstraintApplyPropagations(newRep, newConstraint);
		}
		assert CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_3 || sanityCheck();
		return eqToProp;
	}

	public CCLiteralSetConstraints<ELEM> join(final CongruenceClosure<ELEM> newCc,
			final HashRelation<ELEM, ELEM> thisSplitInfo,
			final HashRelation<ELEM, ELEM> otherSplitInfo,
			final CCLiteralSetConstraints<ELEM> other) {
		if (this.isInconsistent()) {
			return other;
		}
		if (other.isInconsistent()) {
			return this;
		}
		/*
		 * Note that we cannot do shortcut on (this.isTautological() || other.isTautological()) here, because if we
		 *  join x = 1 and x = 2, the literal set constraints by themselves are tautological/empty..
		 */

		final CCLiteralSetConstraints<ELEM> newSetConstraints = new CCLiteralSetConstraints<>(mCcManager, newCc);

		final Map<ELEM, SetConstraintConjunction<ELEM>> newContainsConstraints = new HashMap<>();

		for (final ELEM constrainedElem : newCc.getAllRepresentatives()) {
			final Set<SetConstraint<ELEM>> thisConstraint =
					this.getConstraintWrtSplit(constrainedElem, newCc, thisSplitInfo);
			final Set<SetConstraint<ELEM>> otherConstraint =
					other.getConstraintWrtSplit(constrainedElem, newCc, otherSplitInfo);

			final Set<SetConstraint<ELEM>> newConstraints =
					mSetConstraintManager.join(newSetConstraints, thisConstraint, otherConstraint);

			assert mSetConstraintManager.getSingletonValues(newConstraints).stream()
				.filter(sv -> !newCc.getRepresentativeElement(sv).equals(constrainedElem))
				.collect(Collectors.toSet()).isEmpty()
					: "created non-tautological singleton set constraints "
						+ "--> report them, befor buildSetConstraintConj.. throws them away!";
			final SetConstraintConjunction<ELEM> newConstraint =
					mCcManager.buildSetConstraintConjunction(newSetConstraints, constrainedElem, newConstraints);

			if (mSetConstraintManager.isTautological(newConstraint)) {
				// tautological constraint --> nothing to add
			} else {
				newContainsConstraints.put(constrainedElem, newConstraint);
			}

		}

		newSetConstraints.setContainsConstraints(newContainsConstraints);

		return newSetConstraints;
	}

	private void setContainsConstraints(final Map<ELEM, SetConstraintConjunction<ELEM>> newContainsConstraints) {
		mContainsConstraints = newContainsConstraints;
	}

	public boolean isStrongerThan(
			final CCLiteralSetConstraints<ELEM> other) {
		assert CcManager.isPartitionStronger(this.getCongruenceClosure().mElementTVER,
				other.getCongruenceClosure().mElementTVER) : "assuming this has been checked already";

		final Set<ELEM> constrainedElements = new HashSet<>();
		constrainedElements.addAll(this.mContainsConstraints.keySet());
		constrainedElements.addAll(other.mContainsConstraints.keySet());


		final HashRelation<ELEM, ELEM> splitInfo = CcManager.computeSplitInfo(this.getCongruenceClosure(),
				other.getCongruenceClosure());

		for (final ELEM elem : constrainedElements) {

			// [old: the two constraints must be in terms of the same representatives --> adapt the first to the second..]
			/*
			 *  update the literal constraints wrt the split that the congruenceclosure has between first and second
			 *  (at this point we already know that the Cc of other is weaker or equal than the Cc of this, so the
			 *  partition can only be finer.
			 */
			final Set<SetConstraint<ELEM>> firstConstraint = //this.getConstraint(elem);
//				mSetConstraintManager.updateOnChangedRepresentative(this.getConstraint(elem),
//						other.getCongruenceClosure());
					getConstraintWrtSplit(elem, other.getCongruenceClosure(), splitInfo);
			final Set<SetConstraint<ELEM>> secondConstraint = other.getConstraint(elem);

			if (!mSetConstraintManager.isStrongerThan(firstConstraint, secondConstraint)) {
				return false;
			}
		}
		return true;
	}

	public boolean isInconsistent() {
		return mIsInconsistent;
	}

	boolean sanityCheck() {
		if (mIsInconsistent) {
			return true;
		}

		/*
		 * <li> we only store representatives in our set of constraints, i.e., for each explicitly stored constraint
		 *  "e in L", e must be a representative in mCongruenceClosure.
		 * <li> we leave the constraints of the form "l in {l}" implicit.
		 */
//		for (final ELEM el : mContainsConstraints.keySet()) {
		for (final Entry<ELEM, SetConstraintConjunction<ELEM>> en : mContainsConstraints.entrySet()) {
			if (!mCongruenceClosure.isRepresentative(en.getKey())) {
				assert false;
				return false;
			}
			if (en.getValue().isTautological()) {
				assert false;
				return false;
			}
			// this is not a violation: e.g., 2 in {x, y} is a valid (in the sense of "sane") constraint
//			if (en.getKey().isLiteral()) {
//				assert false;
//				return false;
//			}
		}

		/*
		 * for any constrain "e in L", all elements of L must be literals
		 */
		for (final SetConstraintConjunction<ELEM> constraint : mContainsConstraints.values()) {
			if (!constraint.sanityCheck()) {
				assert false;
				return false;
			}

			if (constraint.mSurroundingCCSetConstraints != this) {
				assert false;
				return false;
			}
//			if (literalSet.size() == 1) {
//				// we leave constraints of the form l in {l} implicit
//				assert false;
//				return false;
//			}
//			if (!literalSet.stream().allMatch(ELEM::isLiteral)) {
//				assert false;
//				return false;
//			}
		}

		if (mCongruenceClosure.mLiteralSetConstraints != this) {
				assert false;
				return false;
		}

		return true;
	}

	public Map<ELEM, SetConstraintConjunction<ELEM>> getConstraints() {
		return Collections.unmodifiableMap(mContainsConstraints);
	}

	/**
	 * Return the constraint of the form "e in L U N" that the set constraints of mCongruenceClosure puts on elem.
	 *
	 * If there is a set constraint, return the set.
	 * Otherwise return null (for "unconstrained")
	 *
	 * @param elem
	 * @return
	 */
	Set<SetConstraint<ELEM>> getConstraint(final ELEM elem) {
		if (!mCongruenceClosure.hasElement(elem)) {
			return null;
		}


		final Set<SetConstraint<ELEM>> result = new HashSet<>();

		final ELEM rep = mCongruenceClosure.getRepresentativeElement(elem);

		/* an equality x ~ y implies a set constraint x in {y}, which we add to the conjunction. */
//		if (!rep.equals(elem)) {
			result.add(mSetConstraintManager.buildSetConstraint(Collections.singleton(rep)));
//		}
		// dont do this: (only talk about representatives..)
//		for (final ELEM eqMember : mCongruenceClosure.getEquivalenceClass(elem)) {
//			result.add(mSetConstraintManager.buildSetConstraint(Collections.singleton(eqMember)));
//		}

		{
			final SetConstraintConjunction<ELEM> sccRep = mContainsConstraints.get(rep);
			if (sccRep != null) {
				result.addAll(sccRep.getSetConstraints());
			}
			/*
			 * for good measure: also check if there is a constraint stored under elem when elem is not rep (happens during
			 *   CCLiteralSetConstraint.reportEquality
			 */
			final SetConstraintConjunction<ELEM> sccEl = mContainsConstraints.get(elem);
			if (sccEl != null) {
				result.addAll(sccEl.getSetConstraints());
			}
		}




		if (result.isEmpty()) {
			// could not find any elements for the set constraint
			return null;
		}

		return result;
	}

	/**
	 * Get the constraints that this CCLiteralSetConstraints instance puts on constrainedElem, relative to the
	 * equivalence relation in newCc.
	 *
	 * E.g. if this contains a set constraint x in {a , b}, and splitInfo contains a -> {c, d}, then we replace that set
	 * constraint by x in {c, b} /\ x in {d, b}.
	 *
	 *
	 * [old (wrt. that getConstraint takes into account equalities):
	 * (e.g. mCongruenceClosure = {!x, y, z,a}, newCc = {x, !y, z}, {!a}, constrainedElem = x, (representatives are
	 *  marked with "!"), then the result should be "x in {y} /\ x in {a}")
	 *  ]
	 *
	 * @param constrainedElem
	 * @param ccWithFinerPartition TODO remove this param?
	 * @return
	 */
	private Set<SetConstraint<ELEM>> getConstraintWrtSplit(final ELEM constrainedElem,
			final CongruenceClosure<ELEM> ccWithFinerPartition, final HashRelation<ELEM, ELEM> splitInfo) {
		if (!mCongruenceClosure.hasElement(constrainedElem)) {
			return null;
		}

		final Set<SetConstraint<ELEM>> oldConstraint = getConstraint(constrainedElem);
		if (oldConstraint == null) {
			return null;
		}

		// initialize to constraint relative to old Cc
		Set<SetConstraint<ELEM>> result = new HashSet<>(oldConstraint);

		for (final ELEM oldRep : splitInfo.getDomain()) {
			assert !mCongruenceClosure.hasElement(oldRep)|| mCongruenceClosure.isRepresentative(oldRep);
			final Set<SetConstraint<ELEM>> newResult = new HashSet<>();

			for (final SetConstraint<ELEM> sc : result) {
				/* add a constraint for each newRep corresponding to oldRep, where oldRep has been replaced with that
				 * newRep */
				for (final ELEM newRep : splitInfo.getImage(oldRep)) {
					assert ccWithFinerPartition.isRepresentative(newRep);
					newResult.add(mSetConstraintManager.transformElements(sc, e -> e.equals(oldRep) ? newRep : e));
				}
			}

			result = newResult;
		}

		return result;
	}

	public void setCongruenceClosure(final CongruenceClosure<ELEM> congruenceClosure) {
		assert mCongruenceClosure == null : "never re-set the congruence closure!";
		mCongruenceClosure = congruenceClosure;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();

		sb.append("CCLiteralSetConstraints:\n");

		for (final Entry<ELEM, SetConstraintConjunction<ELEM>> en : getConstraints().entrySet()) {
			sb.append(en.getValue());
			sb.append("\n");
		}

		return sb.toString();
	}

	public void projectAway(final ELEM elem) {
		// EDIT: makes no sense: this is called during removal, when elem may already have been removed from mCc
//		if (!mCongruenceClosure.hasElement(elem)) {
//			// element not present, do nothing
//			return;
//		}
//		assert mCongruenceClosure.isRepresentative(elem) : "right?..";

		// remove constraints of the form "elem in S"
		 mContainsConstraints.remove(elem);

		 /*
		  * remove constraints that have elem on their right hand side
		  * (a more precise alternative would be to introduce a dummy element, effectively an existentially quantified
		  *  variable.. but we would have to introduce one for every projected element, right?..)
		  */
		 for (final Entry<ELEM, SetConstraintConjunction<ELEM>> en : new HashSet<>(mContainsConstraints.entrySet())) {
			 en.getValue().projectAway(elem);

			 // clean up constraints that became tautological
			 if (en.getValue().isTautological()) {
				 mContainsConstraints.remove(en.getKey());
			 }
		 }
	}

	public void replaceRepresentative(final ELEM oldRep, final ELEM newRep) {
		// replace elem in constraints of the form "elem in S"
		final SetConstraintConjunction<ELEM> constraints = mContainsConstraints.remove(oldRep);
		if (constraints != null && newRep != null) {
			putContainsConstraint(newRep, constraints);
		}
		// replace elem in any right hand side set of a constraint
		for (final Entry<ELEM, SetConstraintConjunction<ELEM>> en : new HashSet<>(mContainsConstraints.entrySet())) {
			final Set<SetConstraint<ELEM>> oldSc = en.getValue().getSetConstraints();
			final Set<SetConstraint<ELEM>> newSc =
					mSetConstraintManager.updateOnChangedRepresentative(oldSc, oldRep, newRep);

			assert mSetConstraintManager.getSingletonValues(newSc).isEmpty();
			final SetConstraintConjunction<ELEM> updated = newSc == oldSc ? en.getValue() :
					mCcManager.buildSetConstraintConjunction(this, en.getKey(), newSc);
			putContainsConstraint(en.getKey(), updated);
		}
	}

	public SetConstraintConjunction<ELEM> putContainsConstraint(final ELEM newRep,
			final SetConstraintConjunction<ELEM> constraints) {
		assert constraints.mSurroundingCCSetConstraints == this;
		return mContainsConstraints.put(newRep, constraints);
	}

	public void reportDisequality(final ELEM elem1, final ELEM elem2) {

		final ELEM elem1Rep = mCongruenceClosure.getRepresentativeElement(elem1);
		final ELEM elem2Rep = mCongruenceClosure.getRepresentativeElement(elem2);

		assert !elem1Rep.isLiteral() || !elem2Rep.isLiteral() : "literal disequalities should be implicit and not "
				+ "reported";

		// rule: e in L /\ e != l --> e in L\{l}
		{
			final Set<SetConstraint<ELEM>> elem2Constraint = getConstraint(elem2Rep);//mContainsConstraints.get(elem2Rep);
			if (elem2Constraint != null) {
				final Set<SetConstraint<ELEM>> elem2ConstraintFiltered =
						mSetConstraintManager.filterWithDisequality(elem2Constraint, elem1Rep);

				if (elem2ConstraintFiltered != elem2Constraint) {
					// made changes

					assert mSetConstraintManager.getSingletonValues(elem2ConstraintFiltered).isEmpty();
					final SetConstraintConjunction<ELEM> newConstraint =
							mCcManager.buildSetConstraintConjunction(this, elem2Rep, elem2ConstraintFiltered);
					// rule: e in {} --> \bot
					if (newConstraint.isInconsistent()) {
						reportInconsistency();
					}

					putContainsConstraint(elem2Rep, newConstraint);
				} else {
					// made no changes
				}
			}
		}
		// rule: e in L /\ e != l --> e in L\{l}
		{
			final Set<SetConstraint<ELEM>> elem1Constraint = getConstraint(elem1Rep);
			if (elem1Constraint != null) {
				final Set<SetConstraint<ELEM>> elem1ConstraintFiltered =
						mSetConstraintManager.filterWithDisequality(elem1Constraint, elem2Rep);

				if (elem1ConstraintFiltered != elem1Constraint) {
					// made changes

					final SetConstraintConjunction<ELEM> newConstraint =
							mCcManager.buildSetConstraintConjunction(this, elem1Rep, elem1ConstraintFiltered);
					// rule: e in {} --> \bot
					if (newConstraint.isInconsistent()) {
						reportInconsistency();
					}

					putContainsConstraint(elem1Rep, newConstraint);
				} else {
					// made no changes
				}
			}
		}
	}

	/**
	 *
	 * @param constraintsToKeepReps
	 * @return
	 * 		CCliteralSetconstraints where all constraints constrain an element in the given set. CongrunceClosure field
	 *   is left at null.
	 */
	public CCLiteralSetConstraints<ELEM> filterAndKeepOnlyConstraintsThatIntersectWith(
			final Set<ELEM> constraintsToKeepReps) {
		assert !isInconsistent() : "handle this case";


		final CCLiteralSetConstraints<ELEM> result =
				new CCLiteralSetConstraints<>(mCcManager, null);

		for (final Entry<ELEM, SetConstraintConjunction<ELEM>> en : mContainsConstraints.entrySet()) {
			if (constraintsToKeepReps.contains(en.getKey())) {
				result.putContainsConstraint(en.getKey(), new SetConstraintConjunction<>(result, en.getValue()));
			}
			if (DataStructureUtils.haveNonEmptyIntersection(constraintsToKeepReps, en.getValue().getAllRhsElements())) {
				result.putContainsConstraint(en.getKey(), new SetConstraintConjunction<>(result, en.getValue()));
			}
		}
		assert !result.isInconsistent();
		return result;
	}

	public void transformElements(final Function<ELEM, ELEM> elemTransformer) {
		final Map<ELEM, SetConstraintConjunction<ELEM>> copy = new HashMap<>(mContainsConstraints);
		for (final Entry<ELEM, SetConstraintConjunction<ELEM>> en : copy.entrySet()) {

			mContainsConstraints.remove(en.getKey());

			final ELEM keyTransformed = elemTransformer.apply(en.getKey());

			final Set<SetConstraint<ELEM>> valueTransformedSet =
					mSetConstraintManager.transformElements(en.getValue().getSetConstraints(), elemTransformer);

			assert mSetConstraintManager.getSingletonValues(valueTransformedSet).isEmpty();
			final SetConstraintConjunction<ELEM> valueTransformed =
					 mCcManager.buildSetConstraintConjunction(this, keyTransformed, valueTransformedSet);

			putContainsConstraint(keyTransformed, valueTransformed);
		}
	}

	public CongruenceClosure<ELEM> getCongruenceClosure() {
		return mCongruenceClosure;
	}

	public HashRelation<ELEM, ELEM> getElemToExpansion() {
		final HashRelation<ELEM, ELEM> result = new HashRelation<>();

		for (final Entry<ELEM, SetConstraintConjunction<ELEM>> en : mContainsConstraints.entrySet()) {
			if (en.getValue().hasOnlyLiterals()) {
				result.addAllPairs(en.getKey(), en.getValue().getLiterals());
			}
		}

		return result;
	}

	/**
	 *
	 * @return true iff this is not inconsistent and no literal constraints are stored explicitly (note that if
	 *  mCongruenceClosure has equalities there are non-tautological literal constraints which are not stored
	 *  explicitly)
	 */
	public boolean isEmpty() {
		if (isInconsistent()) {
			return false;
		}
		return mContainsConstraints.isEmpty();
	}

	public Set<ELEM> getRelatedElements(final ELEM rep) {
		assert mCongruenceClosure.isRepresentative(rep);
		final Set<ELEM> result = new HashSet<>();
		{
			final Set<SetConstraint<ELEM>> c = getConstraint(rep);
			if (c != null) {
				c.forEach(sc -> sc.getElementSet().forEach(result::add));
			}
		}
		for (final Entry<ELEM, SetConstraintConjunction<ELEM>> en : getConstraints().entrySet()) {
			if (en.getKey().equals(rep)) {
				en.getValue().getAllRhsElements().forEach(result::add);
			} else {
				if (en.getValue().getAllRhsElements().contains(rep)) {
					en.getValue().getAllRhsElements().forEach(result::add);
					result.add(en.getKey());
				}
			}
		}
		result.remove(rep);
		return result;
	}

	/**
	 * method for queries from the outside
	 * @param elem
	 * @return
	 */
//	public SetConstraintConjunction<ELEM> getContainsConstraint(final ELEM elem) {
	public Set<SetConstraint<ELEM>> getContainsConstraint(final ELEM elem) {
		return getConstraint(elem);
//		final ELEM rep = mCongruenceClosure.getRepresentativeElement(elem);
//		return mContainsConstraints.get(rep);
	}

	public boolean isConstrained(final ELEM elem) {
		if (elem != mCongruenceClosure.getRepresentativeElement(elem)) {
			throw new AssertionError("this is only called when elem is "
				+ "unconstrained on mCongruenceClosure.mElementTVER, right?");
		}
		return mContainsConstraints.get(elem) != null;
	}

	public Set<ELEM> getAllElementsMentionedInASetConstraint() {
		final Set<ELEM> result = new HashSet<>();
		for (final Entry<ELEM, SetConstraintConjunction<ELEM>> en : mContainsConstraints.entrySet()) {
			result.add(en.getValue().getConstrainedElement());
			result.addAll(en.getValue().getAllRhsElements());
		}
		return result;
	}
}
