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

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.util.datastructures.ThreeValuedEquivalenceRelation;

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

	private CongruenceClosure<ELEM> mCongruenceClosure;

	private Map<ELEM, SetConstraintConjunction<ELEM>> mContainsConstraints;

	private boolean mIsInconsistent;

	public CCLiteralSetConstraints(final CcManager<ELEM> manager, final CongruenceClosure<ELEM> congruenceClosure) {
		mCcManager = manager;
		mCongruenceClosure = congruenceClosure;

		mContainsConstraints = new HashMap<>();
		mIsInconsistent = false;
	}

	private CCLiteralSetConstraints(final CcManager<ELEM> manager, final CongruenceClosure<ELEM> congruenceClosure,
			final Map<ELEM, SetConstraintConjunction<ELEM>> containsConstraints) {
		mCcManager = manager;
		mCongruenceClosure = congruenceClosure;

		mContainsConstraints = containsConstraints;
		mIsInconsistent = false;
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

		mContainsConstraints = new HashMap<>();
		// deep copy
		for (final Entry<ELEM, SetConstraintConjunction<ELEM>> en : litSetConstraints.getConstraints().entrySet()) {
			mContainsConstraints.put(en.getKey(), new SetConstraintConjunction<>(this, en.getValue()));
		}
		mIsInconsistent = false;
	}

	public void reportContains(final ELEM element, final SetConstraintConjunction<ELEM> constraint) {
		final ELEM elementRep = mCongruenceClosure.getRepresentativeElement(element);


		final SetConstraintConjunction<ELEM> oldConstraint = mContainsConstraints.get(elementRep);

		SetConstraintConjunction<ELEM> newConstraint;
		if (oldConstraint != null) {
			newConstraint = SetConstraintConjunction.meet(oldConstraint, constraint);
		} else {
			newConstraint = constraint;
		}

		updateContainsConstraintApplyPropagations(elementRep, newConstraint);
	}

	public void reportContains(final ELEM element, final Set<ELEM> elements) {

		if (isInconsistent()) {
			// nothing to do
			return;
		}


		mCcManager.addElement(mCongruenceClosure, element, true, false);
		mCcManager.addAllElements(mCongruenceClosure, elements, null, true);

		final ELEM elementRep = mCongruenceClosure.getRepresentativeElement(element);

		if (elementRep.isLiteral()) {
			// element is already equal to a literal (x ~ l), thus we implicitly have the constraint x in {l}
			if (elements.contains(elementRep)) {
				// the new constraint is weaker than the existing one, do nothing
				return;
			} else {
				// the new constraint and the existing one contradict
				reportInconsistency();
				return;
			}
		}

		final SetConstraintConjunction<ELEM> additionalConstraint =
				mCcManager.buildSetConstraintConjunction(this, elementRep, elements);

		reportContains(elementRep, additionalConstraint);
	}

	private void updateContainsConstraintApplyPropagations(final ELEM elemRep,
			final SetConstraintConjunction<ELEM> newConstraint) {
		assert !mContainsConstraints.containsKey(elemRep) : "assuming this has been removed before";


		newConstraint.filterWithDisequalities(mCongruenceClosure);

		/*
		 * rule: e in {} --> \bot
		 */
		if (newConstraint.isInconsistent()) {
			reportInconsistency();
			return;
		}

		if (newConstraint.isSingleton()) {
			/*
			 * rule: e in {l} --> e ~ l
			 * (containsConstraint is implicit in this case)
			 */
			mCcManager.reportEquality(elemRep, newConstraint.getSingletonValue(), mCongruenceClosure, true);
		} else {
			/*
			 * rule: e in L /\ l in L' --> e in intersect(L, L')
			 */
			mContainsConstraints.put(elemRep, newConstraint);
		}

		// variable/literal expansion rule
		if (newConstraint.hasOnlyLiterals()) {
			for (final Entry<ELEM, SetConstraintConjunction<ELEM>> en : mContainsConstraints.entrySet()) {
				en.getValue().expandVariableToLiterals(elemRep, newConstraint.getLiterals());
			}
		}

		// filter after expand
		newConstraint.mSetConstraints = mCcManager.normalizeSetConstraintConjunction(newConstraint.mSetConstraints);

		assert CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_3 || sanityCheck();
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
	 */
	public void reportEquality(final ELEM elem1OldRep, final ELEM elem2OldRep, final ELEM newRep) {
		assert mCongruenceClosure.getRepresentativeElement(elem1OldRep) == newRep;
		assert mCongruenceClosure.getRepresentativeElement(elem2OldRep) == newRep;

		if (isInconsistent()) {
			// nothing to do
			return;
		}

		final SetConstraintConjunction<ELEM> elem1LiteralSet = mContainsConstraints.remove(elem1OldRep);
		final SetConstraintConjunction<ELEM> elem2LiteralSet = mContainsConstraints.remove(elem2OldRep);

		if (elem1LiteralSet != null) {
			elem1LiteralSet.updateOnChangedRepresentative(elem1OldRep, elem2OldRep, newRep);
		}
		if (elem2LiteralSet != null) {
			elem2LiteralSet.updateOnChangedRepresentative(elem1OldRep, elem2OldRep, newRep);
		}

		SetConstraintConjunction<ELEM> newConstraint = null;
		if (elem1LiteralSet != null && elem2LiteralSet != null)  {
			newConstraint = SetConstraintConjunction.meet(elem1LiteralSet, elem2LiteralSet);
		} else if (elem1LiteralSet != null) {
			newConstraint = elem1LiteralSet;
		} else if (elem2LiteralSet != null) {
			newConstraint = elem2LiteralSet;
		} else {
			// no contains-constraints on either element present --> nothing to do
			assert CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_3 || sanityCheck();
		}

		// update the other set constraints according to the change in representatives
		for (final Entry<ELEM, SetConstraintConjunction<ELEM>> en : mContainsConstraints.entrySet()) {
			en.getValue().updateOnChangedRepresentative(elem1OldRep, elem2OldRep, newRep);
		}

		if (newConstraint != null) {
			updateContainsConstraintApplyPropagations(newRep, newConstraint);
		}
	}

	public CCLiteralSetConstraints<ELEM> join(final CCLiteralSetConstraints<ELEM> other,
			final ThreeValuedEquivalenceRelation<ELEM> newTVER) {
		if (this.isInconsistent()) {
			return other;
		}
		if (other.isInconsistent()) {
			return this;
		}

		final Map<ELEM, SetConstraintConjunction<ELEM>> newContainsConstraints = new HashMap<>();

		for (final ELEM rep : newTVER.getAllRepresentatives()) {
			final SetConstraintConjunction<ELEM> thisConstraint = this.getConstraint(rep);
			final SetConstraintConjunction<ELEM> otherConstraint = other.getConstraint(rep);

			SetConstraintConjunction<ELEM> newConstraint;
			if (thisConstraint != null && otherConstraint != null) {
//				union = DataStructureUtils.union(thisConstraint, otherConstraint);
				newConstraint = SetConstraintConjunction.join(thisConstraint, otherConstraint);
//			} else if (thisConstraint != null) {
//				union = thisConstraint;
//			} else if (otherConstraint != null) {
//				union = otherConstraint;
			} else {
				// at least one side has no constraint on rep
				continue;
			}

			if (newConstraint.isSingleton()) {
//				assert newConstraint.iterator().next().equals(rep);
				assert newConstraint.getSingletonValue().equals(rep);
				// we leave constraints of the form l in {l} implicit
				// (this information is kept as an equality in CongruenceClosure)
				// do nothing
			} else {
				newContainsConstraints.put(rep, newConstraint);
			}

		}

		return new CCLiteralSetConstraints<>(mCcManager, null, newContainsConstraints);
	}

	public static <ELEM extends ICongruenceClosureElement<ELEM>> boolean isStrongerThan(
			final CCLiteralSetConstraints<ELEM> first,
			final CCLiteralSetConstraints<ELEM> second) {

		final Set<ELEM> constrainedElements = new HashSet<>();
		constrainedElements.addAll(first.mContainsConstraints.keySet());
		constrainedElements.addAll(second.mContainsConstraints.keySet());

		for (final ELEM elem : constrainedElements) {

			final SetConstraintConjunction<ELEM> firstConstraint = first.getConstraint(elem);
			final SetConstraintConjunction<ELEM> secondConstraint = second.getConstraint(elem);

			if (!SetConstraintConjunction.isStrongerThan(firstConstraint, secondConstraint)) {
				return false;
			}
		}
		return true;
	}

	public boolean isInconsistent() {
		return mIsInconsistent;
	}

	boolean sanityCheck() {
		/*
		 * <li> we only store representatives in our set of constraints, i.e., for each explicitly stored constraint
		 *  "e in L", e must be a representative in mCongruenceClosure.
		 * <li> we leave the constraints of the form "l in {l}" implicit.
		 */
		for (final ELEM el : mContainsConstraints.keySet()) {
			if (!mCongruenceClosure.isRepresentative(el)) {
				assert false;
				return false;
			}
			if (el.isLiteral()) {
				assert false;
				return false;
			}
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
	 * Return the constraint of the form elem in L that mCongrunenceClosure puts on elem.
	 * If elem is equal to something, return a singleton.
	 * If there is a set constraint, return the set.
	 * Otherwise return null (for "unconstrained")
	 *
	 * @param elem
	 * @return
	 */
	SetConstraintConjunction<ELEM> getConstraint(final ELEM elem) {
		if (!mCongruenceClosure.hasElement(elem)) {
			return null;
		}

		final ELEM rep = mCongruenceClosure.getRepresentativeElement(elem);

		if (rep.isLiteral()) {
			return new SingletonSetConstraintConjunction<>(this, rep, rep);
		}

		return mContainsConstraints.get(rep);
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
//			sb.append(en.getKey() + " in " + en.getValue());
			sb.append(en.getValue());
			sb.append("\n");
		}

		return sb.toString();
	}

	public boolean isTautological() {
		if (isInconsistent()) {
			return false;
		}
		return mContainsConstraints.isEmpty();
	}

	public void projectAway(final ELEM elem) {
		assert mCongruenceClosure.isRepresentative(elem) : "right?..";

		// remove constraints of the form "elem in S"
		 mContainsConstraints.remove(elem);

		 /*
		  * remove constraints that have elem on their right hand side
		  * (a more precise alternative would be to introduce a dummy element, effectively an existentially quantified
		  *  variable.. but we would have to introduce one for every projected element, right?..)
		  */
//		 for (final Entry<ELEM, Set<ELEM>> en : new HashSet<>(mContainsConstraints.entrySet())) {
		 for (final Entry<ELEM, SetConstraintConjunction<ELEM>> en : mContainsConstraints.entrySet()) {
			 en.getValue().projectAway(elem);
//			 if (en.getValue().contains(elem)) {
//				 mContainsConstraints.remove(en.getKey());
//			 }
		 }
	}

	public void replaceRepresentative(final ELEM oldRep, final ELEM newRep) {
		// replace elem in constraints of the form "elem in S"
		final SetConstraintConjunction<ELEM> constraints = mContainsConstraints.remove(oldRep);
		if (constraints != null && newRep != null) {
			mContainsConstraints.put(newRep, constraints);
		}
		// replace elem in any right hand side set of a constraint
		 for (final Entry<ELEM, SetConstraintConjunction<ELEM>> en : mContainsConstraints.entrySet()) {
			 en.getValue().updateOnChangedRepresentative(oldRep, newRep);
//			 if (!(en.getValue().remove(elem))) {
//				 // elem was not in the set, nothing to replace
//				 continue;
//			 }
//			 if (newRep.isLiteral() && en.getValue().isEmpty()) {
//				 /*
//				  * we leave constraints of the form e in {l} implicit
//				  * (note: a constraint e in l can not occur because l is always the representative of its equivalence
//				  *  class)
//				  */
//				 assert en.getKey().equals(newRep);
//				 continue;
//			 }
//			 en.getValue().add(newRep);
		 }
	}

	public void reportDisequality(final ELEM elem1, final ELEM elem2) {

		final ELEM elem1Rep = mCongruenceClosure.getRepresentativeElement(elem1);
		final ELEM elem2Rep = mCongruenceClosure.getRepresentativeElement(elem2);

		assert !elem1Rep.isLiteral() || !elem2Rep.isLiteral() : "literal disequalities should be implicit and not "
				+ "reported";

		// rule: e in L /\ e != l --> e in L\{l}
//		if (elem1Rep.isLiteral()) {
		{
			final SetConstraintConjunction<ELEM> elem2Constraint = mContainsConstraints.get(elem2Rep);
			if (elem2Constraint != null) {
				elem2Constraint.filterWithDisequality(elem1Rep);
//				literalSet.remove(elem1Rep);
				// rule: e in {} --> \bot
				if (elem2Constraint.isInconsistent()) {
					reportInconsistency();
				}
			}
		}
//		} else if (elem2Rep.isLiteral()) {
		{
			final SetConstraintConjunction<ELEM> elem1Constraint = mContainsConstraints.get(elem1Rep);
			if (elem1Constraint != null) {
				elem1Constraint.filterWithDisequality(elem2Rep);
//				literalSet.remove(elem2Rep);
				// rule: e in {} --> \bot
				if (elem1Constraint.isInconsistent()) {
					reportInconsistency();
				}
			}
		}
//		}
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

		final Map<ELEM, SetConstraintConjunction<ELEM>> newContainsConstraints = new HashMap<>();
		for (final Entry<ELEM, SetConstraintConjunction<ELEM>> en : mContainsConstraints.entrySet()) {
			if (constraintsToKeepReps.contains(en.getKey())) {
//				newContainsConstraints.put(en.getKey(), new HashSet<>(en.getValue()));
				newContainsConstraints.put(en.getKey(), new SetConstraintConjunction<>(this, en.getValue()));
			}
		}
		return new CCLiteralSetConstraints<>(mCcManager, null, newContainsConstraints);
	}

	public void transformElements(final Function<ELEM, ELEM> elemTransformer) {
		final Map<ELEM, SetConstraintConjunction<ELEM>> copy = new HashMap<>(mContainsConstraints);
		for (final Entry<ELEM, SetConstraintConjunction<ELEM>> en : copy.entrySet()) {

			mContainsConstraints.remove(en.getKey());

			final ELEM keyTransformed = elemTransformer.apply(en.getKey());

//			final SetConstraintConjunction<ELEM> valueTransformed =
//					SetConstraintConjunction.transformElements(en.getValue(), elemTransformer);
			en.getValue().transformElements(elemTransformer);

//			final Set<ELEM> valueTransformed = new HashSet<>();
//			for (final ELEM el : en.getValue()) {
//				valueTransformed.add(elemTransformer.apply(el));
//			}

//			mContainsConstraints.put(keyTransformed, valueTransformed);
			mContainsConstraints.put(keyTransformed, en.getValue());

		}
	}

	public CongruenceClosure<ELEM> getCongruenceClosure() {
		return mCongruenceClosure;
	}
}
