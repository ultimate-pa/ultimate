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

	private CongruenceClosure<ELEM> mCongruenceClosure;

	private Map<ELEM, SetConstraintConjunction<ELEM>> mContainsConstraints;

	private boolean mIsInconsistent;

	public CCLiteralSetConstraints(final CcManager<ELEM> manager, final CongruenceClosure<ELEM> congruenceClosure) {
		mCcManager = manager;
		mCongruenceClosure = congruenceClosure;

		mContainsConstraints = new HashMap<>();
		mIsInconsistent = false;
//		assert CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_3 || sanityCheck();
	}

	private CCLiteralSetConstraints(final CcManager<ELEM> manager, final CongruenceClosure<ELEM> congruenceClosure,
			final Map<ELEM, SetConstraintConjunction<ELEM>> containsConstraints) {
		mCcManager = manager;
		mCongruenceClosure = congruenceClosure;

		mContainsConstraints = containsConstraints;
		mIsInconsistent = false;
//		assert CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_3 || sanityCheck();
		assert containsConstraints.values().stream().allMatch(scc -> (scc.mSurroundingCCSetConstraints == this));
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
//		assert CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_3 || sanityCheck();
	}

//	public Pair<ELEM, ELEM> reportContains(final ELEM element, final SetConstraintConjunction<ELEM> constraint) {
	public HashRelation<ELEM, ELEM> reportContains(final ELEM element, final Set<SetConstraint<ELEM>> constraintRaw) {
//		assert constraint.mSurroundingCCSetConstraints == this ||
//				constraint.mSurroundingCCSetConstraints == null;
		assert CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_3 || sanityCheck();


		final ELEM elementRep = mCongruenceClosure.getRepresentativeElement(element);

		final Set<SetConstraint<ELEM>> constraintUpdRep =
				SetConstraintConjunction.updateOnChangedRepresentative(constraintRaw, mCongruenceClosure);


//		final SetConstraintConjunction<ELEM> oldConstraint = getConstraint(element);
		final Set<SetConstraint<ELEM>> oldConstraint = getConstraint(element);
		// just for analogy to reportEquality
		mContainsConstraints.remove(elementRep);

//		SetConstraintConjunction<ELEM> newConstraint;
		Set<SetConstraint<ELEM>> newConstraint;
		if (oldConstraint != null) {
//			newConstraint = SetConstraintConjunction.meet(this, elementRep, oldConstraint, constraint);
//			newConstraint = DataStructureUtils.union(oldConstraint.getSetConstraints(), constraint);
			newConstraint = DataStructureUtils.union(oldConstraint, constraintUpdRep);
		} else {
//			assert constraint.getConstrainedElement() == elementRep;
//			newConstraint = mCcManager.buildSetConstraintConjunction(this, elementRep, constraint.mSetConstraints);//new SetConstraintConjunction<>(this, constraint);
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

//		if (elementRep.isLiteral()) {
//			// element is already equal to a literal (x ~ l), thus we implicitly have the constraint x in {l}
//			if (elements.contains(elementRep)) {
//				// the new constraint is weaker than the existing one, do nothing
//				return;
//			} else {
//				// the new constraint and the existing one contradict
//				reportInconsistency();
//				return;
//			}
//		}

//		final SetConstraintConjunction<ELEM> additionalConstraint =
//				mCcManager.buildSetConstraintConjunction(this, elementRep, elements);

		return reportContains(elementRep, Collections.singleton(SetConstraint.buildSetConstraint(elements)));// additionalConstraint);
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
				SetConstraintConjunction.filterWithDisequalities(mCongruenceClosure, constrainedElemRep, newConstraint);

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
		for (final ELEM sv : SetConstraintConjunction.getSingletonValues(newConstraint1)) {
			if (!constrainedElemRep.equals(sv)) {
				result.addPair(constrainedElemRep, sv);
			}
		}


//		if (SetConstraintConjunction.hasSingletons(newConstraint1)) {
			/*
			 * rule: e in {l} --> e ~ l
			 * (containsConstraint is implicit in this case)
			 */
			// don't directly call reportEquality here, as we are in an intermediate state of
			// CongruenceClosure.reportEquality..!!


//			final ELEM singletonValue = SetConstraintConjunction.getSingletonValue(newConstraint1);
//			if (singletonValue != constrainedElemRep) {
////				result = new Pair<>(constrainedElemRep, singletonValue);
//			}
//		}


		final SetConstraintConjunction<ELEM> newConstraint2 =
				mCcManager.buildSetConstraintConjunction(this, constrainedElemRep, newConstraint1);

//		if (!newConstraint2.isTautological() && result == null) {
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
					SetConstraintConjunction.updateOnChangedRepresentative(elem1LiteralSet, elem1OldRep, elem2OldRep, newRep);
		}
		if (elem2LiteralSet != null) {
			elem2LiteralSet =
					SetConstraintConjunction.updateOnChangedRepresentative(elem2LiteralSet, elem1OldRep, elem2OldRep, newRep);
		}

		Set<SetConstraint<ELEM>> newConstraint = null;
		if (elem1LiteralSet != null && elem2LiteralSet != null)  {
			newConstraint =
					SetConstraintConjunction.meet(this, elem1LiteralSet, elem2LiteralSet);
		} else if (elem1LiteralSet != null) {
			newConstraint = elem1LiteralSet;
		} else if (elem2LiteralSet != null) {
			newConstraint = elem2LiteralSet;
		} else {
			// no contains-constraints on either element present --> nothing to do
		}

		// update the other set constraints according to the change in representatives
		for (final Entry<ELEM, SetConstraintConjunction<ELEM>> en : new HashSet<>(mContainsConstraints.entrySet())) {
//			en.getValue().updateOnChangedRepresentative(elem1OldRep, elem2OldRep, newRep);
			final Set<SetConstraint<ELEM>> oldSc = en.getValue().getSetConstraints();
			final Set<SetConstraint<ELEM>> newSc =
					SetConstraintConjunction.updateOnChangedRepresentative(oldSc, elem1OldRep, elem2OldRep, newRep);

			assert newSc == oldSc || SetConstraintConjunction.getSingletonValues(newSc).isEmpty();
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

//	private void removeConstraint(final ELEM elem1OldRep) {
//		mContainsConstraints.remove(mCongruenceClosure.getRepresentativeElement(elem1OldRep));
//	}

	public CCLiteralSetConstraints<ELEM> join(final CongruenceClosure<ELEM> newCc,
			final CCLiteralSetConstraints<ELEM> other) {
		if (this.isInconsistent()) {
			return other;
		}
		if (other.isInconsistent()) {
			return this;
		}
		// this is problematic: if we join x = 1 and x = 2, the literal set constraints are tautological..
//		if (this.isTautological() || other.isTautological()) {
//			return new CCLiteralSetConstraints<>(mCcManager, newCc);
//		}

		final CCLiteralSetConstraints<ELEM> newSetConstraints = new CCLiteralSetConstraints<>(mCcManager, newCc);

		final Map<ELEM, SetConstraintConjunction<ELEM>> newContainsConstraints = new HashMap<>();

		for (final ELEM constrainedElem : newCc.getAllElementRepresentatives()) {
			final Set<SetConstraint<ELEM>> thisConstraint = this.getConstraint(constrainedElem);
			final Set<SetConstraint<ELEM>> otherConstraint = other.getConstraint(constrainedElem);

			final Set<SetConstraint<ELEM>> thisUpdRep =
					SetConstraintConjunction.updateOnChangedRepresentative(thisConstraint, newCc);
			final Set<SetConstraint<ELEM>> otherUpdRep =
					SetConstraintConjunction.updateOnChangedRepresentative(otherConstraint, newCc);

			Set<SetConstraint<ELEM>> newConstraints;
			if (thisUpdRep != null && otherUpdRep != null) {
				newConstraints = SetConstraintConjunction.join(newSetConstraints, thisUpdRep, otherUpdRep);
			} else {
				// at least one side has no constraint on rep
				continue;
			}

			assert SetConstraintConjunction.getSingletonValues(newConstraints).stream()
			.filter(sv -> !sv.equals(constrainedElem)).collect(Collectors.toSet()).isEmpty() : "created "
					+ "non-tautological singleton set constraints --> report them, befor buildSetConstraintConj.."
					+ "throws them away!";
			final SetConstraintConjunction<ELEM> newConstraint =
					mCcManager.buildSetConstraintConjunction(newSetConstraints, constrainedElem, newConstraints);

			if (SetConstraintConjunction.isTautological(newConstraint)) {
				// tautological constraint --> nothing to add
//			} else if (newConstraint.isSingleton()) {
////				assert newConstraint.iterator().next().equals(rep);
//				assert newConstraint.getSingletonValue().equals(rep);
//				// we leave constraints of the form l in {l} implicit
//				// (this information is kept as an equality in CongruenceClosure)
//				// do nothing
			} else {
				newContainsConstraints.put(constrainedElem, newConstraint);
			}

		}

		newSetConstraints.setContainsConstraints(newContainsConstraints);

		return newSetConstraints;
//		return new CCLiteralSetConstraints<>(mCcManager, null, newContainsConstraints);
	}

	private void setContainsConstraints(final Map<ELEM, SetConstraintConjunction<ELEM>> newContainsConstraints) {
		mContainsConstraints = newContainsConstraints;
	}

	public static <ELEM extends ICongruenceClosureElement<ELEM>> boolean isStrongerThan(
			final CCLiteralSetConstraints<ELEM> first,
			final CCLiteralSetConstraints<ELEM> second) {

		final Set<ELEM> constrainedElements = new HashSet<>();
		constrainedElements.addAll(first.mContainsConstraints.keySet());
		constrainedElements.addAll(second.mContainsConstraints.keySet());

		for (final ELEM elem : constrainedElements) {

			final Set<SetConstraint<ELEM>> firstConstraint = first.getConstraint(elem);
			final Set<SetConstraint<ELEM>> secondConstraint = second.getConstraint(elem);

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
	 * Return the constraint of the form elem in L that mCongrunenceClosure puts on elem.
	 * If elem is equal to something, return a singleton.
	 * If there is a set constraint, return the set.
	 * Otherwise return null (for "unconstrained")
	 *
	 * @param elem
	 * @return
	 */
//	SetConstraintConjunction<ELEM> getConstraint(final ELEM elem) {
	Set<SetConstraint<ELEM>> getConstraint(final ELEM elem) {
		if (!mCongruenceClosure.hasElement(elem)) {
			return null;
		}


		final Set<SetConstraint<ELEM>> result = new HashSet<>();

		final ELEM rep = mCongruenceClosure.getRepresentativeElement(elem);

		// an equality x ~ y implies a set constraint x in {y}, which we simply conjoin with the rest
//		if (!rep.equals(elem)) {
			result.add(SetConstraint.buildSetConstraint(Collections.singleton(rep)));
//		}

//		if (rep.isLiteral()) {
//			return new SingletonSetConstraintConjunction<>(this, rep, rep);
//		}

//		return mContainsConstraints.get(rep).getSetConstraints();
		final SetConstraintConjunction<ELEM> scc = mContainsConstraints.get(rep);
		if (scc != null) {
			result.addAll(scc.getSetConstraints());
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
//			sb.append(en.getKey() + " in " + en.getValue());
			sb.append(en.getValue());
			sb.append("\n");
		}

		return sb.toString();
	}

//	public boolean isTautological() {
//		if (isInconsistent()) {
//			return false;
//		}
//		return mContainsConstraints.isEmpty();
//	}

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
//		 for (final Entry<ELEM, Set<ELEM>> en : new HashSet<>(mContainsConstraints.entrySet())) {
		 for (final Entry<ELEM, SetConstraintConjunction<ELEM>> en : new HashSet<>(mContainsConstraints.entrySet())) {
			 en.getValue().projectAway(elem);
//			 if (en.getValue().contains(elem)) {
//				 mContainsConstraints.remove(en.getKey());
//			 }
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
					SetConstraintConjunction.updateOnChangedRepresentative(oldSc, oldRep, newRep);

			assert SetConstraintConjunction.getSingletonValues(newSc).isEmpty();
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
						SetConstraintConjunction.filterWithDisequality(elem2Constraint, elem1Rep);

				if (elem2ConstraintFiltered != elem2Constraint) {
					// made changes

					assert SetConstraintConjunction.getSingletonValues(elem2ConstraintFiltered).isEmpty();
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
						SetConstraintConjunction.filterWithDisequality(elem1Constraint, elem2Rep);

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

//		final Map<ELEM, SetConstraintConjunction<ELEM>> newContainsConstraints = new HashMap<>();
		for (final Entry<ELEM, SetConstraintConjunction<ELEM>> en : mContainsConstraints.entrySet()) {
			if (constraintsToKeepReps.contains(en.getKey())) {
//				newContainsConstraints.put(en.getKey(), new HashSet<>(en.getValue()));
//				newContainsConstraints.put(en.getKey(), new SetConstraintConjunction<>(this, en.getValue()));
				result.putContainsConstraint(en.getKey(), new SetConstraintConjunction<>(result, en.getValue()));
			}
			if (DataStructureUtils.haveNonEmptyIntersection(constraintsToKeepReps, en.getValue().getAllRhsElements())) {
//				newContainsConstraints.put(en.getKey(), new SetConstraintConjunction<>(this, en.getValue()));
				result.putContainsConstraint(en.getKey(), new SetConstraintConjunction<>(result, en.getValue()));
			}
		}
//		final CCLiteralSetConstraints<ELEM> result =
//				new CCLiteralSetConstraints<>(mCcManager, null, newContainsConstraints);
		assert !result.isInconsistent();
		return result;
	}

	public void transformElements(final Function<ELEM, ELEM> elemTransformer) {
		final Map<ELEM, SetConstraintConjunction<ELEM>> copy = new HashMap<>(mContainsConstraints);
		for (final Entry<ELEM, SetConstraintConjunction<ELEM>> en : copy.entrySet()) {

			mContainsConstraints.remove(en.getKey());

			final ELEM keyTransformed = elemTransformer.apply(en.getKey());

			final Set<SetConstraint<ELEM>> valueTransformedSet =
					SetConstraintConjunction.transformElements(en.getValue().getSetConstraints(), elemTransformer);

			assert SetConstraintConjunction.getSingletonValues(valueTransformedSet).isEmpty();
			final SetConstraintConjunction<ELEM> valueTransformed =
					 mCcManager.buildSetConstraintConjunction(this, keyTransformed, valueTransformedSet);
//			en.getValue().transformElements(elemTransformer);

//			final Set<ELEM> valueTransformed = new HashSet<>();
//			for (final ELEM el : en.getValue()) {
//				valueTransformed.add(elemTransformer.apply(el));
//			}

			putContainsConstraint(keyTransformed, valueTransformed);
//			mContainsConstraints.put(keyTransformed, en.getValue());

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
}
