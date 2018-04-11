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

import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.EqualityStatus;
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

	private Map<ELEM, Set<ELEM>> mContainsConstraints;

	private boolean mIsInconsistent;

	public CCLiteralSetConstraints(final CcManager<ELEM> manager, final CongruenceClosure<ELEM> congruenceClosure) {
		mCcManager = manager;
		mCongruenceClosure = congruenceClosure;

		mContainsConstraints = new HashMap<>();
		mIsInconsistent = false;
	}

	private CCLiteralSetConstraints(final CcManager<ELEM> manager, final CongruenceClosure<ELEM> congruenceClosure,
			final Map<ELEM, Set<ELEM>> containsConstraints) {
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
		for (final Entry<ELEM, Set<ELEM>> en : litSetConstraints.getConstraints().entrySet()) {
			mContainsConstraints.put(en.getKey(), new HashSet<>(en.getValue()));
		}
		mIsInconsistent = false;
	}


	public void reportContains(final ELEM element, final Set<ELEM> literalSet) {

		if (isInconsistent()) {
			// nothing to do
			return;
		}

		final ELEM elementRep = mCongruenceClosure.getRepresentativeElement(element);

		if (elementRep.isLiteral()) {
			// element is already equal to a literal (x ~ l), thus we implicitly have the constraint x in {l}
			if (literalSet.contains(elementRep)) {
				// the new constraint is weaker than the existing one, do nothing
				return;
			} else {
				// the new constraint and the existing one contradict
				reportInconsistency();
				return;
			}
		}

		assert literalSet.stream().allMatch(ELEM::isLiteral);

		mCcManager.addElement(mCongruenceClosure, elementRep, true, false);
		mCcManager.addAllElements(mCongruenceClosure, literalSet, null, true);

		final Set<ELEM> oldSet = mContainsConstraints.get(elementRep);

		final Set<ELEM> intersection;
		if (oldSet != null) {
			intersection = DataStructureUtils.intersection(oldSet, literalSet);
		} else {
			intersection = literalSet;
		}

		final Set<ELEM> newLiteralSet = new HashSet<>(intersection);
		for (final ELEM lit : intersection) {
			/*
			 * rule: e in L /\ e != l --> e in L\{l}
			 */
			if (mCongruenceClosure.getEqualityStatus(elementRep, lit) == EqualityStatus.NOT_EQUAL) {
				newLiteralSet.remove(lit);
			}
		}

		/*
		 * rule: e in {} --> \bot
		 */
		if (newLiteralSet.isEmpty()) {
			reportInconsistency();
			return;
		}

		if (newLiteralSet.size() == 1) {
			/*
			 * rule: e in {l} --> e ~ l
			 * (containsConstraint is implicit in this case)
			 */
			mCcManager.reportEquality(elementRep, intersection.iterator().next(), mCongruenceClosure, true);
		} else {
			/*
			 * rule: e in L /\ l in L' --> e in intersect(L, L')
			 */
			mContainsConstraints.put(elementRep, intersection);
		}

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

		final Set<ELEM> elem1LiteralSet = mContainsConstraints.remove(elem1OldRep);
		final Set<ELEM> elem2LiteralSet = mContainsConstraints.remove(elem2OldRep);

		Set<ELEM> intersection = null;
		if (elem1LiteralSet != null && elem2LiteralSet != null)  {
			intersection = DataStructureUtils.intersection(elem1LiteralSet, elem2LiteralSet);
		} else if (elem1LiteralSet != null) {
			intersection = elem1LiteralSet;
		} else if (elem2LiteralSet != null) {
			intersection = elem2LiteralSet;
		} else {
			// no contains-constraints on either element present --> nothing to do
			assert CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_3 || sanityCheck();
			return;
		}

		// rule: e in {} --> \bot
		if (intersection.isEmpty()) {
			reportInconsistency();
			assert CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_3 || sanityCheck();
			return;
		}

		mContainsConstraints.put(newRep, intersection);
		assert CcSettings.OMIT_SANITYCHECK_FINE_GRAINED_3 || sanityCheck();
	}

	public CCLiteralSetConstraints<ELEM> join(final CCLiteralSetConstraints<ELEM> other,
			final ThreeValuedEquivalenceRelation<ELEM> newTVER) {
		if (this.isInconsistent()) {
			return other;
		}
		if (other.isInconsistent()) {
			return this;
		}

		final Map<ELEM, Set<ELEM>> newContainsConstraints = new HashMap<>();

		for (final ELEM rep : newTVER.getAllRepresentatives()) {
			final Set<ELEM> thisConstraint = this.getConstraint(rep);
			final Set<ELEM> otherConstraint = other.getConstraint(rep);

			Set<ELEM> union;
			if (thisConstraint != null && otherConstraint != null) {
				union = DataStructureUtils.union(thisConstraint, otherConstraint);
//			} else if (thisConstraint != null) {
//				union = thisConstraint;
//			} else if (otherConstraint != null) {
//				union = otherConstraint;
			} else {
				// at least one side has not constraint on rep
				continue;
			}

			if (union.size() == 1) {
				assert union.iterator().next().equals(rep);
				// we leave constraints of the form l in {l} implicit
				// (this information is kept as an equality in CongruenceClosure)
				// do nothing
			} else {
				newContainsConstraints.put(rep, union);
			}

		}

		return new CCLiteralSetConstraints<>(mCcManager, null, newContainsConstraints);
	}

	public static <ELEM extends ICongruenceClosureElement<ELEM>> boolean isStrongerThan(
			final CCLiteralSetConstraints<ELEM> first,
			final CCLiteralSetConstraints<ELEM> second) {

		for (final Entry<ELEM, Set<ELEM>> en : first.getConstraints().entrySet()) {
			final ELEM firstElem = en.getKey();
			final Set<ELEM> secondConstraint = second.getConstraint(firstElem);
			if (secondConstraint == null) {
				// second has no constraint, inclusion holds, for firstElem
				continue;
			}
			final Set<ELEM> firstConstraint = en.getValue();
			if (firstConstraint == null) {
				// second has a constraint, first has not --> inclusion violated
				return false;
			}

			if (!secondConstraint.containsAll(firstConstraint)) {
				// second's constraint is not a superset --> inclusion violated
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
		for (final Set<ELEM> literalSet : mContainsConstraints.values()) {
			if (literalSet.size() == 1) {
				// we leave constraints of the form l in {l} implicit
				assert false;
				return false;
			}
			if (!literalSet.stream().allMatch(ELEM::isLiteral)) {
				assert false;
				return false;
			}
		}

		if (mCongruenceClosure.mLiteralSetConstraints != this) {
				assert false;
				return false;
		}

		return true;
	}

	public Map<ELEM, Set<ELEM>> getConstraints() {
		return Collections.unmodifiableMap(mContainsConstraints);
	}

	Set<ELEM> getConstraint(final ELEM elem) {
		if (!mCongruenceClosure.hasElement(elem)) {
			return null;
		}

		final ELEM rep = mCongruenceClosure.getRepresentativeElement(elem);

		if (rep.isLiteral()) {
			return Collections.singleton(rep);
		}

		final Set<ELEM> literalSet = mContainsConstraints.get(rep);

		if (literalSet == null) {
			return null;
		}
		return Collections.unmodifiableSet(literalSet);
	}

	public void setCongruenceClosure(final CongruenceClosure<ELEM> congruenceClosure) {
		assert mCongruenceClosure == null : "never re-set the congruence closure!";
		mCongruenceClosure = congruenceClosure;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();

		sb.append("CCLiteralSetConstraints:\n");

		for (final Entry<ELEM, Set<ELEM>> en : getConstraints().entrySet()) {
			sb.append(en.getKey() + " in " + en.getValue());
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

	public void removeConstraint(final ELEM elem) {
		// remove constraints of the form "elem in S"
		 mContainsConstraints.remove(elem);

		 /*
		  * remove constraints that have elem on their right hand side
		  * (a more precise alternative would be to introduce a dummy element, effectively an existentially quantified
		  *  variable.. but we would have to introduce one for every projected element, right?..)
		  */
		 for (final Entry<ELEM, Set<ELEM>> en : new HashSet<>(mContainsConstraints.entrySet())) {
			 if (en.getValue().contains(elem)) {
				 mContainsConstraints.remove(en.getKey());
			 }
		 }
	}

	public void replaceRepresentative(final ELEM elem, final ELEM newRep) {
		// replace elem in constraints of the form "elem in S"
		final Set<ELEM> literalSet = mContainsConstraints.remove(elem);
		if (literalSet != null && newRep != null) {
			mContainsConstraints.put(newRep, literalSet);
		}
		// replace elem in any right hand side set of a constraint
		 for (final Entry<ELEM, Set<ELEM>> en : mContainsConstraints.entrySet()) {
			 if (!(en.getValue().remove(elem))) {
				 // elem was not in the set, nothing to replace
				 continue;
			 }
			 if (newRep.isLiteral() && en.getValue().isEmpty()) {
				 /*
				  * we leave constraints of the form e in {l} implicit
				  * (note: a constraint e in l can not occur because l is always the representative of its equivalence
				  *  class)
				  */
				 assert en.getKey().equals(newRep);
				 continue;
			 }
			 en.getValue().add(newRep);
		 }
	}

	public void reportDisequality(final ELEM elem1, final ELEM elem2) {

		final ELEM elem1Rep = mCongruenceClosure.getRepresentativeElement(elem1);
		final ELEM elem2Rep = mCongruenceClosure.getRepresentativeElement(elem2);

		assert !elem1Rep.isLiteral() || !elem2Rep.isLiteral() : "literal disequalities should be implicit and not "
				+ "reported";

		// rule: e in L /\ e != l --> e in L\{l}
		if (elem1Rep.isLiteral()) {
			final Set<ELEM> literalSet = mContainsConstraints.get(elem2Rep);
			if (literalSet != null) {
				literalSet.remove(elem1Rep);
				// rule: e in {} --> \bot
				if (literalSet.isEmpty()) {
					reportInconsistency();
				}
			}
		} else if (elem2Rep.isLiteral()) {
			final Set<ELEM> literalSet = mContainsConstraints.get(elem1Rep);
			if (literalSet != null) {
				literalSet.remove(elem2Rep);
				// rule: e in {} --> \bot
				if (literalSet.isEmpty()) {
					reportInconsistency();
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

		final Map<ELEM, Set<ELEM>> newContainsConstraints = new HashMap<>();
		for (final Entry<ELEM, Set<ELEM>> en : mContainsConstraints.entrySet()) {
			if (constraintsToKeepReps.contains(en.getKey())) {
				newContainsConstraints.put(en.getKey(), new HashSet<>(en.getValue()));
			}
		}
		return new CCLiteralSetConstraints<>(mCcManager, null, newContainsConstraints);
	}

	public void transformElements(final Function<ELEM, ELEM> elemTransformer) {
		final Map<ELEM, Set<ELEM>> copy = new HashMap<>(mContainsConstraints);
		for (final Entry<ELEM, Set<ELEM>> en : copy.entrySet()) {

			mContainsConstraints.remove(en.getKey());

			final ELEM keyTransformed = elemTransformer.apply(en.getKey());

			final Set<ELEM> valueTransformed = new HashSet<>();
			for (final ELEM el : en.getValue()) {
				valueTransformed.add(elemTransformer.apply(el));
			}

			mContainsConstraints.put(keyTransformed, valueTransformed);

		}
	}
}
