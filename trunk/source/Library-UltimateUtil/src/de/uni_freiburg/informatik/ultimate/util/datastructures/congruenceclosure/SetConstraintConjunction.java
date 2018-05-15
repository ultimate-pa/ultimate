package de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure;

import java.util.HashSet;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.util.datastructures.EqualityStatus;

/**
 * Represents a conjunction over single set constraints that all constrain the same element.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <ELEM>
 */
public class SetConstraintConjunction<ELEM extends ICongruenceClosureElement<ELEM>> {

	private final ELEM mConstrainedElement;

	Set<SetConstraint<ELEM>> mSetConstraints;

	CCLiteralSetConstraints<ELEM> mSurroundingCCSetConstraints;

	public SetConstraintConjunction(final CCLiteralSetConstraints<ELEM> surroundingSetConstraints,
			final ELEM constrainedElement,
			final Set<ELEM> elements) {
		mConstrainedElement = constrainedElement;

	}

	/**
	 * copy constructor
	 *
	 * @param original
	 */
	public SetConstraintConjunction(final SetConstraintConjunction<ELEM> original) {
		mConstrainedElement = original.mConstrainedElement;
	}

	public void projectAway(final ELEM elem) {
		assert mSurroundingCCSetConstraints.getCongruenceClosure().isRepresentative(elem) : "right?..";
		// TODO Auto-generated method stub

	}

	/**
	 * Propagate according to the disequality "mConstrainedElement != elem".
	 *
	 * rule: e in L /\ e != l --> e in L\{l}
	 *
	 * @param elem1Rep
	 */
	public void filterWithDisequality(final ELEM elem) {
		// TODO Auto-generated method stub

	}

	public ELEM getSingletonValue() {
		// TODO Auto-generated method stub
		return null;
	}

	public boolean isSingleton() {
		// TODO Auto-generated method stub
		return false;
	}

	public boolean isInconsistent() {
		// TODO Auto-generated method stub
		return false;
	}

	public CongruenceClosure<ELEM> getCongruenceClosure() {
		// TODO Auto-generated method stub
		return null;
	}

	public ELEM getConstrainedElement() {
		return mConstrainedElement;
	}

	/**
	 * Apply propagation rule
	 *  e in L /\ e != l --> e in L\{l}
	 */
	public void filterWithDisequalities(final CongruenceClosure<ELEM> congruenceClosure) {
		for (final SetConstraint<ELEM> setConstraint : mSetConstraints) {
			setConstraint.filterWithDisequalities();
		}
	}

	public void updateOnChangedRepresentative(final ELEM oldRep, final ELEM newRep) {

	}

	public void updateOnChangedRepresentative(final ELEM elem1OldRep, final ELEM elem2OldRep, final ELEM newRep) {
		// TODO Auto-generated method stub

	}

	public static <ELEM extends ICongruenceClosureElement<ELEM>> SetConstraintConjunction<ELEM> transformElements(
			final SetConstraintConjunction<ELEM> value,
			final Function<ELEM, ELEM> elemTransformer) {
		// TODO Auto-generated method stub
		return null;
	}

	public static <ELEM extends ICongruenceClosureElement<ELEM>> SetConstraintConjunction<ELEM> meet(
			final SetConstraintConjunction<ELEM> elem1LiteralSet,
			final SetConstraintConjunction<ELEM> elem2LiteralSet) {
		// TODO Auto-generated method stub
		return null;
	}

	public static <ELEM extends ICongruenceClosureElement<ELEM>> boolean meetIsInconsistent(
			final SetConstraintConjunction<ELEM> litConstraint1,
			final SetConstraintConjunction<ELEM> litConstraint2) {
		// TODO Auto-generated method stub
		return false;
	}

	public static <ELEM extends ICongruenceClosureElement<ELEM>> boolean isStrongerThan(
			final SetConstraintConjunction<ELEM> firstConstraint,
			final SetConstraintConjunction<ELEM> secondConstraint) {
		// TODO Auto-generated method stub
		return false;
	}

	public static <ELEM extends ICongruenceClosureElement<ELEM>> SetConstraintConjunction<ELEM> join(
			final SetConstraintConjunction<ELEM> thisConstraint,
			final SetConstraintConjunction<ELEM> otherConstraint) {
		// TODO Auto-generated method stub
		return null;
	}

	public boolean sanityCheck() {
		for (final SetConstraint<ELEM> conjunct : mSetConstraints) {
			if (!conjunct.sanityCheck()) {
				assert false;
				return false;
			}
		}

		if (mSurroundingCCSetConstraints.getConstraint(mConstrainedElement) != this) {
				assert false;
				return false;
		}

		return true;
	}

	/**
	 *
	 * Represents a conjunction over single set constraints of the form e in L cup N, where L is a set of literals and N is
	 * a set of non-literal elements.
	 *
	 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
	 *
	 * @param <ELEM>
	 */
	class SetConstraint<ELEM extends ICongruenceClosureElement<ELEM>> {

		/**
		 * the conjunction this constraint belongs to
		 */
		SetConstraintConjunction<ELEM> mScConjunction;

		Set<ELEM> mLiterals;
		Set<ELEM> mNonLiterals;

		/**
		 * Apply propagation rule
		 *  e in L /\ e != l --> e in L\{l}
		 */
		public void filterWithDisequalities() {

			final CongruenceClosure<ELEM> congruenceClosure = mScConjunction.getCongruenceClosure();
			final ELEM constrainedElement = mScConjunction.getConstrainedElement();


			final Set<ELEM> newLiterals = new HashSet<>(mLiterals);

			for (final ELEM lit : mLiterals) {
				/*
				 * rule: e in L /\ e != l --> e in L\{l}
				 */
				if (congruenceClosure.getEqualityStatus(constrainedElement, lit) == EqualityStatus.NOT_EQUAL) {
					newLiterals.remove(lit);
				}
			}
			mLiterals = newLiterals;

			final Set<ELEM> newNonLiterals = new HashSet<>(mNonLiterals);

			for (final ELEM lit : mNonLiterals) {
				/*
				 * rule: e in L /\ e != l --> e in L\{l}
				 */
				if (congruenceClosure.getEqualityStatus(constrainedElement, lit) == EqualityStatus.NOT_EQUAL) {
					newNonLiterals.remove(lit);
				}
			}
			mNonLiterals = newNonLiterals;
		}

		public boolean sanityCheck() {
			if (mLiterals.size() == 1 && mNonLiterals.isEmpty()) {
				// we leave constraints of the form l in {l} implicit
				assert false;
				return false;
			}
			if (!mLiterals.stream().allMatch(ELEM::isLiteral)) {
				assert false;
				return false;
			}

			if (mNonLiterals.stream().anyMatch(ELEM::isLiteral)) {
				assert false;
				return false;
			}

			return true;
		}
	}

	public Set<Set<ELEM>> getSets() {
		// TODO Auto-generated method stub
		return null;
	}
}