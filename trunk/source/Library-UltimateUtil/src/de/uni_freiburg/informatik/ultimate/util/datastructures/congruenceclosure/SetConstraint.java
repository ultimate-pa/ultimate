package de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure;

import java.util.Collections;
import java.util.Iterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 *
 * Represents a conjunction over single set constraints of the form e in L cup N, where L is a set of literals and N is
 * a set of non-literal elements.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <ELEM>
 */
public class SetConstraint<ELEM extends ICongruenceClosureElement<ELEM>> {

	/**
	 * the conjunction this constraint belongs to
	 */
//	private final SetConstraintConjunction<ELEM> mSurroundingScConjunction;

	private final Set<ELEM> mLiterals;
	private final Set<ELEM> mNonLiterals;

	/**
	 * sufficient condition, not necessary for being inconsistent
	 */
	private final boolean mIsInconsistent;


	protected SetConstraint(final boolean inconsistent) {
		assert inconsistent : "use other constructor for this case!";
//		mSurroundingScConjunction = null;
		mLiterals = null;
		mNonLiterals = null;
		mIsInconsistent = true;
//		assert sanityCheck();
	}

	public boolean isSingleton() {
		return getElementSet().size() == 1;
	}

	public ELEM getSingletonValue() {
		assert isSingleton();
		return getElementSet().iterator().next();
	}

	/**
	 * Construct a SetConstraint that has not yet been added to a SetConstraintConjunction.
	 *
	 * @param literals
	 * @param nonLiterals
	 */
	protected SetConstraint(//final SetConstraintConjunction<ELEM> surroundingSetCc,
			final Set<ELEM> literals,
			final Set<ELEM> nonLiterals) {
		assert literals.stream().allMatch(ELEM::isLiteral);
		assert !nonLiterals.stream().anyMatch(ELEM::isLiteral);

		mLiterals = Collections.unmodifiableSet(literals);
		mNonLiterals = Collections.unmodifiableSet(nonLiterals);

		mIsInconsistent = literals.isEmpty() && nonLiterals.isEmpty();
		assert !mIsInconsistent : "use other constructor, no?";
		assert sanityCheck();
	}

//	/**
//	 * copy constructor that may change surrounding set constraints
//	 *
//	 * @param surroundingSetCc
//	 * @param sc
//	 */
//	SetConstraint(final SetConstraintConjunction<ELEM> surroundingSetCc, final SetConstraint<ELEM> sc) {
//		mSurroundingScConjunction = surroundingSetCc;
//		mLiterals = new HashSet<>(sc.mLiterals);
//		mNonLiterals = new HashSet<>(sc.mNonLiterals);
//		mIsInconsistent = false;
//		assert sanityCheck();
//	}

	public Set<ELEM> getLiterals() {
//		assert hasOnlyLiterals();
		return Collections.unmodifiableSet(mLiterals);
	}

	/**
	 *
	 * @param elemRep
	 * @param literals
	 * @return true if made changes
	 */
	public boolean expandVariableToLiterals(final ELEM elemRep, final Set<ELEM> literals) {
		if (mNonLiterals.contains(elemRep)) {
			mNonLiterals.remove(elemRep);
			mLiterals.addAll(literals);
			return true;
		}
		return false;
	}

	public boolean hasOnlyLiterals() {
		return mNonLiterals.isEmpty();
	}

	public boolean isInconsistent() {
		return mIsInconsistent || (mLiterals.isEmpty() && mNonLiterals.isEmpty());
	}



	/**
	 * all elements on the right hand side of this constraint (literals and non-literals)
	 * @return
	 */
	public Set<ELEM> getElementSet() {
		return DataStructureUtils.union(mLiterals, mNonLiterals);
	}

//	public void filterWithDisequality(final ELEM elem) {
//		assert mSurroundingScConjunction.getCongruenceClosure().isRepresentative(elem);
//		mLiterals.remove(elem);
//		mNonLiterals.remove(elem);
//	}

	public boolean containsElement(final ELEM elem) {
		if (elem.isLiteral()) {
			return mLiterals != null && mLiterals.contains(elem);
		} else {
			return mNonLiterals != null && mNonLiterals.contains(elem);
		}
	}



	@Override
	public String toString() {
		return "SetConstraint " + mLiterals + " U " + mNonLiterals + "";
	}

	public boolean sanityCheck() {
		// all elements of mLiterals must be literals
		if (!mLiterals.stream().allMatch(ELEM::isLiteral)) {
			assert false;
			return false;
		}

		// all elements of mNonLiterals must not be literals
		if (mNonLiterals.stream().anyMatch(ELEM::isLiteral)) {
			assert false;
			return false;
		}

		// all elements must have the same sort
		{
			if (getElementSet().size() >= 2) {
				final Iterator<ELEM> it = getElementSet().iterator();
				ELEM currentOne = null;
				ELEM currentTwo = it.next();

				while (it.hasNext()) {
					currentOne = currentTwo;
					currentTwo = it.next();

					if (!currentOne.hasSameTypeAs(currentTwo)) {
						assert false;
						return false;
					}
				}
			}
		}
		return true;
	}

	public boolean sanityCheck(final SetConstraintConjunction<ELEM> surroundingScConjunction) {

		if (!sanityCheck()) {
			assert false;
			return false;
		}

		if (surroundingScConjunction == null) {
			// has not yet been added to a SetConstraintConjunction, omit the remaining checks
			return true;
		}

		if (surroundingScConjunction.mSurroundingCCSetConstraints == null) {
			// has not yet been added to a SetConstraintConjunction, omit the remaining checks
			return true;
		}

		final CongruenceClosure<ELEM> surrCc = surroundingScConjunction.getCongruenceClosure();

		if (surrCc == null) {
			// has not yet been added to a SetConstraintConjunction with a Cc, omit the remaining checks
			return true;
		}

		if (surrCc.mLiteralSetConstraints == null) {
			return true;
		}


		/*
		 * all elements that his constraint talks about must be known to the surrounding CongruenceClosure instance.
		 */
		if (!mLiterals.stream().allMatch(surrCc::hasElement)) {
			assert false;
			return false;
		}

		// all elements of mNonLiterals must be representatives
		if (mNonLiterals.stream().anyMatch(nl -> !surrCc.isRepresentative(nl))) {
			assert false;
			return false;
		}

		// all expandable elements of mNonLiterals must have been expanded
		for (final ELEM nl : mNonLiterals) {
			final Set<SetConstraint<ELEM>> contCons = surrCc.getContainsConstraintForElement(nl);
			if (contCons != null && SetConstraintConjunction.hasOnlyLiterals(contCons)) {
				assert false;
				return false;
			}
		}

		return true;
	}

	public static <ELEM extends ICongruenceClosureElement<ELEM>> boolean
			isTautological(final ELEM constrainedElement, final SetConstraint<ELEM> sc) {
		return sc.containsElement(constrainedElement);
	}

	public static <ELEM extends ICongruenceClosureElement<ELEM>> SetConstraint<ELEM> getInconsistentSetConstraint() {
		return new SetConstraint<>(true);
	}


	public Set<ELEM> getNonLiterals() {
		return Collections.unmodifiableSet(mNonLiterals);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + (mIsInconsistent ? 1231 : 1237);
		result = prime * result + ((mLiterals == null) ? 0 : mLiterals.hashCode());
		result = prime * result + ((mNonLiterals == null) ? 0 : mNonLiterals.hashCode());
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final SetConstraint<ELEM> other = (SetConstraint<ELEM>) obj;
		if (mIsInconsistent != other.mIsInconsistent) {
			return false;
		}
		if (mLiterals == null) {
			if (other.mLiterals != null) {
				return false;
			}
		} else if (!mLiterals.equals(other.mLiterals)) {
			return false;
		}
		if (mNonLiterals == null) {
			if (other.mNonLiterals != null) {
				return false;
			}
		} else if (!mNonLiterals.equals(other.mNonLiterals)) {
			return false;
		}
		return true;
	}


}
