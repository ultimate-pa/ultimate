package de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure;

import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.IPartialComparator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.SymmetricHashRelation;

public class CachingSetConstraintComparator<ELEM extends ICongruenceClosureElement<ELEM>>
		implements IPartialComparator<SetConstraint<ELEM>> {

	private final SetConstraintComparator<ELEM> mBaseScc;

//	SymmetricHashRelation<SetConstraint<ELEM>> mEqualElements = new SymmetricHashRelation<>();
	SymmetricHashRelation<SetConstraint<ELEM>> mIncomparableElements = new SymmetricHashRelation<>();
	HashRelation<SetConstraint<ELEM>, SetConstraint<ELEM>> mStrictlySmaller = new HashRelation<>();

	// po cache is not a good idea here
//	private final PartialOrderCache<SetConstraint<ELEM>> mPoCache;

	public CachingSetConstraintComparator(final SetConstraintManager<ELEM> setConstraintManager) {
		mBaseScc = new SetConstraintComparator<>(setConstraintManager);
//		mPoCache = new PartialOrderCache<>(mBaseScc);
	}

	@Override
	public ComparisonResult compare(final SetConstraint<ELEM> o1, final SetConstraint<ELEM> o2) {

		if (mIncomparableElements.containsPair(o1, o2)) {
			return ComparisonResult.INCOMPARABLE;
		}
		if (mStrictlySmaller.containsPair(o1, o2)) {
			return ComparisonResult.STRICTLY_SMALLER;
		}
		if (mStrictlySmaller.containsPair(o2, o1)) {
			return ComparisonResult.STRICTLY_GREATER;
		}

		final ComparisonResult comparisonResult = mBaseScc.compare(o1, o2);

		if (comparisonResult == ComparisonResult.INCOMPARABLE) {
			mIncomparableElements.addPair(o1, o2);
		} else if (comparisonResult == ComparisonResult.STRICTLY_GREATER) {
			mStrictlySmaller.addPair(o2, o1);
		} else if (comparisonResult == ComparisonResult.STRICTLY_SMALLER) {
			mStrictlySmaller.addPair(o1, o2);
		} else {
			assert false : "setConstraints are unified, right??";
		}
		return comparisonResult;

//		mPoCache.addElement(o1);
//		mPoCache.addElement(o2);
//
//		final boolean o1Stronger = mPoCache.lowerEqual(o2, o1);
//		final boolean o2Stronger = mPoCache.lowerEqual(o1, o2);
//		if (o1Stronger && o2Stronger) {
//			return ComparisonResult.EQUAL;
//		} else if (o1Stronger) {
//			return ComparisonResult.STRICTLY_GREATER;
//		} else if (o2Stronger) {
//			return ComparisonResult.STRICTLY_SMALLER;
//		} else {
//			return ComparisonResult.INCOMPARABLE;
//		}

	}
}
