package de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure;

import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.IPartialComparator;

/**
 * Convention: Stronger constraints are "smaller"
 *
 * note that this is sublty different from the CongruenceClosureComparator,
 * because here we want to keep the strongest, not the weakest elements when
 * filtering..
 *
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <ELEM>
 */
public class SetConstraintComparator<ELEM extends ICongruenceClosureElement<ELEM>>
		implements IPartialComparator<SetConstraint<ELEM>> {

	private final SetConstraintManager<ELEM> mSetConstraintManager;
	public SetConstraintComparator(final SetConstraintManager<ELEM> setConstraintManager) {
		mSetConstraintManager = setConstraintManager;
	}

	@Override
	public ComparisonResult compare(final SetConstraint<ELEM> o1, final SetConstraint<ELEM> o2) {
		if (o1.equals(o2)) {
			return ComparisonResult.EQUAL;
		}
		final boolean o1Stronger = mSetConstraintManager.isStrongerThan(o1, o2);
		final boolean o2Stronger = mSetConstraintManager.isStrongerThan(o2, o1);
		if (o1Stronger && o2Stronger) {
			return ComparisonResult.EQUAL;
		} else if (o1Stronger) {
			// return ComparisonResult.STRICTLY_SMALLER;
			return ComparisonResult.STRICTLY_GREATER;
		} else if (o2Stronger) {
			return ComparisonResult.STRICTLY_SMALLER;
			// return ComparisonResult.STRICTLY_GREATER;
		} else {
			return ComparisonResult.INCOMPARABLE;
		}
	}
}