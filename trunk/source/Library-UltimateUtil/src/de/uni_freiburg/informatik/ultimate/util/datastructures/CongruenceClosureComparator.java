package de.uni_freiburg.informatik.ultimate.util.datastructures;

import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.IPartialComparator;

/**
 * Checks for strength of the constraint that is expressed by the given CongruenceClosures.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <E>
 */
public class CongruenceClosureComparator<E extends ICongruenceClosureElement<E>>
		implements IPartialComparator<CongruenceClosure<E>> {

	@Override
	public ComparisonResult compare(final CongruenceClosure<E> o1, final CongruenceClosure<E> o2) {
		if (o1.equals(o2)) {
			return ComparisonResult.EQUAL;
		}
		final boolean o1Stronger = o1.isStrongerThan(o2);
		final boolean o2Stronger = o2.isStrongerThan(o1);
		if (o1Stronger && o2Stronger) {
			return ComparisonResult.EQUAL;
		} else if (o1Stronger) {
			return ComparisonResult.STRICTLY_SMALLER;
		} else if (o2Stronger) {
			return ComparisonResult.STRICTLY_GREATER;
		} else {
			return ComparisonResult.INCOMPARABLE;
		}
	}
}