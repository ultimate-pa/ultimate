package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import java.util.Comparator;

/**
 * Order presented by Esparza, Römer, Vogler in 1996 TACAS,
 * <a href="http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.1.9584"> An improvement of McMillan's unfolding
 * algorithm</a>, definition 4.1.
 *
 * @author Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author schaetzc@tf.uni-freiburg.de
 * @author Mehdi Naouar
 *
 * @param <LETTER>
 *            Type of letters from the alphabet used to label transitions
 * @param <PLACE>
 *            place content type
 */
public class EsparzaRoemerVoglerOrder<LETTER, PLACE> extends ConfigurationOrder<LETTER, PLACE> {
	final Comparator<Event<LETTER, PLACE>> mIdComparator = new IdComparator();
	int mFotateNormalFormComparisons = 0;

	@Override
	public int compare(final Configuration<LETTER, PLACE> c1, final Configuration<LETTER, PLACE> c2) {
		// we compare first the sizes of C1 and C2; if they are equal, we compare ϕ(C1)
		// and ϕ(C2);
		int result = c1.compareTo(c2, mIdComparator);
		if (result != 0) {
			return result;
		}

		// if they are equal, we compare FC1 and FC2 by comparing their Foata normal
		// forms FC1 = C11...C1n1 and
		// FC2 =C21...C2n2 with respect to the order <<
		// See Section 6 of the following publication.
		// 2002FMSD - Esparza,Römer,Vogler - An Improvement of McMillan's Unfolding Algorithm
		c1.computeFoataNormalForm();
		c2.computeFoataNormalForm();
		mFotateNormalFormComparisons++;
		final int maxDepth = Math.max(c1.getDepth(), c2.getDepth());

		for (int depth = 1; depth < maxDepth + 1; depth++) {
			result = c1.compareMin(c2, depth, mIdComparator);
			if (result != 0) {
				return result;
			}
		}
		assert false : "the Order is total";
		return 0;
	}

	@Override
	public boolean isTotal() {
		return true;
	}

	@Override
	public int getFotateNormalFormComparisons() {
		return mFotateNormalFormComparisons;
	}

	class IdComparator implements Comparator<Event<LETTER, PLACE>> {
		@Override
		public int compare(final Event<LETTER, PLACE> e1, final Event<LETTER, PLACE> e2) {
			return e1.getTotalOrderId() - e2.getTotalOrderId();
		}
	}
}
