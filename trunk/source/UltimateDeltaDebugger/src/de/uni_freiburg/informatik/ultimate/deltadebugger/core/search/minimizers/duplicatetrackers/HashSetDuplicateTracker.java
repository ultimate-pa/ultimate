package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.duplicatetrackers;

import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.IDuplicateVariantTracker;

/**
 * Just stores all lists in a hash set, good choice for smaller inputs.
 *
 * @param <E>
 */
public class HashSetDuplicateTracker<E> implements IDuplicateVariantTracker<E> {
	private final Set<List<? extends E>> mVariants = new HashSet<>();

	@Override
	public void add(final List<? extends E> variant) {
		mVariants.add(variant);
	}

	@Override
	public boolean contains(final List<? extends E> variant) {
		return mVariants.contains(variant);
	}

	@Override
	public void removeLargerVariants(final int keptVariantSize) {
		final Iterator<List<? extends E>> it = mVariants.iterator();
		while (it.hasNext()) {
			if (it.next().size() >= keptVariantSize) {
				it.remove();
			}
		}
	}

}
