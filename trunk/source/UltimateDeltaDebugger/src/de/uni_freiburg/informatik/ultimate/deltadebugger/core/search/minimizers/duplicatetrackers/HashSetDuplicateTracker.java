package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.duplicatetrackers;

import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.DuplicateVariantTracker;

/**
 * Just stores all lists in a hash set, good choice for smaller inputs.
 *
 * @param <E>
 */
public class HashSetDuplicateTracker<E> implements DuplicateVariantTracker<E> {
	final Set<List<? extends E>> variants = new HashSet<>();
	
	@Override
	public void add(List<? extends E> variant) {
		variants.add(variant);
	}

	@Override
	public boolean contains(List<? extends E> variant) {
		return variants.contains(variant);
	}

	@Override
	public void removeLargerVariants(int keptVariantSize) {
		final Iterator<List<? extends E>> it = variants.iterator();
		while (it.hasNext()) {
			if (it.next().size() >= keptVariantSize) {
				it.remove();
			}
		}
	}

}
