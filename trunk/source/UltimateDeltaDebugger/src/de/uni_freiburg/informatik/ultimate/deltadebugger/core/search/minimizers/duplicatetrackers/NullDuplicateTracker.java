package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.duplicatetrackers;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.DuplicateVariantTracker;

/**
 * Remembers nothing and always returns false.
 *
 * @param <E> element type
 */
public class NullDuplicateTracker<E> implements DuplicateVariantTracker<E> {
	@SuppressWarnings("rawtypes")
	public static final DuplicateVariantTracker INSTANCE = new NullDuplicateTracker<>(); 
	
	@SuppressWarnings("unchecked")
	public static <E> DuplicateVariantTracker<E> getInstance() {
		return INSTANCE;
	}
	
	@Override
	public void add(List<? extends E> variant) {
		// store nothing
	}

	@Override
	public boolean contains(List<? extends E> variant) {
		return false;
	}

	@Override
	public void removeLargerVariants(int keptVariantSize) {
		// nothing to remove
	}
}