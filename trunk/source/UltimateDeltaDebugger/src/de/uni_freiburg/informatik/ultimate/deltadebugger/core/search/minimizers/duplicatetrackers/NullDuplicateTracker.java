package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.duplicatetrackers;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.IDuplicateVariantTracker;

/**
 * Remembers nothing and always returns false.
 *
 * @param <E>
 *            element type
 */
public class NullDuplicateTracker<E> implements IDuplicateVariantTracker<E> {
	public static final IDuplicateVariantTracker INSTANCE = new NullDuplicateTracker<>();

	public static <E> IDuplicateVariantTracker<E> getInstance() {
		return INSTANCE;
	}

	@Override
	public void add(final List<? extends E> variant) {
		// store nothing
	}

	@Override
	public boolean contains(final List<? extends E> variant) {
		return false;
	}

	@Override
	public void removeLargerVariants(final int keptVariantSize) {
		// nothing to remove
	}
}
