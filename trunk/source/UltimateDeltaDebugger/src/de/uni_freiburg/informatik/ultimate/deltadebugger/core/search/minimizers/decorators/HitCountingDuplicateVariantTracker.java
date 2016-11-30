package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.decorators;

import java.util.List;
import java.util.Objects;
import java.util.concurrent.atomic.AtomicInteger;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.IChangeHandle;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.IDuplicateVariantTracker;

/**
 * Duplicate variant tracker that counts hits.
 */
public class HitCountingDuplicateVariantTracker implements IDuplicateVariantTracker<IChangeHandle> {
	private final IDuplicateVariantTracker<IChangeHandle> mDelegate;
	private final AtomicInteger mCounter;
	
	/**
	 * @param delegate
	 *            Delegate duplicate variant tracker.
	 * @param counter
	 *            counter
	 */
	public HitCountingDuplicateVariantTracker(final IDuplicateVariantTracker<IChangeHandle> delegate,
			final AtomicInteger counter) {
		mDelegate = Objects.requireNonNull(delegate);
		mCounter = Objects.requireNonNull(counter);
	}
	
	@Override
	public void add(final List<? extends IChangeHandle> variant) {
		mDelegate.add(variant);
	}
	
	@Override
	public boolean contains(final List<? extends IChangeHandle> variant) {
		final boolean result = mDelegate.contains(variant);
		if (result) {
			mCounter.incrementAndGet();
		}
		return result;
	}
	
	public AtomicInteger getCounter() {
		return mCounter;
	}
	
	@Override
	public void removeLargerVariants(final int keptVariantSize) {
		mDelegate.removeLargerVariants(keptVariantSize);
	}
}
