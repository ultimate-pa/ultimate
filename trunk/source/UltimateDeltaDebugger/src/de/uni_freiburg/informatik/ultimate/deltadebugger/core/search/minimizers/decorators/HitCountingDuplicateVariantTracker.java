package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.decorators;

import java.util.List;
import java.util.Objects;
import java.util.concurrent.atomic.AtomicInteger;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.IChangeHandle;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.DuplicateVariantTracker;

public class HitCountingDuplicateVariantTracker implements DuplicateVariantTracker<IChangeHandle> {
	private final DuplicateVariantTracker<IChangeHandle> delegate;
	private final AtomicInteger counter;

	public HitCountingDuplicateVariantTracker(final DuplicateVariantTracker<IChangeHandle> delegate,
			final AtomicInteger counter) {
		this.delegate = Objects.requireNonNull(delegate);
		this.counter = Objects.requireNonNull(counter);
	}

	@Override
	public void add(final List<? extends IChangeHandle> variant) {
		delegate.add(variant);
	}

	@Override
	public boolean contains(final List<? extends IChangeHandle> variant) {
		final boolean result = delegate.contains(variant);
		if (result) {
			counter.incrementAndGet();
		}
		return result;
	}

	public AtomicInteger getCounter() {
		return counter;
	}

	@Override
	public void removeLargerVariants(final int keptVariantSize) {
		delegate.removeLargerVariants(keptVariantSize);
	}

}