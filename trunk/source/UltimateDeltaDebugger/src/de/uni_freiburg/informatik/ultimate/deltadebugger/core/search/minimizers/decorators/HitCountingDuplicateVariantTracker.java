package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.decorators;

import java.util.List;
import java.util.Objects;
import java.util.concurrent.atomic.AtomicInteger;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.ChangeHandle;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.DuplicateVariantTracker;

public class HitCountingDuplicateVariantTracker implements DuplicateVariantTracker<ChangeHandle> {
	private final DuplicateVariantTracker<ChangeHandle> delegate;
	private final AtomicInteger counter;

	public HitCountingDuplicateVariantTracker(DuplicateVariantTracker<ChangeHandle> delegate, AtomicInteger counter) {
		this.delegate = Objects.requireNonNull(delegate);
		this.counter = Objects.requireNonNull(counter);
	}

	public AtomicInteger getCounter() {
		return counter;
	}

	@Override
	public void add(List<? extends ChangeHandle> variant) {
		delegate.add(variant);
	}

	@Override
	public boolean contains(List<? extends ChangeHandle> variant) {
		final boolean result = delegate.contains(variant);
		if (result) {
			counter.incrementAndGet();
		}
		return result;
	}

	@Override
	public void removeLargerVariants(int keptVariantSize) {
		delegate.removeLargerVariants(keptVariantSize);
	}

}