package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.duplicatetrackers;

import java.util.BitSet;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.DuplicateVariantTracker;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.HasSequenceIndex;

abstract class AbstractBitSetDuplicateTracker<E> implements DuplicateVariantTracker<E> {
	protected final Set<BitSet> variants = new HashSet<>();

	@Override
	public void add(final List<? extends E> variant) {
		variants.add(computeInputIndices(variant));
	}

	protected abstract BitSet computeInputIndices(List<? extends E> variant);

	@Override
	public boolean contains(final List<? extends E> variant) {
		return variants.contains(computeInputIndices(variant));
	}

	@Override
	public void removeLargerVariants(final int keptVariantSize) {
		final Iterator<BitSet> it = variants.iterator();
		while (it.hasNext()) {
			if (it.next().cardinality() >= keptVariantSize) {
				it.remove();
			}
		}
	}

}

public class BitSetDuplicateTracker {
	public static <E extends HasSequenceIndex> DuplicateVariantTracker<E> create() {
		return new DefaultBitSetDuplicateTracker<>();
	}

	/**
	 * Computes indices of a variant given the full input sequence. Assumes that all objects in the input sequence are
	 * unique. Otherwise this computation is unsound.
	 *
	 * @param <E>
	 */
	public static <E> DuplicateVariantTracker<E> createFallback(final List<E> input) {
		return new FallbackBitSetDuplicateTracker<>(input);
	}

	private BitSetDuplicateTracker() {
	}

}

class DefaultBitSetDuplicateTracker<E extends HasSequenceIndex> extends AbstractBitSetDuplicateTracker<E> {

	@Override
	protected BitSet computeInputIndices(final List<? extends E> variant) {
		if (variant.isEmpty()) {
			return new BitSet();
		}

		final int highestBit = variant.get(variant.size() - 1).getSequenceIndex();
		final BitSet result = new BitSet(highestBit + 1);
		for (final HasSequenceIndex e : variant) {
			result.set(e.getSequenceIndex());
		}
		return result;
	}
}

class FallbackBitSetDuplicateTracker<E> extends AbstractBitSetDuplicateTracker<E> {
	final List<E> input;

	public FallbackBitSetDuplicateTracker(final List<E> input) {
		this.input = input;
	}

	@Override
	protected BitSet computeInputIndices(final List<? extends E> variant) {
		final BitSet result = new BitSet(input.size());
		final Iterator<? extends E> it = variant.iterator();
		final ListIterator<? extends E> inputIter = input.listIterator();
		while (it.hasNext()) {
			final E element = it.next();
			while (true) {
				if (inputIter.next().equals(element)) {
					result.set(inputIter.previousIndex());
					break;
				}
			}
		}
		return result;
	}
}
