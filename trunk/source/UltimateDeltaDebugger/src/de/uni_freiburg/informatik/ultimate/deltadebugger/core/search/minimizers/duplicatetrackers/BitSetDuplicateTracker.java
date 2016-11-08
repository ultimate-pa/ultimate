package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.duplicatetrackers;

import java.util.BitSet;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.IDuplicateVariantTracker;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.IHasSequenceIndex;

public final class BitSetDuplicateTracker {

	private BitSetDuplicateTracker() {
	}
	
	public static <E extends IHasSequenceIndex> IDuplicateVariantTracker<E> create() {
		return new DefaultBitSetDuplicateTracker<>();
	}

	/**
	 * Computes indices of a variant given the full input sequence. Assumes that all objects in the input sequence are
	 * unique. Otherwise this computation is unsound.
	 *
	 * @param <E>
	 */
	public static <E> IDuplicateVariantTracker<E> createFallback(final List<E> input) {
		return new FallbackBitSetDuplicateTracker<>(input);
	}
	
	private abstract static class AbstractBitSetDuplicateTracker<E> implements IDuplicateVariantTracker<E> {
		protected final Set<BitSet> mVariants = new HashSet<>();
	
		@Override
		public void add(final List<? extends E> variant) {
			mVariants.add(computeInputIndices(variant));
		}
	
		protected abstract BitSet computeInputIndices(List<? extends E> variant);
	
		@Override
		public boolean contains(final List<? extends E> variant) {
			return mVariants.contains(computeInputIndices(variant));
		}
	
		@Override
		public void removeLargerVariants(final int keptVariantSize) {
			final Iterator<BitSet> it = mVariants.iterator();
			while (it.hasNext()) {
				if (it.next().cardinality() >= keptVariantSize) {
					it.remove();
				}
			}
		}
	
	}

	private static class DefaultBitSetDuplicateTracker<E extends IHasSequenceIndex>
			extends AbstractBitSetDuplicateTracker<E> {
		@Override
		protected BitSet computeInputIndices(final List<? extends E> variant) {
			if (variant.isEmpty()) {
				return new BitSet();
			}
	
			final int highestBit = variant.get(variant.size() - 1).getSequenceIndex();
			final BitSet result = new BitSet(highestBit + 1);
			for (final IHasSequenceIndex e : variant) {
				result.set(e.getSequenceIndex());
			}
			return result;
		}
	}
	
	private static class FallbackBitSetDuplicateTracker<E> extends AbstractBitSetDuplicateTracker<E> {
		private final List<E> mInput;
	
		public FallbackBitSetDuplicateTracker(final List<E> input) {
			mInput = input;
		}
	
		@Override
		protected BitSet computeInputIndices(final List<? extends E> variant) {
			final BitSet result = new BitSet(mInput.size());
			final Iterator<? extends E> it = variant.iterator();
			final ListIterator<? extends E> inputIter = mInput.listIterator();
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

}
