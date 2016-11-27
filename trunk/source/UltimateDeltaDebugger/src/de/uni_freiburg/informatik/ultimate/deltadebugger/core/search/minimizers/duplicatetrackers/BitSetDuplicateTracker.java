/*
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the Ultimate Delta Debugger plug-in.
 *
 * The Ultimate Delta Debugger plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The Ultimate Delta Debugger plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the Ultimate Delta Debugger plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the Ultimate Delta Debugger plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the Ultimate Delta Debugger plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.duplicatetrackers;

import java.util.BitSet;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.IDuplicateVariantTracker;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.IHasSequenceIndex;

/**
 * A duplicate tracker that uses a bit set.
 */
public final class BitSetDuplicateTracker {
	private BitSetDuplicateTracker() {
		// static method access
	}
	
	/**
	 * @param <E>
	 *            element type
	 * @return A duplicate variant tracker.
	 */
	public static <E extends IHasSequenceIndex> IDuplicateVariantTracker<E> create() {
		return new DefaultBitSetDuplicateTracker<>();
	}
	
	/**
	 * Computes indices of a variant given the full input sequence. Assumes that all objects in the input sequence are
	 * unique. Otherwise this computation is unsound.
	 *
	 * @param <E>
	 *            element type
	 * @param input
	 *            input list
	 * @return fallback tracker
	 */
	public static <E> IDuplicateVariantTracker<E> createFallback(final List<E> input) {
		return new FallbackBitSetDuplicateTracker<>(input);
	}
	
	/**
	 * Abstract bit set duplicate tracker for inheritance.
	 * 
	 * @param <E>
	 *            element type
	 */
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
	
	/**
	 * A default bit set duplicate tracker.
	 * 
	 * @param <E>
	 *            element type
	 */
	static class DefaultBitSetDuplicateTracker<E extends IHasSequenceIndex>
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
	
	/**
	 * A bit set duplicate tracker for fallback.
	 * 
	 * @param <E>
	 *            element type
	 */
	static class FallbackBitSetDuplicateTracker<E> extends AbstractBitSetDuplicateTracker<E> {
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
