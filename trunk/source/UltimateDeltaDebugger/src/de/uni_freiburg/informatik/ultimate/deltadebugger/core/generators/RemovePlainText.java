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
package de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators;

import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.IChangeHandle;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.IPassContext;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.IVariantGenerator;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;

/**
 * Removes Lines or Characters.
 */
public final class RemovePlainText implements IVariantGenerator {
	private final ISourceDocument mSource;
	private final List<PlainTextChange> mChanges;
	private final boolean mRemoveLines;

	private RemovePlainText(final ISourceDocument source, final List<PlainTextChange> changes,
			final boolean removeLines) {
		mSource = source;
		mChanges = changes;
		mRemoveLines = removeLines;
	}

	@Override
	public List<IChangeHandle> getChanges() {
		return Collections.unmodifiableList(mChanges);
	}

	@Override
	public String apply(final List<IChangeHandle> activeChanges) {
		if (activeChanges.isEmpty()) {
			return mSource.getText();
		}
		final String text = mSource.getText();
		final int maxIndex = mRemoveLines ? mSource.getNumberOfLines() : mSource.getLength();
		final StringBuilder sb = new StringBuilder();
		final Iterator<IChangeHandle> iter = activeChanges.iterator();
		PlainTextChange nextChange = (PlainTextChange) iter.next();
		for (int i = 0; i < maxIndex; ++i) {
			if (nextChange != null && i == nextChange.mIndex) {
				nextChange = iter.hasNext() ? (PlainTextChange) iter.next() : null;
				continue;
			}
			if (mRemoveLines) {
				final int endOffset = (i + 1 == mSource.getNumberOfLines()) ? mSource.getLength()
						: mSource.getLineOffset(i + 2);
				sb.append(text, mSource.getLineOffset(i + 1), endOffset);
			} else {
				sb.append(text.charAt(i));
			}
		}

		return sb.toString();
	}

	private static int getNumberOfRemovableLines(ISourceDocument source) {
		// Don't count an empty final line
		int numLines = source.getNumberOfLines();
		if (source.getLineOffset(numLines) == source.getLength()) {
			return numLines - 1;
		}
		return numLines;
	}

	/**
	 * @param context
	 *            Pass context.
	 * @return result
	 */
	public static Optional<IVariantGenerator> analyzeLines(final IPassContext context) {
		final int numLines = getNumberOfRemovableLines(context.getInput());
		final List<PlainTextChange> changes = IntStream.range(0, numLines).mapToObj(PlainTextChange::new)
				.collect(Collectors.toList());
		return changes.isEmpty() ? Optional.empty()
				: Optional.of(new RemovePlainText(context.getInput(), changes, true));
	}

	/**
	 * @param context
	 *            Pass context.
	 * @return result
	 */
	public static Optional<IVariantGenerator> analyzeChars(final IPassContext context) {
		final List<PlainTextChange> changes = IntStream.range(0, context.getInput().getLength())
				.mapToObj(PlainTextChange::new).collect(Collectors.toList());
		return changes.isEmpty() ? Optional.empty()
				: Optional.of(new RemovePlainText(context.getInput(), changes, false));
	}

	/**
	 * A change handle.
	 */
	private static class PlainTextChange implements IChangeHandle {
		private final int mIndex;

		public PlainTextChange(final int index) {
			mIndex = index;
		}

		@Override
		public int getSequenceIndex() {
			return mIndex;
		}
	}
}
