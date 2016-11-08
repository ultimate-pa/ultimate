package de.uni_freiburg.informatik.ultimate.deltadebugger.core.text;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.exceptions.RewriteConflictException;

/**
 * Collects multiple independent text changes specified by the original character offsets and eventually applies them
 * all to the original text. Only non-overlapping changes are allowed, i.e. all changed regions must be disjoint.
 *
 * Multiple insertions at the same offset are allowed as long as the surrounding region is not deleted/replaced.
 * Subsequent insertions are appended to the existing insertion. Other than that the order of operations does not
 * matter.
 *
 * All modifications are validated as early as possible (fail-fast). If an attempt to change an already changed range is
 * detected, a RewriteConflictException is thrown and the observable state is not modified. The merge method allows to
 * commit multiple changes together iff all of them can be applied.
 *
 * This class is meant to be a simplified alternative to org.eclipse.text.edits.TextEdit. It has similiar behaviour but
 * additionally validates that all changes are within the original text bounds as early as possible.
 */
public abstract class AbstractTextRewriter {
	protected static class Change {
		protected final int mOffset;
		protected final int mEndOffset;
		protected final String mReplacement;

		protected Change(final int offset, final int endOffset, final String replacement) {
			mOffset = offset;
			mEndOffset = endOffset;
			mReplacement = replacement;
		}

		protected int length() {
			return mEndOffset - mOffset;
		}
	}

	private final List<Change> mChanges;

	private int mDelta;

	/**
	 * Creates a new rewriter instance for an arbitrary text of the specified length. The originalLength is used to
	 * validate bounds of all operations.
	 *
	 * @param originalLength
	 *            length of the original text
	 */
	protected AbstractTextRewriter() {
		this(new ArrayList<>(), 0);
	}

	/**
	 * Copy constructor.
	 *
	 * @param other
	 *            source rewriter to copy
	 */
	protected AbstractTextRewriter(final AbstractTextRewriter other) {
		this(new ArrayList<>(other.mChanges), other.mDelta);
	}

	protected AbstractTextRewriter(final List<Change> changes, final int delta) {
		this.mChanges = changes;
		this.mDelta = delta;
	}

	private void addAllOrNone(final List<Change> source) {
		int nextSourceIndex = 0;
		int lastDestIndex = -1;
		try {
			for (; nextSourceIndex != source.size(); ++nextSourceIndex) {
				final Change newChange = source.get(nextSourceIndex);
				lastDestIndex = findInsertionIndex(newChange, lastDestIndex + 1);
				mChanges.add(lastDestIndex, newChange);
			}
		} catch (final RewriteConflictException e) {
			// Rollback by removing all added Change instances backwards
			while (nextSourceIndex > 0) {
				--nextSourceIndex;
				final Change newChange = source.get(nextSourceIndex);
				while (true) {
					if (lastDestIndex < 0) {
						throw new IllegalStateException("rollback failed ffs");
					}
					if (mChanges.get(lastDestIndex).equals(newChange)) {
						mChanges.remove(lastDestIndex);
						--lastDestIndex;
						break;
					}
					--lastDestIndex;
				}
			}
			throw e;
		}
	}

	private void addNewChange(final int offset, final int endOffset, final String replacement) {
		if (offset < 0 || offset > endOffset || endOffset > getOriginalLength()) {
			throw new IndexOutOfBoundsException(
					"offset=" + offset + " endOffset=" + endOffset + " originalLength=" + getOriginalLength());
		}
		// Do not add changes that don't actually change something
		if (offset == endOffset && replacement.isEmpty()) {
			return;
		}
		final Change newChange = new Change(offset, endOffset, replacement);
		mChanges.add(findInsertionIndex(newChange, 0), newChange);
		mDelta += newChange.mReplacement.length() - newChange.length();
	}

	/**
	 * Applies all recorded changes to the original text.
	 *
	 * @param originalText
	 *            original text
	 * @return rewritten text
	 */
	public String apply() {
		final String originalText = getOriginalText();
		if (isEmpty()) {
			return originalText;
		}
		final StringBuilder sb = new StringBuilder(getOriginalLength() + mDelta);
		int cursor = 0;
		for (final Change change : mChanges) {
			sb.append(originalText, cursor, change.mOffset).append(change.mReplacement);
			cursor = change.mEndOffset;
		}
		sb.append(originalText, cursor, originalText.length());
		return sb.toString();
	}

	/**
	 * Removes a range of text.
	 *
	 * Equivalent to {@code replace(offset, endOffset, "")}
	 *
	 * @param offset
	 *            inclusive start index to delete from
	 * @param endOffset
	 *            exclusive end index up to which text is deleted
	 * @return this
	 * @throws RewriteConflictException
	 */
	public AbstractTextRewriter delete(final int offset, final int endOffset) {
		addNewChange(offset, endOffset, "");
		return this;
	}

	private int findInsertionIndex(final Change change, final int startIndex) {
		if (startIndex > mChanges.size()) {
			throw new IllegalArgumentException();
		}
		// Shortcut for constant time insertion if changes are appended
		if (!mChanges.isEmpty() && mChanges.get(mChanges.size() - 1).mEndOffset <= change.mOffset) {
			return mChanges.size();
		}
		int low = startIndex;
		int high = mChanges.size() - 1;
		while (low <= high) {
			final int mid = (low + high) >>> 1;
			if (isInsertedAfter(change, mChanges.get(mid))) {
				low = mid + 1;
			} else {
				high = mid - 1;
			}
		}
		return low;
	}

	/**
	 * @return getRewrittenLength() - getOriginalLength()
	 */
	public int getDelta() {
		return mDelta;
	}

	protected String getExceptionText(final Change change) {
		return "[" + change.mOffset + ", " + change.mEndOffset + "]";
	}

	protected List<Change> getMergedChanges(final AbstractTextRewriter other) {
		return mergeSortedLists(mChanges, other.mChanges);
	}

	protected abstract int getOriginalLength();

	protected abstract String getOriginalText();

	public int getRewrittenLength() {
		return getOriginalLength() + mDelta;
	}

	/**
	 * Inserts a string at an offset.
	 *
	 * Equivalent to {@code replace(offset, offset, text)}
	 *
	 * @param offset
	 *            index to insert at
	 * @param text
	 *            inserted text string
	 * @return this
	 * @throws RewriteConflictException
	 */
	public AbstractTextRewriter insert(final int offset, final String text) {
		addNewChange(offset, offset, Objects.requireNonNull(text));
		return this;
	}

	public boolean isEmpty() {
		return mChanges.isEmpty();
	}

	private boolean isInsertedAfter(final Change newChange, final Change existing) {
		// Keep order of multiple insertions at the same offset
		if (newChange.mOffset >= existing.mEndOffset) {
			return true;
		} else if (newChange.mEndOffset <= existing.mOffset) {
			return false;
		}
		throw new RewriteConflictException("New change " + getExceptionText(newChange)
				+ " conflicts with previous change " + getExceptionText(existing));
	}

	/**
	 * Add all changes from the other rewriter to this instance.
	 *
	 * In case of a RewriteConflictException this instance is not modified.
	 *
	 * @param other
	 *            rewriter containing changes to be added
	 * @return this
	 * @throws RewriteConflictException
	 * @throws IllegalArgumentException
	 *             if original length in both rewriters is not the same
	 */
	public AbstractTextRewriter merge(final AbstractTextRewriter other) {
		if (getOriginalLength() != other.getOriginalLength()) {
			throw new IllegalArgumentException("length mismatch");
		}
		addAllOrNone(other.mChanges);
		mDelta += other.mDelta;
		return this;
	}

	private List<Change> mergeSortedLists(final List<Change> lhs, final List<Change> rhs) {
		final List<Change> merged = new ArrayList<>(lhs.size() + rhs.size());
		int left = 0;
		int right = 0;
		while (left != lhs.size() && right != rhs.size()) {
			if (isInsertedAfter(rhs.get(right), lhs.get(left))) {
				merged.add(lhs.get(left));
				++left;
			} else {
				merged.add(rhs.get(right));
				++right;
			}
		}
		merged.addAll(lhs.subList(left, lhs.size()));
		merged.addAll(rhs.subList(right, rhs.size()));
		return merged;
	}

	/**
	 * Computes a character's offset in the rewritten text for a given offset in the original text.
	 *
	 * @param offset
	 *            offset in the original text
	 * @param includeInsertions
	 *            include insertations at offset, i.e. compute the remapped offset after all insertions at the original
	 *            offset
	 * @return corresponding offset in the rewritten text
	 * @throws IndexOutOfBoundsException
	 */
	public int remapOffset(final int offset, final boolean includeInsertions) {
		if (offset < 0 || offset > getOriginalLength()) {
			throw new IndexOutOfBoundsException();
		}
		int result = offset;
		for (final Change change : mChanges) {
			if (change.mOffset < offset) {
				result += change.mReplacement.length() - change.length();
			} else if (includeInsertions && change.mOffset == offset && change.length() == 0) {
				result += change.mReplacement.length();
			} else {
				break;
			}
		}
		return result;
	}

	/**
	 * Replaces a range of text.
	 *
	 * @param offset
	 *            inclusive start index to replace from
	 * @param endOffset
	 *            exclusive end index up to which text is replaced
	 * @param replacement
	 *            replacement string
	 * @return this
	 * @throws RewriteConflictException
	 */
	public AbstractTextRewriter replace(final int offset, final int endOffset, final String replacement) {
		addNewChange(offset, endOffset, Objects.requireNonNull(replacement));
		return this;
	}
}
