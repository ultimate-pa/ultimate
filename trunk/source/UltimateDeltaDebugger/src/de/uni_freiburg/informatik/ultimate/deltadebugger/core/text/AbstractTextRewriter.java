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
		protected final int offset;
		protected final int endOffset;
		protected final String replacement;

		protected Change(final int offset, final int endOffset, final String replacement) {
			this.offset = offset;
			this.endOffset = endOffset;
			this.replacement = replacement;
		}

		protected int length() {
			return endOffset - offset;
		}
	}

	private final List<Change> changes;

	private int delta;

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
		this(new ArrayList<>(other.changes), other.delta);
	}

	protected AbstractTextRewriter(final List<Change> changes, final int delta) {
		this.changes = changes;
		this.delta = delta;
	}

	private void addAllOrNone(final List<Change> source) {
		int nextSourceIndex = 0;
		int lastDestIndex = -1;
		try {
			for (; nextSourceIndex != source.size(); ++nextSourceIndex) {
				final Change newChange = source.get(nextSourceIndex);
				lastDestIndex = findInsertionIndex(newChange, lastDestIndex + 1);
				changes.add(lastDestIndex, newChange);
			}
		} catch (final RewriteConflictException e) {
			// Rollback by removing all added Change instances backwards
			while (nextSourceIndex > 0) {
				final Change newChange = source.get(--nextSourceIndex);
				while (true) {
					if (lastDestIndex < 0) {
						throw new IllegalStateException("rollback failed ffs");
					}
					if (changes.get(lastDestIndex) == newChange) {
						changes.remove(lastDestIndex);
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
		changes.add(findInsertionIndex(newChange, 0), newChange);
		delta += newChange.replacement.length() - newChange.length();
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
		final StringBuilder sb = new StringBuilder(getOriginalLength() + delta);
		int cursor = 0;
		for (final Change change : changes) {
			sb.append(originalText, cursor, change.offset).append(change.replacement);
			cursor = change.endOffset;
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
		if (startIndex > changes.size()) {
			throw new IllegalArgumentException();
		}
		// Shortcut for constant time insertion if changes are appended
		if (!changes.isEmpty() && changes.get(changes.size() - 1).endOffset <= change.offset) {
			return changes.size();
		}
		int low = startIndex;
		int high = changes.size() - 1;
		while (low <= high) {
			final int mid = low + high >>> 1;
			if (isInsertedAfter(change, changes.get(mid))) {
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
		return delta;
	}

	protected String getExceptionText(final Change change) {
		return "[" + change.offset + ", " + change.endOffset + "]";
	}

	protected List<Change> getMergedChanges(final AbstractTextRewriter other) {
		return mergeSortedLists(changes, other.changes);
	}

	protected abstract int getOriginalLength();

	protected abstract String getOriginalText();

	public int getRewrittenLength() {
		return getOriginalLength() + delta;
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
		return changes.isEmpty();
	}

	private boolean isInsertedAfter(final Change newChange, final Change existing) {
		// Keep order of multiple insertions at the same offset
		if (newChange.offset >= existing.endOffset) {
			return true;
		} else if (newChange.endOffset <= existing.offset) {
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
		addAllOrNone(other.changes);
		delta += other.delta;
		return this;
	}

	private List<Change> mergeSortedLists(final List<Change> lhs, final List<Change> rhs) {
		final List<Change> merged = new ArrayList<>(lhs.size() + rhs.size());
		int left = 0;
		int right = 0;
		while (left != lhs.size() && right != rhs.size()) {
			if (isInsertedAfter(rhs.get(right), lhs.get(left))) {
				merged.add(lhs.get(left++));
			} else {
				merged.add(rhs.get(right++));
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
		for (final Change change : changes) {
			if (change.offset < offset) {
				result += change.replacement.length() - change.length();
			} else if (includeInsertions && change.offset == offset && change.length() == 0) {
				result += change.replacement.length();
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
