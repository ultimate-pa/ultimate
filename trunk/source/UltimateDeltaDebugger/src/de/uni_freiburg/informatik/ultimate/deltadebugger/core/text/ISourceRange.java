package de.uni_freiburg.informatik.ultimate.deltadebugger.core.text;

/**
 * Represents a character range in a source file.
 */
public interface ISourceRange {

	default boolean contains(final int index) {
		return offset() <= index && index < endOffset();
	}

	default boolean contains(final int offset, final int endOffset) {
		return offset() <= offset && endOffset <= endOffset();
	}

	default boolean contains(final ISourceRange other) {
		return offset() <= other.offset() && other.endOffset() <= endOffset();
	}

	default boolean disjoint(final ISourceRange other) {
		return endOffset() <= other.offset() || other.endOffset() <= offset();
	}

	/**
	 * @return exlusive end-offset of the range
	 */
	int endOffset();

	default boolean equalsSourceRange(final ISourceRange other) {
		return offset() == other.offset() && endOffset() == other.endOffset();
	}

	/**
	 * @return number of characters in this range
	 */
	default int length() {
		return endOffset() - offset();
	}

	/**
	 * @return start offset of the range
	 */
	int offset();
}
