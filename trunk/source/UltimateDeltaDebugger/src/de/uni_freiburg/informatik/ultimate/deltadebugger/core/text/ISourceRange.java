package de.uni_freiburg.informatik.ultimate.deltadebugger.core.text;

/**
 * Represents a character range in a source file.
 */
public interface ISourceRange {

	/**
	 * @return start offset of the range
	 */
	int offset();
		
	/**
	 * @return exlusive end-offset of the range
	 */
	int endOffset();

	/**
	 * @return number of characters in this range
	 */
	default int length() {
		return endOffset() - offset();
	}
	
	default boolean contains(int index) {
		return offset() <= index && index < endOffset();
	}
	
	default boolean contains(ISourceRange other) {
		return offset() <= other.offset() && other.endOffset() <= endOffset();
	}
	
	default boolean contains(int offset, int endOffset) {
		return offset() <= offset && endOffset <= endOffset();
	}
	
	default boolean disjoint(ISourceRange other) {
		return endOffset() <= other.offset() || other.endOffset() <= offset();
	}
	
	default boolean equalsSourceRange(ISourceRange other) {
		return offset() == other.offset() && endOffset() == other.endOffset();
	}
}
