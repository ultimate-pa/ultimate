package de.uni_freiburg.informatik.ultimate.deltadebugger.core.text;

import java.util.Arrays;
import java.util.Objects;
import java.util.concurrent.atomic.AtomicReference;

public class StringSourceDocument implements ISourceDocument {
	private final String text;
	private AtomicReference<int[]> lazyNewLineOffsets = new AtomicReference<>(null);
	
	public StringSourceDocument(String text) {
		this.text = Objects.requireNonNull(text);
	}
		
	@Override
	public int getLength() {
		return text.length();
	}

	@Override
	public String getText() {
		return text;
	}

	@Override
	public String getText(int offset, int endOffset) {
		return text.substring(offset, endOffset);
	}

	@Override
	public String getText(ISourceRange location) {
		return getText(location.offset(), location.endOffset());
	}


	@Override
	public int getNumberOfLines() {
		return getNewLineOffsets().length + 1;
	}
	
	@Override
	public int getLineNumber(int offset) {
		final int index = Arrays.binarySearch(getNewLineOffsets(), offset);
		if (index < 0) {
			return -index;
		}
		return index + 1;
	}

	@Override
	public int getLineOffset(int lineNumber) {
		final int[] newLineOffsets = getNewLineOffsets();
		if (lineNumber < 1 || lineNumber - 2 >= newLineOffsets.length) {
			throw new IndexOutOfBoundsException();
		}
		return lineNumber == 1 ? 0 : newLineOffsets[lineNumber - 2] + 1;
	}

	@Override
	public int getColumnNumber(int offset) {
		int startOffset = getLineOffset(getLineNumber(offset));
		// count tabs as 4 chars, to show the same as eclipse and other IDE's
		int result = 1;
		for (int i = startOffset; i != offset; ++i) {
			result += (text.charAt(i) == '\t') ? 4 : 1;
		}
		
		return result;
	}
	
	@Override
	public ISourceRange newSourceRange(int offset, int endOffset) {
		if (offset < 0 || offset > endOffset || endOffset > text.length()) {
			throw new IndexOutOfBoundsException(
					"offset = " + offset + ", endOffset = " + endOffset + ", getLength() = " + getLength());
		}	
		
		// Create an object with a more useful toString() for easier debugging
		return new SourceRange(offset, endOffset);
	}

	protected int[] getNewLineOffsets() {
		int[] newLineOffsets = lazyNewLineOffsets.get();
		if (newLineOffsets == null) {
			lazyNewLineOffsets.compareAndSet(null, computeNewLineOffsets(text));
			newLineOffsets = lazyNewLineOffsets.get();
		}
		return newLineOffsets;
	}
	
	/**
	 * @param text
	 * @return number of new line characters in text
	 */
	static int countNumberOfNewLines(String text) {
		int nextLineStart = -1;
		for (int i = 0;; ++i) {
			nextLineStart = text.indexOf('\n', nextLineStart + 1);
			if (nextLineStart == -1) {
				return i;
			}
		}
	}
	
	/**
	 * @param text
	 * @return array with indices of all new line characters in the textt
	 */
	static int[] computeNewLineOffsets(String text) {
		final int[] offsets = new int[countNumberOfNewLines(text)];
		int nextLineStart = -1;
		for (int i = 0;; ++i) {
			nextLineStart = text.indexOf('\n', nextLineStart + 1);
			if (nextLineStart == -1) {
				return offsets;
			}
			offsets[i] = nextLineStart;
		}
	}
	
	
	class SourceRange implements ISourceRange {
		private final int begin;
		private final int end;

		SourceRange(int offset, int endOffset) {
			this.begin = offset;
			this.end = endOffset;
		}
		
		@Override
		public int offset() {
			return begin;
		}
		
		@Override
		public int endOffset() {
			return end;
		}
		
		@Override
		public String toString() {
			StringBuilder sb = new StringBuilder();
			sb.append("[");
			SourceDocumentLocationPrinter.appendTo(StringSourceDocument.this, this, sb);
			sb.append("]");
			return sb.toString();
		}
	}
}
