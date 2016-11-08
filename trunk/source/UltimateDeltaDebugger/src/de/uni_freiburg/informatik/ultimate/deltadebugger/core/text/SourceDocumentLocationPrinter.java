package de.uni_freiburg.informatik.ultimate.deltadebugger.core.text;

public final class SourceDocumentLocationPrinter {

	private SourceDocumentLocationPrinter() {
	}
	
	public static StringBuilder appendTo(final ISourceDocument document, final int offset, final int endOffset,
			final StringBuilder sb) {
		final int startingLineNumber = document.getLineNumber(offset);
		final int startingLineColumn = document.getColumnNumber(offset);
		sb.append("Line ").append(startingLineNumber).append(", Column ").append(startingLineColumn);
		if (offset == endOffset) {
			return sb;
		}

		final int endingLineNumber = document.getLineNumber(endOffset - 1);
		final int endingLineColumn = document.getColumnNumber(endOffset);
		if (startingLineNumber == endingLineNumber) {
			sb.append(" - ").append(endingLineColumn);
			return sb;
		}

		sb.append(" - ").append("Line ").append(endingLineNumber).append(", Column ").append(endingLineColumn);
		return sb;
	}

	public static StringBuilder appendTo(final ISourceDocument document, final ISourceRange range,
			final StringBuilder sb) {
		return appendTo(document, range.offset(), range.endOffset(), sb);
	}

	public static String makeString(final ISourceDocument document, final int offset, final int endOffset) {
		return appendTo(document, offset, endOffset, new StringBuilder()).toString();
	}

	public static String makeString(final ISourceDocument document, final ISourceRange range) {
		return makeString(document, range.offset(), range.endOffset());
	}

}
