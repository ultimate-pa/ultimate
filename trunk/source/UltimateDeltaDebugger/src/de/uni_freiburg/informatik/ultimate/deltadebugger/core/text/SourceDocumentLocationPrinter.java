package de.uni_freiburg.informatik.ultimate.deltadebugger.core.text;

public class SourceDocumentLocationPrinter {

	private SourceDocumentLocationPrinter() {
	}

	public static String makeString(ISourceDocument document, ISourceRange range) {
		return makeString(document, range.offset(), range.endOffset());
	}

	public static String makeString(ISourceDocument document, int offset, int endOffset) {
		return appendTo(document, offset, endOffset, new StringBuilder()).toString();
	}

	public static StringBuilder appendTo(ISourceDocument document, ISourceRange range, StringBuilder sb) {
		return appendTo(document, range.offset(), range.endOffset(), sb);
	}

	public static StringBuilder appendTo(ISourceDocument document, int offset, int endOffset, StringBuilder sb) {
		int startingLineNumber = document.getLineNumber(offset);
		int startingLineColumn = document.getColumnNumber(offset);
		sb.append("Line ").append(startingLineNumber).append(", Column ").append(startingLineColumn);
		if (offset == endOffset) {
			return sb;
		}

		int endingLineNumber = document.getLineNumber(endOffset - 1);
		int endingLineColumn = document.getColumnNumber(endOffset);
		if (startingLineNumber == endingLineNumber) {
			sb.append(" - ").append(endingLineColumn);
			return sb;
		}

		sb.append(" - ").append("Line ").append(endingLineNumber).append(", Column ").append(endingLineColumn);
		return sb;
	}
}
