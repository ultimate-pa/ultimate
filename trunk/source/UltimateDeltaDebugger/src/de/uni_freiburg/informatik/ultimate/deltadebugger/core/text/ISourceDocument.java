package de.uni_freiburg.informatik.ultimate.deltadebugger.core.text;

public interface ISourceDocument {
	int getColumnNumber(int offset);

	int getLength();

	int getLineNumber(int offset);

	int getLineOffset(int lineNumber);

	int getNumberOfLines();

	String getText();

	String getText(int offset, int endOffset);

	String getText(ISourceRange location);

	ISourceRange newSourceRange(int offset, int endOffset);
}