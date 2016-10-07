package de.uni_freiburg.informatik.ultimate.deltadebugger.core.text;

public interface ISourceDocument {
	int getLength();
	
	String getText();
	String getText(int offset, int endOffset);
	String getText(ISourceRange location);
	
	int getNumberOfLines();
	int getLineOffset(int lineNumber);
	
	int getLineNumber(int offset);
	int getColumnNumber(int offset);
	
	ISourceRange newSourceRange(int offset, int endOffset);
}