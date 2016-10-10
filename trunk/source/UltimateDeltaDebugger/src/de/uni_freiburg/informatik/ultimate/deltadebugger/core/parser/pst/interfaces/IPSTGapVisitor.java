package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces;

public interface IPSTGapVisitor extends IPSTVisitor {
	public int visitGap(int offset, int endOffset);
}