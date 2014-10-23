package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation;

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.result.Check;

public class CLocation extends CACSLLocation {

	private static final long serialVersionUID = -7497131349540138810L;
	private final IASTNode mNode;

	protected CLocation(IASTNode node, Check checkedSpec, boolean ignoreDuringBacktranslation) {
		super(checkedSpec, ignoreDuringBacktranslation);
		mNode = node;
	}

	@Override
	public String getFileName() {
		if (mNode != null) {
			return mNode.getFileLocation().getFileName();
		}
		return null;
	}

	@Override
	public int getStartLine() {
		if (mNode != null) {
			return mNode.getFileLocation().getStartingLineNumber();
		}
		return -1;
	}

	@Override
	public int getEndLine() {
		if (mNode != null) {
			return mNode.getFileLocation().getEndingLineNumber();
		}
		return -1;
	}

	@Override
	public int getStartColumn() {
		return -1;
	}

	@Override
	public int getEndColumn() {
		return -1;
	}

	@Override
	public boolean isLoop() {
		return false;
	}

	public IASTNode getNode() {
		return mNode;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		if (mNode != null) {
			sb.append("C: ");
			sb.append(mNode.getRawSignature());
			sb.append(" ");
		}

		return sb.toString();
	}

}
