package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation;

import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.result.Check;

public class ACSLLocation extends CACSLLocation {

	private static final long serialVersionUID = -4361747376994862578L;
	private final ACSLNode mNode;

	ACSLLocation(ACSLNode acslNode, Check checkedSpec, boolean ignoreDuringBacktranslation) {
		super(checkedSpec, ignoreDuringBacktranslation);
		mNode = acslNode;
	}

	/**
	 * @return the acslNode
	 */
	public ACSLNode getNode() {
		return mNode;
	}

	@Override
	public String getFileName() {
		if (mNode != null) {
			return mNode.getFileName();
		}
		return null;
	}

	@Override
	public int getStartLine() {
		if (mNode != null) {
			return mNode.getStartingLineNumber();
		}
		return -1;
	}

	@Override
	public int getEndLine() {
		if (mNode != null) {
			return mNode.getEndingLineNumber();
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

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		if (mNode != null) {
			sb.append("ACSL: ");
			sb.append(mNode.toString());
		}
		return sb.toString();
	}

}
