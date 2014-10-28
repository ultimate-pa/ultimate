package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.graphml;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class WitnessNode {
	private boolean mIsEntry;
	private final String mId;

	WitnessNode(boolean isEntry, long currentNodeId) {
		mIsEntry = isEntry;
		mId = "N" + String.valueOf(currentNodeId);
	}

	public boolean isEntry() {
		return mIsEntry;
	}

	public String getName() {
		return mId;
	}

}
