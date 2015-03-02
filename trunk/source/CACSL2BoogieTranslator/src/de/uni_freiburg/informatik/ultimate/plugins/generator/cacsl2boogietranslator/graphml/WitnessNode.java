package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.graphml;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class WitnessNode {
	private final boolean mIsEntry;
	private final String mId;
	private final boolean mIsError;

	WitnessNode(long currentNodeId, boolean isEntry, boolean isError) {
		mIsEntry = isEntry;
		mIsError = isError;
		mId = "N" + String.valueOf(currentNodeId);
	}

	public boolean isEntry() {
		return mIsEntry;
	}
	
	public boolean isError(){
		return mIsError;
	}

	public String getName() {
		return mId;
	}

}
