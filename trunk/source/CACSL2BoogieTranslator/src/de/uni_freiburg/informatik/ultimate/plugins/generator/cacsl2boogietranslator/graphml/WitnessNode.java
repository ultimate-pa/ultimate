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
	private final boolean mIsSink;

	WitnessNode(long currentNodeId, boolean isEntry, boolean isError,boolean isSink) {
		mIsEntry = isEntry;
		mIsError = isError;
		mId = "N" + String.valueOf(currentNodeId);
		mIsSink = isSink;
	}

	public boolean isEntry() {
		return mIsEntry;
	}
	
	public boolean isError(){
		return mIsError;
	}
	
	public boolean isSink(){
		return mIsSink;
	}

	public String getName() {
		return mId;
	}

}
