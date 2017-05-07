package de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.preferences;

public class PreferenceGroup {
	
	protected final int mId;
	protected final String mVariableInfix;
	
	public PreferenceGroup(final int id, final String infix) {
		mId = id;
		mVariableInfix = (infix != null) ? infix : "";
	}
	
	public String getVariableInfix() {
		return mVariableInfix;
	}
	
	public int getId() {
		return mId;
	}
}
