package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.refactoring;

import java.util.HashMap;

public class StringMapper implements IStringMapper {

	private HashMap<String, String> mMapping;
	
	public StringMapper(String[] oldNames, String[] newNames) {
		mMapping = new HashMap<String, String>(oldNames.length);
		for (int i = 0; i < oldNames.length; ++i) {
			mMapping.put(oldNames[i], newNames[i]);
		}
	}
	
	@Override
	public String map(String oldVarName) {
		String newVarName = mMapping.get(oldVarName);
		if (newVarName == null)
			return oldVarName;
		return newVarName;
	}

}
