package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.preferences;

/**
 * All supported behaviors on an attempt to inline a (possibly) recursive procedure.
 * These are shown in the preferences dialog.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public enum BehaviorOnRecursion {
	
	SKIP("skip"),
	WARN_AND_SKIP("warn and skip"),
	ERROR_AND_ABORT("error and abort");

	private final String mDisplayName;
	
	private BehaviorOnRecursion(String displayName) {
		mDisplayName = displayName;
	}
	
	/*
	@Override
	public String toString() {
		return mDisplayName;
	}
	*/

}
