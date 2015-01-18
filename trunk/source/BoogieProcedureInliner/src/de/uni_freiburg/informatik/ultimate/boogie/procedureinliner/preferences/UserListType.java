package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.preferences;

/**
 * Supported usages of the user list inside the preferences.
 * These are shown in the preferences dialog.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public enum UserListType {

	DISABLED("Disabled"),
	BLACKLIST_RESTRICT("Blacklist restrict - Use preferences above, but never inline listed procedures"),
	BLACKLIST_ONLY("Blacklist only - Ignore preferences above and inline all unlisted procedures"),
	WHITELIST_EXTEND("Whitelist extend - Use preferences above, but always inline listed procedures"),
	WHITELIST_RESTRICT("Whitelist restrict- Use preferences above, but never inline unlisted procedures"),
	WHITELIST_ONLY("Whitelist only - Ignore preferences above and inline listed procedures only");

	private final String mDisplayName;
	
	private UserListType(String displayName) {
		mDisplayName = displayName;
	}
	
	/*
	@Override
	public String toString() {
		return mDisplayName;
	}
	*/
}
