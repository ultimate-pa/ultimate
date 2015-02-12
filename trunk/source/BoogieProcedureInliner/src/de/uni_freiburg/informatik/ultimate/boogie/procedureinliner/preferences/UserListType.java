package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.preferences;

/**
 * Supported usages of the user list inside the preferences.
 * These are shown in the preferences dialog.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public enum UserListType {

	DISABLED("Disabled"),
	BLACKLIST_RESTRICT("Use preferences above, but never inline listed procedures"),
	BLACKLIST_ONLY("Ignore preferences above and inline all unlisted procedures"),
	WHITELIST_EXTEND("Use preferences above, but always inline listed procedures"),
	WHITELIST_RESTRICT("Use preferences above, but never inline unlisted procedures"),
	WHITELIST_ONLY("Ignore preferences above and inline listed procedures only");

	private final String mDisplayName;

	private UserListType(String displayName) {
		mDisplayName = displayName;
	}
	
	/** @return The user list type is {@link #BLACKLIST_ONLY} or {@link #WHITELIST_ONLY} */
	public boolean isOnly() {
		return this == BLACKLIST_ONLY || this == WHITELIST_ONLY;
	}

}
