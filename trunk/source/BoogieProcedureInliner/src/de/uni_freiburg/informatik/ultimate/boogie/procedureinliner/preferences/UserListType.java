package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.preferences;

/**
 * Supported usages of the user list inside the preferences.
 * 
 * Basically, these are some set operations (like union, intersection and so on). There are 3 sets:
 * - ALL: All Procedures from the program
 * - PREF: Procedures selected by the other preferences
 * - LIST: Procedures from the user list
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public enum UserListType {

	/** Inline the set of procedures: PREF. */
	DISABLED("Disabled"),
	/** Inline the set of procedures: PREF - LIST. */
	BLACKLIST_RESTRICT("Use preferences above, but never inline listed procedures"),
	/** Inline the set of procedures: ALL - LIST. */
	BLACKLIST_ONLY("Ignore preferences above and inline all UNlisted procedures"),
	/** Inline the set of procedures: PREF \/ LIST. */
	WHITELIST_EXTEND("Use preferences above, but always inline listed procedures"),
	/** Inline the set of procedures: PREF /\ LIST. */
	WHITELIST_RESTRICT("Use preferences above, but never inline UNlisted procedures"),
	/** Inline the set of procedures: LIST. */
	WHITELIST_ONLY("Ignore preferences above and inline listed procedures only");

	private final String mDescription;

	private UserListType(String displayName) {
		mDescription = displayName;
	}
	
	/** @return The user list type is {@link #BLACKLIST_ONLY} or {@link #WHITELIST_ONLY} */
	public boolean isOnly() {
		return this == BLACKLIST_ONLY || this == WHITELIST_ONLY;
	}
	
	public String getDescription() {
		return mDescription;
	}

}
