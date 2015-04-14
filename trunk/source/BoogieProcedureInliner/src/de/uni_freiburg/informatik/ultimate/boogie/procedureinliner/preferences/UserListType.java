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
	DISABLED("PREF"),
	/** Inline the set of procedures: PREF \ LIST. */
	BLACKLIST_RESTRICT("PREF \\ LIST"),
	/** Inline the set of procedures: ALL \ LIST. */
	BLACKLIST_ONLY("ALL \\ LIST"),
	/** Inline the set of procedures: PREF u LIST. */
	WHITELIST_EXTEND("PREF u LIST"),
	/** Inline the set of procedures: PREF n LIST. */
	WHITELIST_RESTRICT("PREF n LIST"),
	/** Inline the set of procedures: LIST. */
	WHITELIST_ONLY("LIST");

	public static String description() {
		final String indent = "    ";
		StringBuilder sb = new StringBuilder();
		sb.append("There are 3 sets of calls:\n");
		sb.append(indent + "ALL: All calls from the program\n");
		sb.append(indent + "PREF: Calls, selected by the other preferences\n");
		sb.append(indent + "LIST: Calls to procedures from the user list\n");
		sb.append("The user list type defines, how the are mixed:");
		for (UserListType type : UserListType.values()) {
			sb.append("\n" + indent);
			sb.append(type);
			sb.append(" = ");
			sb.append(type.getDescription());
		}
		return sb.toString();
	}

	// ---
	
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
