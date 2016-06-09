/*
 * Copyright (C) 2015 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BoogieProcedureInliner plug-in.
 * 
 * The ULTIMATE BoogieProcedureInliner plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BoogieProcedureInliner plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogieProcedureInliner plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogieProcedureInliner plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE BoogieProcedureInliner plug-in grant you additional permission 
 * to convey the resulting work.
 */
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
		final StringBuilder sb = new StringBuilder();
		sb.append("There are 3 sets of calls:\n");
		sb.append(indent + "ALL: All calls from the program\n");
		sb.append(indent + "PREF: Calls, selected by the other preferences\n");
		sb.append(indent + "LIST: Calls to procedures from the user list\n");
		sb.append("The user list type defines, how the are mixed:");
		for (final UserListType type : UserListType.values()) {
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
