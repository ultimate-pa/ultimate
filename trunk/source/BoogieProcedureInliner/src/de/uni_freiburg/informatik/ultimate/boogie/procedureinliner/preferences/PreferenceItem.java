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

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.Activator;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType;
import static de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType.Boolean;

/**
 * All items from the plug-in's preferences.
 * The current set preferences can be queried on each item.
 * Each item contains the label name, default value and list choices (if available).
 * The preferences dialog should show the items in the order of this enum.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public enum PreferenceItem {

	LABEL___ENABLE_INLINING_FOR("Enable inlining for ..."),
	INLINE_UNIMPLEMENTED("calls to unimplemented procedures", true, Boolean),
	INLINE_IMPLEMENTED("calls to implemented procedures", true, Boolean),

	LABEL___IGNORE_CALLS("\nIgnore calls ..."),
	IGNORE_CALL_FORALL("with \'forall\' modifier *", true, PreferenceType.Boolean),
	IGNORE_WITH_FREE_REQUIRES("to procedures with \'free requires\' specifications *", true, Boolean),
	IGNORE_POLYMORPHIC("to and inside polymorphic procedures *", true, Boolean),
	IGNORE_RECURSIVE("to recursive procedures *", true, Boolean),
	IGNORE_MULTIPLE_CALLED("to procedures, called more than once", false, Boolean),
	NOTE___UNSUPPORTED("* attempt to inline these will cause an exception"),

	LABEL___USER_LIST("\nUser list (procedure ids, separated by whitespace)"),
	USER_LIST("User list", "", PreferenceType.MultilineString),
	USER_LIST_TYPE("User list type", UserListType.BLACKLIST_RESTRICT, PreferenceType.Combo, UserListType.values()),
	NOTE___TYPE_DESCRIPTION(UserListType.description()),
	
	LABEL___ENTRY_PROCEDURE_HANDLING("\nEntry procedure handling"),
	PROCESS_ONLY_ENTRY_AND_RE_ENTRY_PROCEDURES("Process only entry and re-entry procedures", true, Boolean),
	ENTRY_PROCEDURES("Entry procedures (ids, separated by whitespace)", "ULTIMATE.start", PreferenceType.String),
	ENTRY_PROCEDURE_FALLBACK("Fallback: Process everything, if an entry procedure doesn't exist", true, Boolean),
	ELIMINATE_DEAD_CODE("Eliminate dead code after inlining", true, Boolean); // see CallGraphNodeLabel

	protected final String mName;
	protected final Object mDefaultValue;
	protected final PreferenceType mType;
	protected final Object[] mChoices;

	private PreferenceItem(String name) {
		this(name, null, PreferenceType.Label, null);
	}
	
	private PreferenceItem(String name, Object defaultValue, PreferenceType type) {
		this(name, defaultValue, type, null);
	}
	
	private PreferenceItem(String name, Object defaultValue, PreferenceType type, Object[] choices) {
		mName = name;
		mDefaultValue = defaultValue;
		mType = type;
		mChoices = choices;
	}
	
	public String getName() {
		return mName;
	}
	
	public PreferenceType getType() {
		return mType;
	}
	
	public Object getDefaultValue() {
		return mDefaultValue;
	}
	
	public Boolean getBooleanValue() {
		return new UltimatePreferenceStore(Activator.PLUGIN_ID).getBoolean(mName);
	}
	
	public String getStringValue() {
		return new UltimatePreferenceStore(Activator.PLUGIN_ID).getString(mName);
	}
	
	/** @return Tokens from {@link #getStringValue()}, which where separated by whitespace. */
	public List<String> getStringValueTokens() {
		String trimmedStringValue = getStringValue().trim();
		if (trimmedStringValue.isEmpty()) {
			return Collections.emptyList();
		} else {
			return Arrays.asList(trimmedStringValue.split("\\s+"));			
		}
	}
	
	public UserListType getUserListTypeValue() {
		return new UltimatePreferenceStore(Activator.PLUGIN_ID).getEnum(mName, UserListType.class);
	}

	public UltimatePreferenceItem<?> newUltimatePreferenceItem() {
		return new UltimatePreferenceItem<Object>(mName, mDefaultValue, mType, mChoices);
	}
}
