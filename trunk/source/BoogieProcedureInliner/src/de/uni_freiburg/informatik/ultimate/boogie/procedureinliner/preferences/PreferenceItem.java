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
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphNodeLabel;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

/**
 * All items from the plug-in's preferences. The current set preferences can be queried on each item. Each item contains
 * the label name, default value and list choices (if available). The preferences dialog should show the items in the
 * order of this enum.
 *
 * @author schaetzc@informatik.uni-freiburg.de
 */
public enum PreferenceItem {

	LABEL_ENABLE_INLINING_FOR("───  I n l i n e  ───"),

	INLINE_UNIMPLEMENTED("Inline calls to unimplemented procedures",
			"Inline calls to unimplemented procedures.",
			Boolean.FALSE, PreferenceType.Boolean),

	INLINE_IMPLEMENTED("Inline calls to implemented procedures",
			"When to inline calls to implemented procedures.",
			EnableWhen.ALWAYS, PreferenceType.Combo, EnableWhen.values()),

	LABEL_IGNORE_CALLS("───  I g n o r e  ───"),

	IGNORE_CALL_FORALL("Ignore calls with \'forall\' modifier",
			"Do not inline calls with forall-star modifier (attempting to inline these can cause exceptions).",
			Boolean.TRUE, PreferenceType.Boolean),

	IGNORE_WITH_FREE_REQUIRES("Ignore calls to procedures with \'free requires\' specifications",
			"Do not inline calls to procedures with free-requires specification "
					+ "(attempting to inline these can cause exceptions).",
			Boolean.TRUE, PreferenceType.Boolean),

	IGNORE_POLYMORPHIC("Ignore calls to and inside polymorphic procedures",
			"Do not inline calls to and inside polymorphic procedures (attempting to inline these can cause exceptions).",
			Boolean.TRUE, PreferenceType.Boolean),

	IGNORE_RECURSIVE("Ignore calls to recursive procedures",
			"Do not inline calls to recursive procedures (attempting to inline these can cause exceptions).",
			Boolean.TRUE,
			PreferenceType.Boolean),

	IGNORE_MULTIPLE_CALLED("Ignore calls to procedures called more than once",
			"When to ignore calls to procedures called more than once.",
			EnableWhen.NEVER, PreferenceType.Combo, EnableWhen.values()),

	LABEL_USER_LIST("───  U s e r   L i s t  ───"),

	USER_LIST_TYPE("User list type",
			UserListType.description(),
			UserListType.BLACKLIST_RESTRICT, PreferenceType.Combo, UserListType.values()),

	USER_LIST("User list",
			"Procedure IDs/names separated by whitespace",
			"", PreferenceType.MultilineString),

	LABEL_ENTRY_PROCEDURE_HANDLING("───  E n t r y   P o i n t s  ───"),

	PROCESS_ONLY_ENTRY_AND_RE_ENTRY_PROCEDURES("Process only entry and re-entry procedures",
			null, Boolean.TRUE, PreferenceType.Boolean),

	ENTRY_PROCEDURES("Entry procedures",
			"Procedure IDs/names separated by whitespace.",
			"ULTIMATE.start", PreferenceType.String),

	ENTRY_PROCEDURE_FALLBACK("Fallback to processing everything",
			"If no entry procedure can be found, just treat every procedure as potential entry procedure.",
			Boolean.TRUE, PreferenceType.Boolean),

	/** @see CallGraphNodeLabel#isDead() */
	ELIMINATE_DEAD_CODE("Remove dead code",
			"Eliminate dead code after inlining.",
			Boolean.TRUE, PreferenceType.Boolean);

	private final String mName;
	private final Object mDefaultValue;
	private final PreferenceType mType;
	private final Object[] mChoices;
	private final String mDescription;

	PreferenceItem(final String name) {
		this(name, null, null, PreferenceType.Label, null);
	}

	PreferenceItem(final String name, final String description, final Object defaultValue,
			final PreferenceType type) {
		this(name, description, defaultValue, type, null);
	}

	PreferenceItem(final String name, final String description, final Object defaultValue,
			final PreferenceType type, final Object[] choices) {
		mName = name;
		mDefaultValue = defaultValue;
		mType = type;
		mChoices = choices;
		mDescription = description;
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

	public String getDescription() {
		return mDescription;
	}

	/** @return Tokens from {@link #getStringValue()}, which where separated by whitespace. */
	public List<String> getStringValueTokens(final IUltimateServiceProvider services) {
		final String trimmedStringValue = services.getPreferenceProvider(Activator.PLUGIN_ID).getString(mName).trim();
		if (trimmedStringValue.isEmpty()) {
			return Collections.emptyList();
		} else {
			return Arrays.asList(trimmedStringValue.split("\\s+"));
		}
	}

	public UltimatePreferenceItem<?> newUltimatePreferenceItem() {
		return new UltimatePreferenceItem<>(mName, mDefaultValue, mType, mDescription, false, mChoices, null);
	}
}
