/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE DebugGUI plug-in.
 * 
 * The ULTIMATE DebugGUI plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE DebugGUI plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE DebugGUI plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE DebugGUI plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE DebugGUI plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.gui.preferencepages;

import java.util.StringTokenizer;

import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.swt.widgets.List;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.CorePreferenceInitializer;

public class LoggingExternalToolsPreferencePage extends AbstractDetailsPreferencePage
		implements IWorkbenchPreferencePage {

	private final ScopedPreferenceStore mPreferenceStore;

	public LoggingExternalToolsPreferencePage() {
		mPreferenceStore = new ScopedPreferenceStore(InstanceScope.INSTANCE, CorePreferenceInitializer.PLUGINID);
	}

	@Override
	protected IPreferenceStore getCorrectPreferenceStore() {
		return mPreferenceStore;
	}

	@Override
	protected String[] getDefaults() {
		return convert(mPreferenceStore.getDefaultString(CorePreferenceInitializer.LABEL_LOGLEVEL_EXTERNAL_TOOL_SPECIFIC));
	}

	@Override
	protected String getInvalidEntryMessage() {
		return CorePreferenceInitializer.INVALID_TOOL_ENTRY;
	}

	@Override
	protected String[] getPreferenceAsStringArray() {
		return convert(mPreferenceStore.getString(CorePreferenceInitializer.LABEL_LOGLEVEL_EXTERNAL_TOOL_SPECIFIC));
	}

	@Override
	protected void setThePreference(String[] items) {
		final StringBuffer buffer = new StringBuffer();
		for (int i = 0; i < items.length; i++) {
			buffer.append(items[i]);
			buffer.append(CorePreferenceInitializer.VALUE_DELIMITER_LOGGING_PREF);
		}
		mPreferenceStore.setValue(CorePreferenceInitializer.LABEL_LOGLEVEL_EXTERNAL_TOOL_SPECIFIC, buffer.toString());
	}

	@Override
	protected String getInfoContent(List detailList) {
		return CorePreferenceInitializer.EMPTY_STRING;
	}

	@Override
	protected String[] getComboSupply() {
		return new String[0];
	}

	/**
	 * Converts ICorePreferenceStore.VALUE_DELIMITER_LOGGING_PREF delimited String to a String array.
	 */
	private static String[] convert(String preferenceValue) {
		final StringTokenizer tokenizer = new StringTokenizer(preferenceValue,
				CorePreferenceInitializer.VALUE_DELIMITER_LOGGING_PREF);
		final int tokenCount = tokenizer.countTokens();
		final String[] elements = new String[tokenCount];
		for (int i = 0; i < tokenCount; i++) {
			elements[i] = tokenizer.nextToken();
		}

		return elements;
	}

}
