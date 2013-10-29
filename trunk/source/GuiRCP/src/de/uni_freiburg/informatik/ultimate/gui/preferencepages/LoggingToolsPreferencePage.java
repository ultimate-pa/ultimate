package de.uni_freiburg.informatik.ultimate.gui.preferencepages;

import java.util.StringTokenizer;

import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.swt.widgets.List;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.constants.PreferenceConstants;

public class LoggingToolsPreferencePage extends AbstractDetailsPreferencePage
		implements IWorkbenchPreferencePage {

	
	private ScopedPreferenceStore mPreferenceStore;

	public LoggingToolsPreferencePage() {
		mPreferenceStore = new ScopedPreferenceStore(InstanceScope.INSTANCE,
				PreferenceConstants.PLUGINID);
	}
	
	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.AbstractDetailsPreferencePage
	 * #getCorrectPreferenceStore()
	 */
	@Override
	protected IPreferenceStore getCorrectPreferenceStore() {
		return mPreferenceStore;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.AbstractDetailsPreferencePage
	 * #getDefaults()
	 */
	@Override
	protected String[] getDefaults() {
		return convert(mPreferenceStore
				.getDefaultString(PreferenceConstants.PREFID_TOOLDETAILS));
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.AbstractDetailsPreferencePage
	 * #getInvalidEntryMessage()
	 */
	@Override
	protected String getInvalidEntryMessage() {
		return PreferenceConstants.INVALID_TOOL_ENTRY;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.AbstractDetailsPreferencePage
	 * #getPreferenceAsStringArray()
	 */
	@Override
	protected String[] getPreferenceAsStringArray() {
		return convert(mPreferenceStore
				.getString(PreferenceConstants.PREFID_TOOLDETAILS));
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.AbstractDetailsPreferencePage
	 * #setThePreference(java.lang.String[])
	 */
	@Override
	protected void setThePreference(String[] items) {
		StringBuffer buffer = new StringBuffer();
		for (int i = 0; i < items.length; i++) {
			buffer.append(items[i]);
			buffer.append(PreferenceConstants.VALUE_DELIMITER_LOGGING_PREF);
		}
		mPreferenceStore.setValue(PreferenceConstants.PREFID_TOOLDETAILS, buffer
				.toString());
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.AbstractDetailsPreferencePage#getInfoContent(org.eclipse.swt.widgets.List)
	 */
	@Override
	protected String getInfoContent(List detailList) {
		return PreferenceConstants.EMPTY_STRING;
	}

	@Override
	protected String[] getComboSupply() {
		return new String[0];
	}
	
	/**
	 * Converts IPreferenceConstants.VALUE_DELIMITER_LOGGING_PREF delimited
	 * String to a String array.
	 */
	private static String[] convert(String preferenceValue) {
		StringTokenizer tokenizer = new StringTokenizer(preferenceValue,
				PreferenceConstants.VALUE_DELIMITER_LOGGING_PREF);
		int tokenCount = tokenizer.countTokens();
		String[] elements = new String[tokenCount];
		for (int i = 0; i < tokenCount; i++) {
			elements[i] = tokenizer.nextToken();
		}

		return elements;
	}


}
