package de.uni_freiburg.informatik.ultimate.gui.preferencepages;

import java.util.StringTokenizer;

import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.swt.widgets.List;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.CorePreferenceInitializer;


public class LoggingToolsPreferencePage extends AbstractDetailsPreferencePage
		implements IWorkbenchPreferencePage {

	
	private ScopedPreferenceStore mPreferenceStore;

	public LoggingToolsPreferencePage() {
		mPreferenceStore = new ScopedPreferenceStore(InstanceScope.INSTANCE,
				CorePreferenceInitializer.PLUGINID);
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
				.getDefaultString(CorePreferenceInitializer.PREFID_TOOLDETAILS));
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
		return CorePreferenceInitializer.INVALID_TOOL_ENTRY;
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
				.getString(CorePreferenceInitializer.PREFID_TOOLDETAILS));
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
			buffer.append(CorePreferenceInitializer.VALUE_DELIMITER_LOGGING_PREF);
		}
		mPreferenceStore.setValue(CorePreferenceInitializer.PREFID_TOOLDETAILS, buffer
				.toString());
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.AbstractDetailsPreferencePage#getInfoContent(org.eclipse.swt.widgets.List)
	 */
	@Override
	protected String getInfoContent(List detailList) {
		return CorePreferenceInitializer.EMPTY_STRING;
	}

	@Override
	protected String[] getComboSupply() {
		return new String[0];
	}
	
	/**
	 * Converts ICorePreferenceStore.VALUE_DELIMITER_LOGGING_PREF delimited
	 * String to a String array.
	 */
	private static String[] convert(String preferenceValue) {
		StringTokenizer tokenizer = new StringTokenizer(preferenceValue,
				CorePreferenceInitializer.VALUE_DELIMITER_LOGGING_PREF);
		int tokenCount = tokenizer.countTokens();
		String[] elements = new String[tokenCount];
		for (int i = 0; i < tokenCount; i++) {
			elements[i] = tokenizer.nextToken();
		}

		return elements;
	}


}
