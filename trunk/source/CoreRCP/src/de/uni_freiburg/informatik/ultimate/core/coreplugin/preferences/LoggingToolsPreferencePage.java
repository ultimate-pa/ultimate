package de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences;

import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.swt.widgets.List;
import org.eclipse.ui.IWorkbenchPreferencePage;

public class LoggingToolsPreferencePage extends AbstractDetailsPreferencePage
		implements IWorkbenchPreferencePage {

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.AbstractDetailsPreferencePage
	 * #getCorrectPreferenceStore()
	 */
	@Override
	protected IPreferenceStore getCorrectPreferenceStore() {
		return LoggingToolDetailsPreferenceWrapper.getPrefStore();
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
		return LoggingToolDetailsPreferenceWrapper
				.getDefaultLoggingToolDetailsPreference();
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
		return IPreferenceConstants.INVALID_TOOL_ENTRY;
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
		return LoggingToolDetailsPreferenceWrapper
				.getLoggingToolDetailsPreference();
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
		LoggingToolDetailsPreferenceWrapper
				.setLoggingToolDeatilsPreference(items);
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.AbstractDetailsPreferencePage#getInfoContent(org.eclipse.swt.widgets.List)
	 */
	@Override
	protected String getInfoContent(List detailList) {
		return IPreferenceConstants.EMPTY_STRING;
	}

	@Override
	protected String[] getComboSupply() {
		return new String[0];
	}


}
