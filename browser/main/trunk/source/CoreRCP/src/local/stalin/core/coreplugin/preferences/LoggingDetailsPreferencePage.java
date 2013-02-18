package local.stalin.core.coreplugin.preferences;

import local.stalin.core.api.StalinServices;
import local.stalin.ep.interfaces.ITool;

import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.swt.widgets.List;

public class LoggingDetailsPreferencePage extends AbstractDetailsPreferencePage {

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * local.stalin.core.coreplugin.preferences.AbstractDetailsPreferencePage
	 * #getCorrectPreferenceStore()
	 */
	@Override
	protected IPreferenceStore getCorrectPreferenceStore() {
		return LoggingDetailsPreferenceWrapper.getPrefStore();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * local.stalin.core.coreplugin.preferences.AbstractDetailsPreferencePage
	 * #getDefaults()
	 */
	@Override
	protected String[] getDefaults() {
		return LoggingDetailsPreferenceWrapper
				.getDefaultLoggingDetailsPreference();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * local.stalin.core.coreplugin.preferences.AbstractDetailsPreferencePage
	 * #getInvalidEntryMessage()
	 */
	@Override
	protected String getInvalidEntryMessage() {
		return IPreferenceConstants.INVALID_ENTRY;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * local.stalin.core.coreplugin.preferences.AbstractDetailsPreferencePage
	 * #getPreferenceAsStringArray()
	 */
	@Override
	protected String[] getPreferenceAsStringArray() {
		return LoggingDetailsPreferenceWrapper.getLoggingDetailsPreference();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * local.stalin.core.coreplugin.preferences.AbstractDetailsPreferencePage
	 * #setThePreference(java.lang.String[])
	 */
	@Override
	protected void setThePreference(String[] items) {
		LoggingDetailsPreferenceWrapper.setLoggingDeatilsPreference(items);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * local.stalin.core.coreplugin.preferences.AbstractDetailsPreferencePage
	 * #getInfoContent()
	 */
	@Override
	protected String getInfoContent(List detailList) {
		String response = IPreferenceConstants.ALL_PLUGINS_PRESENT;
		StringBuffer invalidPluginIds = new StringBuffer();
		invalidPluginIds.append(IPreferenceConstants.PLUGINS_NOT_PRESENT);
		boolean error = false;
		for (String line : detailList.getItems()) {
			String pluginId = line.substring(0, line.lastIndexOf("="));
			if (!isActivePluginId(pluginId)) {
				error = true;
				invalidPluginIds.append(pluginId + "\n");
			}
		}
		if (error) {
			return invalidPluginIds.toString();
		}
		return response;
	}

	private boolean isActivePluginId(String pluginId) {
		java.util.List<ITool> tools = StalinServices.getInstance()
				.getActiveTools();
		boolean retVal = false;
		for (ITool iTool : tools) {
			if (iTool.getPluginID().equals(pluginId)) {
				retVal = true;
			}
		}
		return retVal;
	}

	@Override
	protected String[] getComboSupply() {
		java.util.List<ITool> plugins = StalinServices.getInstance().getActiveTools();
		String [] return_list = new String[plugins.size()];
		for (int i = 0; i < plugins.size(); i++) {
			return_list[i] = plugins.get(i).getPluginID()+"=<DEBUG LEVEL>";
		}
		return return_list;
	}
}
