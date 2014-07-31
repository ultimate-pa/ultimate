package de.uni_freiburg.informatik.ultimate.gui.preferencepages;

import java.util.StringTokenizer;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.UltimateCore;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.CorePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.ep.ExtensionPoints;

import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.swt.widgets.List;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

public class LoggingSpecificPluginsPreferencePage extends AbstractDetailsPreferencePage {

	private ScopedPreferenceStore mPreferenceStore;

	public LoggingSpecificPluginsPreferencePage() {
		mPreferenceStore = new ScopedPreferenceStore(InstanceScope.INSTANCE, CorePreferenceInitializer.PLUGINID);
	}

	@Override
	protected IPreferenceStore getCorrectPreferenceStore() {
		return mPreferenceStore;
	}

	@Override
	protected String[] getDefaults() {
		return convert(mPreferenceStore.getDefaultString(CorePreferenceInitializer.PREFID_DETAILS));
	}

	@Override
	protected String getInvalidEntryMessage() {
		return CorePreferenceInitializer.INVALID_ENTRY;
	}

	@Override
	protected String[] getPreferenceAsStringArray() {
		return convert(mPreferenceStore.getString(CorePreferenceInitializer.PREFID_DETAILS));
	}

	@Override
	protected void setThePreference(String[] items) {
		StringBuffer buffer = new StringBuffer();
		for (int i = 0; i < items.length; i++) {
			buffer.append(items[i]);
			buffer.append(CorePreferenceInitializer.VALUE_DELIMITER_LOGGING_PREF);
		}
		mPreferenceStore.setValue(CorePreferenceInitializer.PREFID_DETAILS, buffer.toString());
	}

	@Override
	protected String getInfoContent(List detailList) {
		String response = CorePreferenceInitializer.ALL_PLUGINS_PRESENT;
		StringBuffer invalidPluginIds = new StringBuffer();
		invalidPluginIds.append(CorePreferenceInitializer.PLUGINS_NOT_PRESENT);
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
		// hack until this class is auto-generated
		String[] plugins = UltimateCore.getPluginNames();
		boolean retVal = false;
		for (String iTool : plugins) {
			if (iTool.equals(pluginId)) {
				retVal = true;
			}
		}
		return retVal;
	}

	@Override
	protected String[] getComboSupply() {
		// hack until this class is auto-generated
		String[] plugins = UltimateCore.getPluginNames();

		if (plugins == null) {
			return new String[0];
		}

		String[] return_list = new String[plugins.length];

		for (int i = 0; i < plugins.length; i++) {
			return_list[i] = plugins[i] + "=<LOG LEVEL>";
		}
		return return_list;
	}

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
