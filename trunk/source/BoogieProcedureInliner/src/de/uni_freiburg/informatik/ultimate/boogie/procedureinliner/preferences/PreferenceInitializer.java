package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.preferences;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.Activator;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;

/**
 * Initializes the preferences using {@link PreferenceItem}.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class PreferenceInitializer extends UltimatePreferenceInitializer {

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		List<UltimatePreferenceItem<?>> prefItems = new ArrayList<>();
		for (PreferenceItem item : PreferenceItem.values()) {
			prefItems.add(item.newUltimatePreferenceItem());
		}
		return prefItems.toArray(new UltimatePreferenceItem<?>[prefItems.size()]);
	}

	@Override
	protected String getPlugID() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public String getPreferencePageTitle() {
		return Activator.PLUGIN_NAME;
	}

}
