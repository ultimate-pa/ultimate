/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Core.
 * 
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Core grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.preferences;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.osgi.service.prefs.BackingStoreException;

import de.uni_freiburg.informatik.ultimate.core.model.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;

/**
 * UltimatePreferenceInitializer implements an AbstractPreferenceInitializer for Ultimate. It initializes the default
 * values for preferences and provides access to the preferences for Ultimate.
 * 
 * Clients should derive from this class and contribute to the extension point
 * org.eclipse.core.runtime.preferences.initializer (see the plugin.xml of CoreRCP for an example)
 * 
 * @author dietsch
 * 
 */
public abstract class UltimatePreferenceInitializer extends AbstractPreferenceInitializer implements IPreferenceInitializer {

	private final BaseUltimatePreferenceItem[] mPreferenceDescriptors;
	private final UltimatePreferenceStore mPreferenceStore;

	public UltimatePreferenceInitializer() {
		mPreferenceDescriptors = initDefaultPreferences();
		mPreferenceStore = new UltimatePreferenceStore(getPlugID());
	}

	@Override
	public void initializeDefaultPreferences() {
		IEclipsePreferences defaults = mPreferenceStore.getDefaultEclipsePreferences();
		initializePreferences(defaults);
	}

	@Override
	public void resetDefaults() {
		initializePreferences(mPreferenceStore.getEclipsePreferences());
	}

	private void initializePreferences(IEclipsePreferences prefs) {
		try {
			prefs.flush();
			prefs.sync();
		} catch (BackingStoreException e) {
			e.printStackTrace();
		}

		for (BaseUltimatePreferenceItem prefItem : BaseUltimatePreferenceItem
		        .constructFlattenedList(mPreferenceDescriptors)) {
			if (prefItem instanceof UltimatePreferenceItem) {
				UltimatePreferenceItem<?> item = (UltimatePreferenceItem<?>) prefItem;
				String label = item.getLabel();
				Object value = item.getDefaultValue();
				prefs.remove(label);

				switch (item.getType()) {
				case Boolean:
					prefs.putBoolean(label, (Boolean) value);
					break;
				case Integer:
					prefs.putInt(label, (Integer) value);
					break;
				case Directory:
				case String:
				case MultilineString:
				case Combo:
				case Radio:
				case Path:
				case File:
				case Color:
					prefs.put(label, value.toString());
					break;
				case Label:
					// A Label is not really a preference; its just nice for
					// automatic generation of preference pages
					break;
				default:
					throw new UnsupportedOperationException(
					        "You need to implement the new enum type \"" + item.getType() + "\" here");
				}
			}
		}
		try {
			prefs.flush();
			prefs.sync();
		} catch (BackingStoreException e) {
			e.printStackTrace();
		}
	}

	@Override
	public BaseUltimatePreferenceItem[] getDefaultPreferences() {
		return mPreferenceDescriptors;
	}

	/**
	 * Should return an array of UltimatePreferenceItem describing the preferences of the implementing plugin. Will be
	 * called once during construction.
	 * 
	 * The index prescribes the position in the preference pages.
	 * 
	 * Note: Clients should only set default preference values for their own plugin.
	 * 
	 * @return
	 */
	protected abstract BaseUltimatePreferenceItem[] initDefaultPreferences();

	/**
	 * Should return the ID of the implementing plugin.
	 * 
	 * @return
	 */
	protected abstract String getPlugID();

	@Override
	public abstract String getPreferencePageTitle();

}
