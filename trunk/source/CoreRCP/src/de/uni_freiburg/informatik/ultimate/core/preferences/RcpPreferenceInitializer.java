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

import de.uni_freiburg.informatik.ultimate.core.model.IController;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;

/**
 * UltimatePreferenceInitializer implements an AbstractPreferenceInitializer for Ultimate. It initializes the default
 * values for preferences and provides access to the preferences for Ultimate.
 * 
 * Clients should derive from this class and contribute to the extension point
 * org.eclipse.core.runtime.preferences.initializer (see the plugin.xml of CoreRCP for an example)
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * 
 */
public abstract class RcpPreferenceInitializer extends AbstractPreferenceInitializer implements IPreferenceInitializer {

	private final BaseUltimatePreferenceItem[] mPreferenceDescriptors;
	private final RcpPreferenceProvider mPreferenceStore;
	private final String mPluginId;
	private final String mPreferencePageTitle;

	/**
	 * @param pluginId
	 *            The Id of the plugin to which this {@link IPreferenceInitializer} belongs.
	 * @param preferencePageTitle
	 *            A human-readable title for the preference page or preference section that can be used by
	 *            {@link IController} plugins to generate descriptions.
	 * 
	 */
	protected RcpPreferenceInitializer(final String pluginId, final String preferencePageTitle) {
		mPreferenceDescriptors = initDefaultPreferences();
		mPreferenceStore = new RcpPreferenceProvider(pluginId);
		mPluginId = pluginId;
		mPreferencePageTitle = preferencePageTitle;
	}

	@Override
	public void initializeDefaultPreferences() {
		final IEclipsePreferences defaults = mPreferenceStore.getDefaultEclipsePreferences();
		RcpPreferenceBinder.initializePreferences(defaults, mPreferenceDescriptors);
	}

	@Override
	public BaseUltimatePreferenceItem[] getPreferenceItems() {
		return mPreferenceDescriptors;
	}

	@Override
	public String getPluginID() {
		return mPluginId;
	}

	@Override
	public String getPreferenceTitle() {
		return mPreferencePageTitle;
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
}
