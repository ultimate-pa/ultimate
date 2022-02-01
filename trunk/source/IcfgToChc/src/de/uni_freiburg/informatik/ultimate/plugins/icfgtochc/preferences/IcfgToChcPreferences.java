/*
 * Copyright (C) 2019 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgToChc plug-in.
 *
 * The ULTIMATE IcfgToChc plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgToChc plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgToChc plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgToChc plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgToChc plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.preferences;

import de.uni_freiburg.informatik.ultimate.core.lib.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.Activator;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class IcfgToChcPreferences extends UltimatePreferenceInitializer {

//	public static final String LABEL_TRANSFORMATION_TYPE = "TransformationType";
//	private static final String DESC_TRANSFORMATION_TYPE = "";

	/**
	 * Default constructor.
	 */
	public IcfgToChcPreferences() {
		super(Activator.PLUGIN_ID, Activator.PLUGIN_NAME);
	}

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] {

//				new UltimatePreferenceItem<>(LABEL_TRANSFORMATION_TYPE,
//						TransformationTestType.LOOP_ACCELERATION_EXAMPLE, DESC_TRANSFORMATION_TYPE,
//						PreferenceType.Combo, TransformationTestType.values()),

		};
	}

	public static IPreferenceProvider getPreferenceProvider(final IUltimateServiceProvider services) {
		return services.getPreferenceProvider(Activator.PLUGIN_ID);
	}
}
