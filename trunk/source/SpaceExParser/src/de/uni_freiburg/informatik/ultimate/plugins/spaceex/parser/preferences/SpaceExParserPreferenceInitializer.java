/*
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE SpaceExParser plug-in.
 * 
 * The ULTIMATE SpaceExParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE SpaceExParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SpaceExParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SpaceExParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE SpaceExParser plug-in grant you additional permission 
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.preferences;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.lib.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.Activator;

/**
 * SpaceEx Parser preferences.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class SpaceExParserPreferenceInitializer extends UltimatePreferenceInitializer {

	public static final String LABEL_LOAD_CONFIG_FILE_OF_SPACEEX_MODEL = "Load config file of corresponding SpaceEx model";
	public static final String LABEL_SPACEEX_CONFIG_FILE = "Use config file:";
	public static final String LABEL_CONFIG_FILE_EXPLANATION = "If no config file should be loaded automatically "
	        + "and no config file is specified, all occurring\nvariables are set to be unbounded initially and no "
	        + "error location is assumed.";

	private static final Boolean DEFAULT_LOAD_CONFIG_FILE_OF_SPACEEX_MODEL = true;

	/**
	 * Initializes the SpaceEx Parser preferences.
	 */
	public SpaceExParserPreferenceInitializer() {
		super(Activator.PLUGIN_ID, Activator.PLUGIN_NAME);
	}

	@Override
	protected BaseUltimatePreferenceItem[] initDefaultPreferences() {
		final List<BaseUltimatePreferenceItem> rtr = new ArrayList<>();

		rtr.add(new UltimatePreferenceItem<Boolean>(LABEL_LOAD_CONFIG_FILE_OF_SPACEEX_MODEL,
		        DEFAULT_LOAD_CONFIG_FILE_OF_SPACEEX_MODEL, PreferenceType.Boolean));

		rtr.add(new UltimatePreferenceItem<String>(LABEL_SPACEEX_CONFIG_FILE, "", PreferenceType.File));

		rtr.add(new UltimatePreferenceItem<String>(LABEL_CONFIG_FILE_EXPLANATION, null, PreferenceType.Label));

		return rtr.toArray(new BaseUltimatePreferenceItem[rtr.size()]);
	}
}
