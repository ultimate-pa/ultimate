/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * Copyright (C) 2013-2015 Vincent Langenfeld (langenfv@informatik.uni-freiburg.de)
 *
 * This file is part of the ULTIMATE LTL2Aut plug-in.
 *
 * The ULTIMATE LTL2Aut plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LTL2Aut plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LTL2Aut plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LTL2Aut plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LTL2Aut plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.ltl2aut.preferences;

import de.uni_freiburg.informatik.ultimate.core.lib.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.ltl2aut.Activator;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class PreferenceInitializer extends UltimatePreferenceInitializer {

	/*
	 * labels for the different preferencess
	 */
	public static final String LABEL_TOOLLOCATION = "Path to LTL*BA executable (LTL2BA, LTL3BA)";
	public static final String LABEL_TOOLARGUMENT = "Command line string ($1 will be replaced with the property)";
	public static final String LABEL_PROPERTYFROMFILE = "Read property from file";
	public static final String LABEL_PPROPERTY = "Property to check";
	public static final String LABEL_OPTIMIZE_SBE = "Use small block encoding";
	public static final String LABEL_OPTIMIZE_REWRITEASSUME = "Rewrite not equals during small block encoding";

	/*
	 * default values for the different preferences
	 */
	public static final String DEF_TOOLLOCATION = "ltl2ba";
	public static final String DEF_TOOLARGUMENT = "!($1)";
	public static final boolean DEF_PROPERTYFROMFILE = false;
	public static final String DEF_PPROPERTY = "[] a \n a: x > 42";

	public PreferenceInitializer() {
		super(Activator.PLUGIN_ID, Activator.PLUGIN_NAME);
	}

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<>(LABEL_TOOLLOCATION, DEF_TOOLLOCATION, PreferenceType.String),
				new UltimatePreferenceItem<>(LABEL_TOOLARGUMENT, DEF_TOOLARGUMENT, PreferenceType.String),
				new UltimatePreferenceItem<>(LABEL_PROPERTYFROMFILE, DEF_PROPERTYFROMFILE,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_PPROPERTY, DEF_PPROPERTY, PreferenceType.MultilineString),
				new UltimatePreferenceItem<>(LABEL_OPTIMIZE_SBE, false, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_OPTIMIZE_REWRITEASSUME, false, PreferenceType.Boolean), };
	}
}
