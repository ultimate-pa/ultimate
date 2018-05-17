/*
 * Copyright (C) 2008-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE BoogiePreprocessor plug-in.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogiePreprocessor plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogiePreprocessor plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BoogiePreprocessor plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.preferences;

import de.uni_freiburg.informatik.ultimate.boogie.preprocessor.Activator;
import de.uni_freiburg.informatik.ultimate.core.lib.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;

/**
 *
 * This class loads preference default values before they are needed
 *
 * contributes to ep: org.eclipse.core.runtime.preferences.initializer see the plugin.xml
 *
 * @author dietsch
 *
 */
public class PreferenceInitializer extends UltimatePreferenceInitializer {

	public static final String LABEL_SHOWALLANNOTATIONS = "Show all Annotations";
	public static final String LABEL_EMIT_BACKTRANSLATION_WARNINGS = "Show backtranslation warnings";
	public static final String LABEL_USE_SIMPLIFIER = "Simplify expressions";

	public PreferenceInitializer() {
		super(Activator.PLUGIN_ID, Activator.PLUGIN_NAME);
	}

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {

		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<>(LABEL_SHOWALLANNOTATIONS, false, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_EMIT_BACKTRANSLATION_WARNINGS, true, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_USE_SIMPLIFIER, false, PreferenceType.Boolean)

		};
	}
}
