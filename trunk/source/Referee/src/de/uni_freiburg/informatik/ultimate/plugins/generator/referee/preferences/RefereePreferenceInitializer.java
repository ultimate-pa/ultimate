/*
 * Copyright (C) 2018 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE Referee plug-in.
 *
 * The ULTIMATE Referee plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Referee plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Referee plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Referee plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Referee plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.referee.preferences;

import de.uni_freiburg.informatik.ultimate.core.lib.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.plugins.generator.referee.Activator;

/**
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class RefereePreferenceInitializer extends UltimatePreferenceInitializer {

	public static final String LABEL_ALLOW_LOOPS_WITHOUT_ANNOTATION = "Allow loops without annotation";

	public static final boolean DEF_ALLOW_LOOPS_WITHOUT_ANNOTATION = false;

	public RefereePreferenceInitializer() {
		super(Activator.PLUGIN_ID, "Referee");
	}

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] { new UltimatePreferenceItem<>(LABEL_ALLOW_LOOPS_WITHOUT_ANNOTATION,
				DEF_ALLOW_LOOPS_WITHOUT_ANNOTATION, PreferenceType.Boolean), };
	};
}
