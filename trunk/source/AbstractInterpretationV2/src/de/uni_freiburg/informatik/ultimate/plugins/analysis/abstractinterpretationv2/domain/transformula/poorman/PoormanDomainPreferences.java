/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.poorman;

import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItemContainer;

/**
 * Preferences for the {@link PoormanAbstractState}.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class PoormanDomainPreferences {

	public static final String LABEL_USE_STRONGMAN = "Use Strongman";
	private static final boolean DEF_USE_STRONGMAN = false;
	private static final String DESC_USE_STRONGMAN =
			"Use SP to calculate post and then abstract the result instead of abstracting the transformula";

	public static List<BaseUltimatePreferenceItem> getPreferences() {
		final UltimatePreferenceItemContainer poormanContainer = new UltimatePreferenceItemContainer("Poorman Domain");
		poormanContainer.addItem(new UltimatePreferenceItem<String>("", null, PreferenceType.Label));
		poormanContainer.addItem(new UltimatePreferenceItem<>(LABEL_USE_STRONGMAN, DEF_USE_STRONGMAN,
				DESC_USE_STRONGMAN, PreferenceType.Boolean));
		return Collections.singletonList(poormanContainer);
	}

}
