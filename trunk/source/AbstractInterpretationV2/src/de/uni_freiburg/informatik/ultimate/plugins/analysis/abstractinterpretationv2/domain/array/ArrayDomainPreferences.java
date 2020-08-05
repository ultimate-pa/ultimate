/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.array;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItemContainer;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.compound.CompoundDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.congruence.CongruenceDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon.OctagonDomain;

/**
 * Preferences for the array domain.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class ArrayDomainPreferences {

	public static final String LABEL_ABSTRACT_DOMAIN = "Underlying domain";
	private static final String[] VALUES_ABSTRACT_DOMAIN =
			new String[] { IntervalDomain.class.getSimpleName(), OctagonDomain.class.getSimpleName(),
					CongruenceDomain.class.getSimpleName(), CompoundDomain.class.getSimpleName() };
	private static final String DEF_ABSTRACT_DOMAIN = CompoundDomain.class.getSimpleName();
	private static final String DESC_ABSTRACT_DOMAIN =
			"Select the abstract domain that provides predicates to the array domain";

	public static List<BaseUltimatePreferenceItem> getPreferences() {
		final List<BaseUltimatePreferenceItem> returnList = new ArrayList<>();
		final UltimatePreferenceItemContainer container = new UltimatePreferenceItemContainer("Array Domain");
		container.addItem(new UltimatePreferenceItem<>(LABEL_ABSTRACT_DOMAIN, DEF_ABSTRACT_DOMAIN, DESC_ABSTRACT_DOMAIN,
				PreferenceType.Combo, VALUES_ABSTRACT_DOMAIN));
		returnList.add(container);
		return returnList;
	}

}
