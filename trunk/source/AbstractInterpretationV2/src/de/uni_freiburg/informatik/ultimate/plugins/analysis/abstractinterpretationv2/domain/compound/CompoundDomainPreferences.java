/*
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.compound;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItemContainer;

/**
 * Preferences for the compound domain.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class CompoundDomainPreferences {

	public static final String LABEL_DESCRIPTION_CHOOSE_ABSTRACT_DOMAINS =
			"Select the abstract domains that should be part of the compound domain.";

	public static final String LABEL_USE_EMPTY_DOMAIN = "Empty Domain";
	public static final String LABEL_USE_SIGN_DOMAIN = "Sign Domain";
	public static final String LABEL_USE_CONGRUENCE_DOMAIN = "Congruence Domain";
	public static final String LABEL_USE_INTERVAL_DOMAIN = "Interval Domain";
	public static final String LABEL_USE_OCTAGON_DOMAIN = "Octagon Domain";
	public static final String LABEL_USE_EXP_DOMAIN = "Explicit value domain";
	private static final boolean DEF_USE_EXP_DOMAIN = false;

	public static final boolean DEF_USE_EMPTY_DOMAIN = false;
	public static final boolean DEF_USE_SIGN_DOMAIN = false;
	public static final boolean DEF_USE_CONGRUENCE_DOMAIN = true;
	public static final boolean DEF_USE_INTERVAL_DOMAIN = true;
	public static final boolean DEF_USE_OCTAGON_DOMAIN = true;

	public static final String LABEL_CREATE_ASSUMPTIONS = "Create assumptions of other states before post";
	public static final String LABEL_USE_SMT_SOLVER_FEASIBILITY =
			"Check feasibility of abstract posts with an SMT solver";
	public static final String LABEL_SIMPLIFY_ASSUMPTIONS = "Simplify assumptions before abstract post";
	public static final boolean DEF_CREATE_ASSUMPTIONS = false;
	public static final boolean DEF_USE_SMT_SOLVER = false;
	public static final boolean DEF_SIMPLIFY_ASSUMPTIONS = false;

	public static List<BaseUltimatePreferenceItem> getPreferences() {
		final List<BaseUltimatePreferenceItem> returnList = new ArrayList<>();

		final UltimatePreferenceItemContainer compoundContainer =
				new UltimatePreferenceItemContainer("Compound Domain");

		compoundContainer.addItem(new UltimatePreferenceItem<String>(LABEL_DESCRIPTION_CHOOSE_ABSTRACT_DOMAINS, null,
				PreferenceType.Label));
		compoundContainer.addItems(addAbstractDomains());

		compoundContainer.addItem(new UltimatePreferenceItem<String>("", null, PreferenceType.Label));
		compoundContainer.addItem(
				new UltimatePreferenceItem<>(LABEL_CREATE_ASSUMPTIONS, DEF_CREATE_ASSUMPTIONS, PreferenceType.Boolean));
		compoundContainer.addItem(new UltimatePreferenceItem<>(LABEL_SIMPLIFY_ASSUMPTIONS, DEF_SIMPLIFY_ASSUMPTIONS,
				PreferenceType.Boolean));
		compoundContainer.addItem(new UltimatePreferenceItem<>(LABEL_USE_SMT_SOLVER_FEASIBILITY, DEF_USE_SMT_SOLVER,
				PreferenceType.Boolean));

		returnList.add(compoundContainer);
		return returnList;
	}

	private static List<UltimatePreferenceItem<?>> addAbstractDomains() {
		final List<UltimatePreferenceItem<?>> abstractDomains = new ArrayList<>();

		abstractDomains.add(
				new UltimatePreferenceItem<>(LABEL_USE_EMPTY_DOMAIN, DEF_USE_EMPTY_DOMAIN, PreferenceType.Boolean));
		abstractDomains
				.add(new UltimatePreferenceItem<>(LABEL_USE_SIGN_DOMAIN, DEF_USE_SIGN_DOMAIN, PreferenceType.Boolean));
		abstractDomains.add(new UltimatePreferenceItem<>(LABEL_USE_CONGRUENCE_DOMAIN, DEF_USE_CONGRUENCE_DOMAIN,
				PreferenceType.Boolean));
		abstractDomains.add(new UltimatePreferenceItem<>(LABEL_USE_INTERVAL_DOMAIN, DEF_USE_INTERVAL_DOMAIN,
				PreferenceType.Boolean));
		abstractDomains.add(
				new UltimatePreferenceItem<>(LABEL_USE_OCTAGON_DOMAIN, DEF_USE_OCTAGON_DOMAIN, PreferenceType.Boolean));
		abstractDomains
				.add(new UltimatePreferenceItem<>(LABEL_USE_EXP_DOMAIN, DEF_USE_EXP_DOMAIN, PreferenceType.Boolean));
		return abstractDomains;
	}
}
