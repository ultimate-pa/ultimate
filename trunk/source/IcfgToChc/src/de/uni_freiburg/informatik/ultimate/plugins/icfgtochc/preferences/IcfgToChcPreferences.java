/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent.ConcurrencyMode;

public class IcfgToChcPreferences {
	private final IPreferenceProvider mPrefs;

	public enum SpecMode {
		ASSERT_VIOLATIONS, POSTCONDITION
	}

	public IcfgToChcPreferences(final IPreferenceProvider prefs) {
		mPrefs = prefs;
	}

	public ConcurrencyMode concurrencyMode() {
		return mPrefs.getEnum(IcfgToChcPreferenceInitializer.LABEL_CONCURRENCY_MODE, ConcurrencyMode.class);
	}

	public boolean hasPreconditions() {
		return mPrefs.getBoolean(IcfgToChcPreferenceInitializer.LABEL_HAS_PRECONDITION);
	}

	public SpecMode specMode() {
		return mPrefs.getEnum(IcfgToChcPreferenceInitializer.LABEL_SPEC_MODE, SpecMode.class);
	}

	public int getThreadModularProofLevel() {
		return mPrefs.getInt(IcfgToChcPreferenceInitializer.LABEL_THREADMODULAR_LEVEL);
	}

	public boolean explicitLocations() {
		return mPrefs.getBoolean(IcfgToChcPreferenceInitializer.LABEL_EXPLICIT_LOCATIONS);
	}

	public boolean useLiptonReduction() {
		return mPrefs.getBoolean(IcfgToChcPreferenceInitializer.LABEL_LIPTON_REDUCTION);
	}

	public boolean useSleepSets() {
		return mPrefs.getBoolean(IcfgToChcPreferenceInitializer.LABEL_SLEEP_SET_REDUCTION);
	}

	public boolean breakPreferenceOrderSymmetry() {
		return mPrefs.getBoolean(IcfgToChcPreferenceInitializer.DESC_BREAK_PREFORDER_SYMMETRY);
	}

	public boolean explicitSleep() {
		return mPrefs.getBoolean(IcfgToChcPreferenceInitializer.LABEL_EXPLICIT_SLEEP);
	}
}
