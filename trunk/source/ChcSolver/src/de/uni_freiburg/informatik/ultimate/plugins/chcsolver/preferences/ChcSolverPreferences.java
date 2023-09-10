/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE ChcSolver plug-in.
 *
 * The ULTIMATE ChcSolver plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ChcSolver plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ChcSolver plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ChcSolver plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ChcSolver plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.chcsolver.preferences;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.chcsolver.preferences.ChcSolverPreferenceInitializer.SolverBackend;

public class ChcSolverPreferences {

	private final IPreferenceProvider mPrefs;

	public ChcSolverPreferences(final IPreferenceProvider prefs) {
		mPrefs = prefs;
	}

	public SolverBackend getBackend() {
		return mPrefs.getEnum(ChcSolverPreferenceInitializer.LABEL_CHC_BACKEND, SolverBackend.class);
	}

	public boolean produceModels() {
		return mPrefs.getBoolean(ChcSolverPreferenceInitializer.LABEL_PRODUCE_MODEL);
	}

	public boolean produceDerivation() {
		return mPrefs.getBoolean(ChcSolverPreferenceInitializer.LABEL_PRODUCE_DERIVATION);
	}

	public boolean produceUnsatCore() {
		return mPrefs.getBoolean(ChcSolverPreferenceInitializer.LABEL_PRODUCE_UNSAT_CORES);
	}
}
