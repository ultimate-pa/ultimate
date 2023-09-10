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

import de.uni_freiburg.informatik.ultimate.core.lib.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.chcsolver.Activator;

/**
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 */
public class ChcSolverPreferenceInitializer extends UltimatePreferenceInitializer {

	public enum SolverBackend {
		ELDARICA, Z3, TREEAUTOMIZER, GOLEM
	}

	public static final String LABEL_CHC_BACKEND = "CHC solver backend";
	private static final SolverBackend DEF_CHC_BACKEND = SolverBackend.ELDARICA;

	public static final String LABEL_PRODUCE_MODEL = "Produce CHC model if query is SAT";
	private static final boolean DEF_PRODUCE_MODEL = true;

	public static final String LABEL_PRODUCE_DERIVATION = "Produce derivation if query is UNSAT";
	private static final boolean DEF_PRODUCE_DERIVATION = true;

	public static final String LABEL_PRODUCE_UNSAT_CORES = "Produce UNSAT core if query is UNSAT";
	private static final boolean DEF_PRODUCE_UNSAT_CORES = false;

	public ChcSolverPreferenceInitializer() {
		super(Activator.PLUGIN_ID, Activator.PLUGIN_NAME);
	}

	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<>(LABEL_CHC_BACKEND, DEF_CHC_BACKEND, PreferenceType.Combo,
						SolverBackend.values()),
				new UltimatePreferenceItem<>(LABEL_PRODUCE_MODEL, DEF_PRODUCE_MODEL, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_PRODUCE_DERIVATION, DEF_PRODUCE_DERIVATION, PreferenceType.Boolean),
				new UltimatePreferenceItem<>(LABEL_PRODUCE_UNSAT_CORES, DEF_PRODUCE_UNSAT_CORES,
						PreferenceType.Boolean) };
	}

	public static IPreferenceProvider getPreferenceProvider(final IUltimateServiceProvider services) {
		return services.getPreferenceProvider(Activator.PLUGIN_ID);
	}
}
