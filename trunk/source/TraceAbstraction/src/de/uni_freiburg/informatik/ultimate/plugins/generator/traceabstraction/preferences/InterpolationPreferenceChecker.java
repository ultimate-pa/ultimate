/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.RcfgPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;

/**
 * Provides a method that checks compatibility of interpolation related preferences.
 *
 * @author Matthias Heizmann
 *
 */
public class InterpolationPreferenceChecker {

	public static void check(final String pluginName, final InterpolationTechnique interpolation,
			final IUltimateServiceProvider services) {
		final SolverMode currentSolverMode = services.getPreferenceProvider(Activator.PLUGIN_ID)
				.getEnum(RcfgPreferenceInitializer.LABEL_SOLVER, SolverMode.class);
		final Set<SolverMode> legalSolverSettings = new HashSet<>();
		switch (interpolation) {
		case Craig_TreeInterpolation:
		case Craig_NestedInterpolation:
			legalSolverSettings.add(SolverMode.Internal_SMTInterpol);
			legalSolverSettings.add(SolverMode.Internal_SMTInterpol_NoArrayInterpol);
			legalSolverSettings.add(SolverMode.External_PrincessInterpolationMode);
			legalSolverSettings.add(SolverMode.External_SMTInterpolInterpolationMode);
			legalSolverSettings.add(SolverMode.External_Z3InterpolationMode);
			break;
		case BackwardPredicates:
		case FPandBP:
		case ForwardPredicates:
		case PathInvariants:
			legalSolverSettings.add(SolverMode.Internal_SMTInterpol);
			legalSolverSettings.add(SolverMode.Internal_SMTInterpol_NoArrayInterpol);
			legalSolverSettings.add(SolverMode.External_ModelsAndUnsatCoreMode);
			break;
		default:
			throw new AssertionError("unknown option " + interpolation);
		}
		if (!legalSolverSettings.contains(currentSolverMode)) {
			final String errorMessage = "Incompatible preferences. You want to use " + interpolation + " in the "
					+ pluginName + " plugin. This requires that " + RcfgPreferenceInitializer.LABEL_SOLVER + " in the "
					+ Activator.PLUGIN_ID + " has one of the following values. " + legalSolverSettings.toString();
			throw new UnsupportedOperationException(errorMessage);
		}
	}
}
