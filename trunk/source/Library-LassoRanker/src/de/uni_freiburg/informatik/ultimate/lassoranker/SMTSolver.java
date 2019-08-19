/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker;

import java.io.IOException;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.logic.Script;

/**
 * Static class that manages SMT-Solver related things.
 *
 * @author Jan Leike
 */
public class SMTSolver {

	/**
	 * Create a new solver instance with the preferences given
	 *
	 * @param preferences
	 *            the preferences for creating the solver
	 * @param constraintsName
	 *            name of the constraints whose satisfiability is checked
	 * @param services
	 * @return the new solver instance
	 * @throws IOException
	 */
	public static Script newScript(final ILassoRankerPreferences preferences, final String constraintsName,
			final IUltimateServiceProvider services) {
		final SolverSettings settings = preferences
				.getSolverConstructionSettings(preferences.getBaseNameOfDumpedScript() + "+" + constraintsName);
		final Script script = SolverBuilder.buildScript(services, settings);

		// Set options
		script.setOption(":produce-models", true);
		if (preferences.isAnnotateTerms()) {
			script.setOption(":produce-unsat-cores", true);
		}
		return script;

	}

}
