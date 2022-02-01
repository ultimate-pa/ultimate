/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.lassoranker.variables.InequalityConverter.NlaHandling;

/**
 * The {@link DefaultLassoRankerPreferences} contain an implementaton of {@link ILassoRankerPreferences} that represent
 * the default values of the preferences.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Jan Leike
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class DefaultLassoRankerPreferences implements ILassoRankerPreferences {

	@Override
	public boolean isComputeIntegralHull() {
		return false;
	}

	@Override
	public boolean isEnablePartitioneer() {
		return true;
	}

	@Override
	public boolean isAnnotateTerms() {
		return false;
	}

	@Override
	public boolean isExternalSolver() {
		return true;
	}

	@Override
	public String getExternalSolverCommand() {
		return "z3 -smt2 -in SMTLIB2_COMPLIANT=true";
	}

	@Override
	public boolean isDumpSmtSolverScript() {
		return false;
	}

	@Override
	public String getPathOfDumpedScript() {
		return ".";
	}

	@Override
	public String getBaseNameOfDumpedScript() {
		return "LassoRankerScript";
	}

	@Override
	public boolean isOverapproximateArrayIndexConnection() {
		return false;
	}

	@Override
	public NlaHandling getNlaHandling() {
		return NlaHandling.EXCEPTION;
	}

	@Override
	public boolean isUseOldMapElimination() {
		return false;
	}

	@Override
	public boolean isMapElimAddInequalities() {
		return false;
	}

	@Override
	public boolean isMapElimOnlyTrivialImplicationsIndexAssignment() {
		return true;
	}

	@Override
	public boolean isMapElimOnlyTrivialImplicationsArrayWrite() {
		return false;
	}

	@Override
	public boolean isMapElimOnlyIndicesInFormula() {
		return true;
	}

	@Override
	public boolean isFakeNonIncrementalScript() {
		return false;
	}
}