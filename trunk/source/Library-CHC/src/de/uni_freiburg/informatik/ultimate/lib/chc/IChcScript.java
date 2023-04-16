/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE CHC Library.
 *
 * The ULTIMATE CHC Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CHC Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CHC Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CHC Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CHC Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.chc;

import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;

/**
 * A common interface to CHC solvers.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 */
public interface IChcScript {
	/**
	 * The script which should be used to build terms for this solver.
	 *
	 * No other commands should be invoked on this script.
	 *
	 * @return
	 */
	Script getScript();

	/**
	 * Try to solve the given system of Horn clauses.
	 *
	 * @param system
	 *            The list of Horn clauses forming the CHC system
	 * @return
	 */
	LBool solve(List<HornClause> system);

	/**
	 * Determines if the solver can output a model for {@code SAT} queries.
	 *
	 * @return {@code true} if producing models is generally supported.
	 */
	boolean supportsModelProduction();

	/**
	 * Enable or disable model production for future calls to {@link #solve(List)}.
	 *
	 * @param enable
	 *            {@code true} to enable model production, {@code false} to disable it.
	 */
	void produceModels(boolean enable);

	/**
	 * If the last invocation of {@link #solve(List)} returned {@code SAT}, returns a satisfying model.
	 *
	 * Model production must have been enabled via {@link #produceModels(boolean)} prior to the call to
	 * {@link #solve(List)}.
	 *
	 * @return
	 */
	Model getModel();

	/**
	 * Determines if the solver can output a derivation for {@code UNSAT} queries.
	 *
	 * @return if producing derivations is generally supported.
	 */
	boolean supportsDerivationProduction();

	/**
	 * Enable or disable derivation production for future calls to {@link #solve(List)}.
	 *
	 * @param enable
	 *            {@code true} to enable derivation production, {@code false} to disable it.
	 */
	void produceDerivations(boolean enable);

	/**
	 * If the last invocation of {@link #solve(List)} returned {@code UNSAT}, returns a derivation proving
	 * unsatisfiability.
	 *
	 * Derivation production must have been enabled via {@link #produceDerivations(boolean)} prior to the call to
	 * {@link #solve(List)}.
	 *
	 * @return
	 */
	Derivation getDerivation();

	/**
	 * Determines if the solver can output an unsatisfiable core for {@code UNSAT} queries.
	 *
	 * @return if producing UNSAT cores is generally supported.
	 */
	boolean supportsUnsatCores();

	/**
	 * Enable or disable UNSAT core production for future calls to {@link #solve(List)}.
	 *
	 * @param enable
	 *            {@code true} to enable UNSAT core production, {@code false} to disable it.
	 */
	void produceUnsatCores(boolean enable);

	/**
	 * If the last invocation of {@link #solve(List)} returned {@code UNSAT}, returns an unsatisfiable core.
	 *
	 * UNSAT core production must have been enabled via {@link #produceUnsatCores(boolean)} prior to the call to
	 * {@link #solve(List)}.
	 *
	 * @return
	 */
	Set<HornClause> getUnsatCore();
}
