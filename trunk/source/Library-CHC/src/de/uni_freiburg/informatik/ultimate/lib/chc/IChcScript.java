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
import java.util.Optional;
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
	 */
	Script getScript();

	/**
	 * Try to solve the given system of Horn clauses. If the system cannot be solved, {@code UNKNOWN} is returned.
	 *
	 * @param symbolTable
	 *            A symbol table describing the predicates and other symbols used by the given CHC system
	 * @param system
	 *            The list of Horn clauses forming the CHC system
	 * @return the satisfiability of the system
	 */
	LBool solve(HcSymbolTable symbolTable, List<HornClause> system);

	/**
	 * Try to solve the given system of Horn clauses, within the given time.
	 *
	 * @param symbolTable
	 *            A symbol table describing the predicates and other symbols used by the given CHC system
	 * @param system
	 *            The list of Horn clauses forming the CHC system
	 * @param timeout
	 *            The maximum time to be used for solving the system, in milliseconds. The timeout must be greater than
	 *            zero. If the timeout is reached before a solution is found, {@code UNKNOWN} is returned.
	 * @return the satisfiability of the system
	 */
	LBool solve(HcSymbolTable symbolTable, List<HornClause> system, long timeout);

	/**
	 * Determines if the solver class implements retrieval of models for {@link #solve(HcSymbolTable, List)} calls that
	 * returned {@code SAT}.
	 *
	 * If this method returns {@code false}, then any call to {@link #produceModels(boolean)} or {@link #getModel()}
	 * will throw an {@link UnsupportedOperationException}.
	 *
	 * If this method returns {@code true}, individual calls to {@link #getModel()} may still return nothing, e.g.
	 * depending on the constraint logic used by the solved CHC system, or various characteristics of the underlying
	 * solver.
	 *
	 * @return {@code true} if producing models is generally supported.
	 */
	boolean supportsModelProduction();

	/**
	 * Enable or disable model production for future calls to {@link #solve(HcSymbolTable, List)}.
	 *
	 * @param enable
	 *            {@code true} to enable model production, {@code false} to disable it.
	 */
	void produceModels(boolean enable);

	/**
	 * If the last invocation of {@link #solve(HcSymbolTable, List)} returned {@code SAT}, tries to retrieve and return
	 * a satisfying model. If no model can be retrieved, returns an empty {@link Optional}.
	 *
	 * Model production must have been enabled via {@link #produceModels(boolean)} prior to the call to
	 * {@link #solve(HcSymbolTable, List)}.
	 */
	Optional<Model> getModel();

	/**
	 * Determines if the solver class implements retrieval of derivations for {@link #solve(HcSymbolTable, List)} calls
	 * that returned {@code UNSAT}.
	 *
	 * If this method returns {@code false}, then any call to {@link #produceDerivations(boolean)} or
	 * {@link #getDerivation()} will throw an {@link UnsupportedOperationException}.
	 *
	 * If this method returns {@code true}, individual calls to {@link #getDerivation()} may still return nothing, e.g.
	 * depending on the constraint logic used by the solved CHC system, or various characteristics of the underlying
	 * solver.
	 *
	 * @return if producing derivations is generally supported.
	 */
	boolean supportsDerivationProduction();

	/**
	 * Enable or disable derivation production for future calls to {@link #solve(HcSymbolTable, List)}.
	 *
	 * @param enable
	 *            {@code true} to enable derivation production, {@code false} to disable it.
	 */
	void produceDerivations(boolean enable);

	/**
	 * If the last invocation of {@link #solve(HcSymbolTable, List)} returned {@code UNSAT}, tries to retrieve and
	 * return a derivation proving unsatisfiability. If no derivation can be retrieved, returns an empty
	 * {@link Optional}.
	 *
	 * Derivation production must have been enabled via {@link #produceDerivations(boolean)} prior to the call to
	 * {@link #solve(HcSymbolTable, List)}.
	 */
	Optional<Derivation> getDerivation();

	/**
	 * Determines if the solver class implements retrieval of unsatisfiable cores for
	 * {@link #solve(HcSymbolTable, List)} calls that returned {@code UNSAT}.
	 *
	 * If this method returns {@code false}, then any call to {@link #produceUnsatCores(boolean)} or
	 * {@link #getUnsatCore()} will throw an {@link UnsupportedOperationException}.
	 *
	 * If this method returns {@code true}, individual calls to {@link #getUnsatCore()} may still return nothing, e.g.
	 * depending on the constraint logic used by the solved CHC system, or various characteristics of the underlying
	 * solver.
	 *
	 * @return if producing UNSAT cores is generally supported.
	 */
	boolean supportsUnsatCores();

	/**
	 * Enable or disable UNSAT core production for future calls to {@link #solve(HcSymbolTable, List)}.
	 *
	 * @param enable
	 *            {@code true} to enable UNSAT core production, {@code false} to disable it.
	 */
	void produceUnsatCores(boolean enable);

	/**
	 * If the last invocation of {@link #solve(HcSymbolTable, List)} returned {@code UNSAT}, tries to retrieve and
	 * return an unsatisfiable core. If no UNSAT core can be retrieved, returns an empty {@link Optional}.
	 *
	 * UNSAT core production must have been enabled via {@link #produceUnsatCores(boolean)} prior to the call to
	 * {@link #solve(HcSymbolTable, List)}.
	 */
	Optional<Set<HornClause>> getUnsatCore();
}
