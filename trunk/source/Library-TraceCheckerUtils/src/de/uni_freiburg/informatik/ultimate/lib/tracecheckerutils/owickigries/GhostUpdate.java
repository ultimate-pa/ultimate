/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;

/**
 * Encapsulates information about the updates performed on ghost variables during a transition.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public final class GhostUpdate {
	private final Map<IProgramVar, Term> mUpdates;

	/**
	 * Creates a new instance.
	 *
	 * @param updates
	 *            A map from ghost variables to the terms which are assigned to them. The terms may again use ghost
	 *            variables, as well as program variables. The assignments are performed concurrently, i.e., an
	 *            occurrence of a ghost variable in one of these terms always refers to the ghost variable's value
	 *            before any update has occurred.
	 */
	public GhostUpdate(final Map<IProgramVar, Term> updates) {
		mUpdates = updates;

		assert !mUpdates.isEmpty() : "empty ghost updates are redundant";
		assert !mUpdates.containsKey(null) : "invalid ghost update for null";
		assert !mUpdates.values().contains(null) : "cannot update ghost variable to null";
		assert mUpdates.entrySet().stream().noneMatch(
				e -> e.getValue().equals(e.getKey().getTermVariable())) : "trivial ghost updates are redundant";
	}

	/**
	 * The set of variables which are assigned.
	 */
	public Set<IProgramVar> getAssignedVariables() {
		return Collections.unmodifiableSet(mUpdates.keySet());
	}

	/**
	 * Determines if the given ghost variable is updated.
	 *
	 * @param variable
	 *            the ghost variable to check
	 * @return true if this instance may update the value of the ghost variable, false otherwise
	 */
	public boolean containsUpdateFor(final IProgramVar variable) {
		return mUpdates.containsKey(variable);
	}

	/**
	 * Retrieves the term which is assigned to the given ghost variable.
	 *
	 * @param variable
	 *            The ghost variable whose assigned expression is determined
	 * @return the assigned expression
	 *
	 * @throws IllegalArgumentException
	 *             if the given variable is not updated
	 */
	public Term getExpressionFor(final IProgramVar variable) {
		final Term expr = mUpdates.get(variable);
		if (expr == null) {
			throw new IllegalArgumentException("no ghost update stored for " + variable);
		}
		return expr;
	}

	/**
	 * Constructs a transition formula representing the update of ghost variables as prescribed by this instance.
	 *
	 * @param mgdScript
	 *            A script used for the construction
	 * @param symbolTable
	 *            A symbol table used for the construction. This must contain all ghost and program variables.
	 * @return the transition formula
	 */
	public UnmodifiableTransFormula makeTransitionFormula(final ManagedScript mgdScript,
			final IIcfgSymbolTable symbolTable) {
		final var variables = new ArrayList<IProgramVar>(mUpdates.size());
		final var values = new ArrayList<Term>(mUpdates.size());
		for (final var entry : mUpdates.entrySet()) {
			variables.add(entry.getKey());
			values.add(entry.getValue());
		}
		return TransFormulaBuilder.constructAssignment(variables, values, symbolTable, mgdScript);
	}

	/**
	 * Creates a new instance with all updates of this instance, in addition to the given updates.
	 *
	 * @param updates
	 *            Additional updates to include. This must not overlap withthe current instance.
	 * @return
	 */
	public GhostUpdate withAdditionalUpdates(final Map<IProgramVar, Term> updates) {
		if (updates.isEmpty()) {
			return this;
		}

		final var newUpdates = new HashMap<>(mUpdates);
		for (final var entry : updates.entrySet()) {
			final var oldTerm = newUpdates.put(entry.getKey(), entry.getValue());
			if (oldTerm != null) {
				throw new IllegalArgumentException("Duplicate update for " + entry.getKey());
			}
		}
		return new GhostUpdate(newUpdates);
	}

	public static GhostUpdate combine(final GhostUpdate oldUpdate, final Map<IProgramVar, Term> newUpdates) {
		if (oldUpdate == null && newUpdates.isEmpty()) {
			return null;
		}
		if (oldUpdate == null) {
			return new GhostUpdate(newUpdates);
		}
		return oldUpdate;
	}

	/**
	 * Computes the size of the ghost update
	 *
	 * @return the sum of the DAG sizes of all terms assigned to ghost variables
	 */
	public int size() {
		final DAGSize sizeComputation = new DAGSize();
		return mUpdates.values().stream().collect(Collectors.summingInt(sizeComputation::size));
	}

	@Override
	public int hashCode() {
		return Objects.hash(mUpdates);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final GhostUpdate other = (GhostUpdate) obj;
		return Objects.equals(mUpdates, other.mUpdates);
	}

	@Override
	public String toString() {
		final var sb1 = new StringBuilder("(");
		final var sb2 = new StringBuilder("(");
		for (final var entry : mUpdates.entrySet()) {
			if (sb1.length() > 1) {
				sb1.append(", ");
				sb2.append(", ");
			}
			sb1.append(entry.getKey());
			sb2.append(entry.getValue());
		}
		return sb1.toString() + ") := " + sb2.toString() + ")";
	}
}
