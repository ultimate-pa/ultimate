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
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;

public class GhostUpdate {
	private final Map<IProgramVar, Term> mUpdates;

	public GhostUpdate(final Map<IProgramVar, Term> updates) {
		mUpdates = updates;

		assert !mUpdates.isEmpty() : "empty ghost updates are redundant";
		assert !mUpdates.containsKey(null) : "invalid ghost update for null";
		assert !mUpdates.values().contains(null) : "cannot update ghost variable to null";
		assert mUpdates.entrySet().stream().noneMatch(
				e -> e.getValue().equals(e.getKey().getTermVariable())) : "trivial ghost updates are redundant";
	}

	public Set<IProgramVar> getAssignedVariables() {
		return Collections.unmodifiableSet(mUpdates.keySet());
	}

	public boolean containsUpdateFor(final IProgramVar variable) {
		return mUpdates.containsKey(variable);
	}

	public Term getExpressionFor(final IProgramVar variable) {
		final Term expr = mUpdates.get(variable);
		if (expr == null) {
			throw new IllegalArgumentException("no ghost update stored for " + variable);
		}
		return expr;
	}

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

	public int size() {
		final DAGSize sizeComputation = new DAGSize();
		return mUpdates.values().stream().collect(Collectors.summingInt(sizeComputation::size));
	}
}
