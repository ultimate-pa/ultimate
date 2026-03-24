/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE SMTSolverBridge.
 *
 * The ULTIMATE SMTSolverBridge is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE SMTSolverBridge is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SMTSolverBridge. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SMTSolverBridge, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE SMTSolverBridge grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.smtsolver.external;

import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LambdaTerm;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * An SMT model extracted from a (get-model) response.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 */
public class ModelDescription implements Model {
	private final Map<FunctionSymbol, FunctionDefinition> mDefinitions;

	public ModelDescription(final Set<FunctionDefinition> definitions) {
		mDefinitions = definitions.stream().collect(Collectors.toMap(def -> def.getName(), Function.identity()));
	}

	@Override
	public Term evaluate(final Term input) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Map<Term, Term> evaluate(final Term[] input) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Set<FunctionSymbol> getDefinedFunctions() {
		return mDefinitions.values().stream().map(FunctionDefinition::getName).collect(Collectors.toSet());
	}

	@Override
	public LambdaTerm getFunctionDefinition(final FunctionSymbol fs) {
		return Objects
				.requireNonNull(mDefinitions.get(fs), "No function definition for %s found.".formatted(fs.getName()))
				.toLambdaTerm();
	}

	@Override
	public String toString() {
		return mDefinitions.values().stream().map(Object::toString).collect(Collectors.joining("\n"));
	}
}
