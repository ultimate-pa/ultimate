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

import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.UnfTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.FunctionDefinition;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.ModelDescription;

/**
 * Transforms CHC solutions into Ultimate normal form.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 */
public class ChcSolutionNormalizer {
	private final Script mScript;

	public ChcSolutionNormalizer(final Script script) {
		mScript = script;
	}

	public ChcSolution normalize(final ChcSolution solution) {
		switch (solution.getSatisfiability()) {
		case SAT:
			if (solution.getModel() == null) {
				return solution;
			}
			return ChcSolution.sat(normalize((ModelDescription) solution.getModel()), solution.getBacktranslator());
		case UNSAT:
			if (solution.getDerivation() == null) {
				return solution;
			}
			return ChcSolution.unsat(normalize(solution.getDerivation()), solution.getUnsatCore(),
					solution.getBacktranslator());
		case UNKNOWN:
			return solution;
		default:
			throw new AssertionError();
		}
	}

	public Model normalize(final ModelDescription model) {
		return new ModelDescription(model.getDefinedFunctions().stream()
				.map(fun -> normalize(model.getFunctionDefinition(fun.getName()))).collect(Collectors.toSet()));
	}

	public FunctionDefinition normalize(final FunctionDefinition definition) {
		final var body = new UnfTransformer(mScript).transform(definition.getBody());
		return new FunctionDefinition(definition.getName(), definition.getParams(), body);
	}

	public Derivation normalize(final Derivation derivation) {
		// TODO
		return derivation;
	}
}
