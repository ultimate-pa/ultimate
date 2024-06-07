/*
 * Copyright (C) 2024 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE WitnessPrinter plug-in.
 *
 * The ULTIMATE WitnessPrinter plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE WitnessPrinter plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE WitnessPrinter plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE WitnessPrinter plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE WitnessPrinter plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.witnessprinter;

import java.math.BigDecimal;
import java.util.List;
import java.util.Objects;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.translation.IBacktranslationValueProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;

/**
 * Class to represent a {@link ProgramState} as a String to be written into a witness.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class ProgramStatePrinter<TE, E> {
	private final IBacktranslationValueProvider<TE, E> mStringProvider;

	public ProgramStatePrinter(final IBacktranslationValueProvider<TE, E> stringProvider) {
		mStringProvider = stringProvider;
	}

	private String singleEntryAsExpression(final ProgramState<E> state, final E variable,
			final Predicate<String> variableFilter) {
		final String varString = mStringProvider.getStringFromExpression(variable);
		if (!variableFilter.test(varString)) {
			return null;
		}
		final List<String> disjuncts = state.getValues(variable).stream().map(mStringProvider::getStringFromExpression)
				.filter(this::checkValueString).map(x -> varString + " == " + x).collect(Collectors.toList());
		if (disjuncts.isEmpty()) {
			return null;
		}
		final String disjunction = disjuncts.stream().collect(Collectors.joining(" || "));
		if (disjuncts.size() == 1) {
			return disjunction;
		}
		return "(" + disjunction + ")";
	}

	/**
	 * Create a C-expression (represented as string) from a given {@link ProgramState}. Only translate variables with
	 * their name matching {@code variableFilter}.
	 */
	public String stateAsExpression(final ProgramState<E> state, final Predicate<String> variableFilter) {
		if (state == null) {
			return null;
		}
		final List<String> conjuncts =
				state.getVariables().stream().map(x -> singleEntryAsExpression(state, x, variableFilter))
						.filter(Objects::nonNull).collect(Collectors.toList());
		if (conjuncts.isEmpty()) {
			return null;
		}
		return conjuncts.stream().collect(Collectors.joining(" && "));
	}

	public static boolean isValidCVariable(final String variableName) {
		// is something like read, old, etc.
		return !variableName.contains("\\") && !variableName.contains("&");
	}

	private boolean checkValueString(final String value) {
		try {
			new BigDecimal(value);
		} catch (final NumberFormatException ex) {
			// this is no valid number literal, maybe its true or false?
			return "true".equalsIgnoreCase(value) || "false".equalsIgnoreCase(value);
		}
		return true;
	}
}
