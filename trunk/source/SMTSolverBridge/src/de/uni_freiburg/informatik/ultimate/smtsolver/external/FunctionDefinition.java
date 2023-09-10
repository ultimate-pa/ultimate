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

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Represents an SMT command defining a function. This data structure is also used to represent the response to
 * (get-model) commands.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 */
public class FunctionDefinition {
	private final FunctionSymbol mName;
	private final TermVariable[] mParams;
	private final Term mBody;

	public FunctionDefinition(final FunctionSymbol name, final TermVariable[] params, final Term body) {
		mName = name;
		mParams = params;
		mBody = body;
	}

	public FunctionSymbol getName() {
		return mName;
	}

	public TermVariable[] getParams() {
		return mParams;
	}

	public Sort getReturnSort() {
		return mName.getReturnSort();
	}

	public Term getBody() {
		return mBody;
	}

	@Override
	public String toString() {
		final var builder = new StringBuilder("(define-fun ");
		builder.append(mName);
		builder.append(" (");
		for (final var param : mParams) {
			builder.append("(");
			builder.append(param.toString());
			builder.append(" ");
			builder.append(param.getSort());
			builder.append(") ");
		}
		builder.append(") ");
		builder.append(getReturnSort());
		builder.append(" ");
		builder.append(mBody);
		builder.append(")");
		return builder.toString();
	}
}
