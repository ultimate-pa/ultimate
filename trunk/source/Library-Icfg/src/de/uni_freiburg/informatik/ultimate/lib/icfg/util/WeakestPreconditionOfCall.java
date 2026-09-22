/*
 * Copyright (C) 2013-2015 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Icfg Library.
 *
 * The ULTIMATE Icfg Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Icfg Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Icfg Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Icfg Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Icfg Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.icfg.util;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieSubstitution;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;

/**
 * Computes the weakest condition that must hold (at the call site) before a procedure call to ensure that the called
 * procedure's precondition is satisfied.
 *
 * This is achieved by removing old(...) operators -- they are meaningless in a procedure precondition -- and
 * substituting the formal input parameters by the arguments of the call statement.
 */
public class WeakestPreconditionOfCall {
	private WeakestPreconditionOfCall() {
		// static class cannot be instantiated
	}

	public static Expression substitutePrecondition(final Expression precondition, final CallStatement call,
			final Procedure calledProcedure) {
		final Expression preconditionWithoutOld = new OldExpressionRemover().processExpression(precondition);
		final var substitutionMap = computeSubstitutionMap(calledProcedure.getInParams(), call.getArguments(), call);
		final var substitution = new BoogieSubstitution(substitutionMap);
		return substitution.processExpression(preconditionWithoutOld);
	}

	private static Map<String, Expression> computeSubstitutionMap(final VarList[] inParams,
			final Expression[] arguments, final Statement call) {
		final var result = new HashMap<String, Expression>();

		int paramNumber = 0;
		for (final VarList varList : inParams) {
			for (final String identifier : varList.getIdentifiers()) {
				if (paramNumber >= arguments.length) {
					throw new IllegalArgumentException("Statement " + call + " has wrong number of arguments");
				}
				result.put(identifier, arguments[paramNumber]);
				paramNumber++;
			}
		}
		if (arguments.length != paramNumber) {
			throw new IllegalArgumentException("Statement " + call + " has wrong number of arguments");
		}

		return result;
	}

	// Removes old(...) operators from an expression.
	private static final class OldExpressionRemover extends BoogieTransformer {
		@Override
		protected Expression processExpression(final Expression expr) {
			if (expr instanceof final UnaryExpression unExpr && unExpr.getOperator() == Operator.OLD) {
				return super.processExpression(unExpr.getExpr());
			}
			return super.processExpression(expr);
		}
	}
}
