/*
 * Copyright (C) 2026 Manuel Bentele
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.model.acsl;

import java.util.ArrayDeque;
import java.util.Collections;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Expression;

/**
 * Object that returns the DAG size of an ACSL expression on demand.
 *
 * The behavior is the ACSL pendant of the {@code DagSizePrinter} for SMT terms: The DAG size is the number of distinct
 * subexpressions, i.e. every expression node is counted exactly once, even if it is referenced several times. Since
 * ACSL nodes do not provide an equals method, nodes are identified by object identity. Nodes that are no expressions
 * (e.g. types of expressions or declarations of quantified variables) are not counted.
 *
 * @apiNote Use this e.g. in {@code logger.debug(ACSLDagSizePrinter.print(expression))} in order to compute the DAG size
 *          only if the log level is set to debug.
 *
 * @author Manuel Bentele
 */
public class ACSLDagSizePrinter {

	private ACSLDagSizePrinter() {
	}

	/**
	 * Compute the DAG size of the given ACSL expression, i.e. the number of its distinct subexpressions.
	 *
	 * @param expression
	 *            the expression whose DAG size is computed
	 * @return the number of distinct expression nodes, 0 if the expression is null
	 */
	public static int compute(final Expression expression) {
		if (expression == null) {
			return 0;
		}

		final Set<Expression> visited = Collections.newSetFromMap(new IdentityHashMap<>());
		final Deque<Expression> stack = new ArrayDeque<>();
		int size = 0;

		stack.push(expression);

		while (!stack.isEmpty()) {
			final Expression current = stack.pop();
			if (!visited.add(current)) {
				continue;
			}

			++size;

			for (final ACSLNode child : current.getOutgoingNodes()) {
				if (child instanceof final Expression subexpression) {
					stack.push(subexpression);
				}
			}
		}

		return size;
	}

	/**
	 * Print the computed DAG size of the given ACSL expression, i.e. the number of its distinct subexpressions.
	 *
	 * @param expression
	 *            the expression whose computed DAG size is printed
	 * @return printed number of distinct expression nodes
	 */
	public static String print(final Expression expression) {
		return String.valueOf(compute(expression));
	}

}
