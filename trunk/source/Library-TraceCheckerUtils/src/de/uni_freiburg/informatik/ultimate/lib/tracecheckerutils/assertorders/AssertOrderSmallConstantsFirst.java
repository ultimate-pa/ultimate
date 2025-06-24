/*
 * Copyright (C) 2014-2015 Betim Musa (musab@informatik.uni-freiburg.de)
 * Copyright (C) 2024 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify it under the
 * terms of the GNU Lesser General Public License as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License along with the
 * ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7: If you modify the ULTIMATE TraceCheckerUtils Library,
 * or any covered work, by linking or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the licensors of the
 * ULTIMATE TraceCheckerUtils Library grant you additional permission to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.assertorders;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.Counterexample;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Assert statements that with small constants first. Then, check for satisfiability. If the result of the
 * satisfiability check is not unsatisfiable, then assert the rest of the statements, and return the result of the
 * unsatisfiability check.
 *
 * @author Betim Musa (musab@informatik.uni-freiburg.de)
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class AssertOrderSmallConstantsFirst<L extends IAction> implements IAssertOrder<L> {
	private static final int CONSTANT_SIZE = 10;

	/**
	 * Determines whether the given term 't' contains a constant (a (real/natural) number) that is greater than the
	 * given size 'constantSize'.
	 */
	private static boolean termHasConstantGreaterThan(final Term t, final int constantSize) {
		if (t instanceof ApplicationTerm) {
			final Term[] args = ((ApplicationTerm) t).getParameters();
			for (final Term arg : args) {
				if (termHasConstantGreaterThan(arg, constantSize)) {
					return true;
				}
			}
		} else if (t instanceof ConstantTerm) {
			final Object val = ((ConstantTerm) t).getValue();
			if (val instanceof BigInteger) {
				return ((BigInteger) val).compareTo(BigInteger.valueOf(constantSize)) > 0;
			} else if (val instanceof BigDecimal) {
				return ((BigDecimal) val).compareTo(BigDecimal.valueOf(constantSize)) > 0;
			} else if (val instanceof Rational) {
				return ((Rational) val).compareTo(Rational.valueOf(constantSize, 1)) > 0;
			} else {
				throw new UnsupportedOperationException(
						"ConstantTerm is neither BigInter nor BigDecimal, therefore comparison is not possible!");
			}

		}
		return false;
	}

	/**
	 * Partition the statements of the given trace into two sets. The first set consists of the statements, which
	 * contain only constants smaller than or equal to 'constantSize'. The second set contains the statements, which
	 * contain only constants greater than 'constantSize'.
	 */
	private Set<Integer> partitionStmtsAccordingToConstantSize(final NestedWord<L> trace, final int constantSize) {
		final Set<Integer> result = new HashSet<>();

		for (int i = 0; i < trace.length(); i++) {
			final Term t = trace.getSymbol(i).getTransformula().getFormula();
			if (!termHasConstantGreaterThan(t, constantSize)) {
				result.add(i);
			}
		}
		return result;
	}

	@Override
	public List<Set<Integer>> partition(final Counterexample<L> counterexample) {
		final NestedWord<L> trace = counterexample.getWord();
		// Choose statements that contains only constants <= constantSize and assert them
		final Set<Integer> stmtsWithSmallConstant = partitionStmtsAccordingToConstantSize(trace, CONSTANT_SIZE);
		// Then assert the rest of statements
		return List.of(stmtsWithSmallConstant, AssertOrderUtils.getTraceDifference(trace, stmtsWithSmallConstant));
	}
}
