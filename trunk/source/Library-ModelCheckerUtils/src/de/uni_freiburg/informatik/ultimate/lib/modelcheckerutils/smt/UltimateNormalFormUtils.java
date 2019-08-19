/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Provides auxiliary methods for checking if terms respect a certain normal form.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public final class UltimateNormalFormUtils {

	private UltimateNormalFormUtils() {
		// do not instantiate
	}

	private static boolean rootRespectsUltimateNormalForm(final ConstantTerm term) {
		if (SmtSortUtils.isBitvecSort(term.getSort())) {
			assert false : "UNF does not support bitvector literals, use instead e.g., (_ bv23 64) to construct a bitvector of length 64 whose decimal value is 23.";
			return false;
		}
		if (term.getValue() instanceof Rational) {
			return true;
		}
		assert false : "ConstantTerms have to use Rationals";
		return false;
	}

	private static boolean rootRespectsUltimateNormalForm(final ApplicationTerm term) {
		if ("distinct".equals(term.getFunction().getName())) {
			assert false : "use not and equals";
			return false;
		}
		if (term.getFunction().getName().equals("select")) {
			final Term array = term.getParameters()[0];
			final Term index = term.getParameters()[1];
			if (index.equals(SmtUtils.getArrayStoreIdx(array))) {
				assert false : "select-over-store with same index should have been removed";
				return false;
			}
		}
		if (term.getFunction().getName().equals("store")) {
			final Term array = term.getParameters()[0];
			final Term index = term.getParameters()[1];
			if (index.equals(SmtUtils.getArrayStoreIdx(array))) {
				assert false : "select-over-store with same index should have been removed";
				return false;
			}
		}
		if (term.getFunction().getName().equals("+")) {
			for (final Term param : term.getParameters()) {
				if (SmtUtils.isIntegerLiteral(BigInteger.ZERO, param)) {
					assert false : "zero is neutral element of plus operator";
					return false;
				}
			}
		}
		if (term.getFunction().getName().equals("bvadd")) {
			for (final Term param : term.getParameters()) {
				if (BitvectorUtils.isBitvectorConstant(BigInteger.ZERO, param)) {
					assert false : "zero is neutral element of plus operator";
					return false;
				}
			}
		}
		if (term.getFunction().getName().equals("bvand")) {
			for (final Term param : term.getParameters()) {
				if (BitvectorUtils.isBitvectorConstant(BigInteger.ZERO, param)) {
					assert false : "zero is absorbing element of bvand operator";
					return false;
				}
			}
		}
		if (SmtUtils.isUnaryNumericMinus(term.getFunction())) {
			final Term param = term.getParameters()[0];
			if (param instanceof ConstantTerm) {
				return true;
			} else if (param instanceof ApplicationTerm) {
				final ApplicationTerm appTerm = (ApplicationTerm) param;
				if (appTerm.getFunction().getName().equals("+")) {
					assert false : "must not be argument of unary minus " + appTerm.getFunction().getName();
					return false;
				}
				return true;
			} else if (param instanceof TermVariable) {
				return true;
			} else {
				throw new AssertionError("Illegal kind of term " + param.getClass().getSimpleName());
			}

		}
		return true;
	}

	private static boolean rootRespectsUltimateNormalForm(final Term term) {
		if (term instanceof ApplicationTerm) {
			return rootRespectsUltimateNormalForm((ApplicationTerm) term);
		} else if (term instanceof ConstantTerm) {
			return rootRespectsUltimateNormalForm((ConstantTerm) term);
		} else {
			return true;
		}
	}

	/**
	 * Check if a term respects a certain normal form that we want to enforce in Ultimate in order to be able to
	 * simplify terms more easily.
	 * <ul>
	 * <li>Values of {@link ConstantTerm}s have to be represented by {@link Rationals} (instead of {@link BigInteger}
	 * and {@link BigDecimal}).
	 * <li>Do not use "distinct" terms. Always use negated equalities instead. This allows us to detect that (and (= a
	 * b) (not (= a b))) is equivalent to false.
	 * </ul>
	 *
	 * @param term
	 *            The {@link Term} that should be checked.
	 * @return true iff term is in Ultimate normal form.
	 */
	public static boolean respectsUltimateNormalForm(final Term term) {
		final Predicate<Term> property = x -> !rootRespectsUltimateNormalForm(x);
		return !new SubtermPropertyChecker(property).isPropertySatisfied(term);
	}

	public static boolean respectsUltimateNormalForm(final Term... terms) {
		final Predicate<Term> property = x -> !rootRespectsUltimateNormalForm(x);
		boolean respects = true;
		for (final Term term : terms) {
			respects &= !new SubtermPropertyChecker(property).isPropertySatisfied(term);
		}
		return respects;
	}

}
