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
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils;

import java.util.Arrays;
import java.util.Comparator;
import java.util.Set;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 *
 * Provides auxiliary methods for our normal form in which the parameter of commutative functions are sorted wrt. their
 * hash code.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class CommuhashUtils {

	private CommuhashUtils() {
		// do not instantiate
	}

	/**
	 * Dangerous! A function may be commutative in some theory but it is not in e.g., QF_UF
	 */
	public static final Set<String> COMMUTATIVE_OPERATORS =
			Set.of("and", "or", "=", "distinct", "+", "*", "bvadd", "bvmul", "bvand", "bvor", "bvxor");

	/**
	 * Orders {@link Term}s by hash code, using {@code toString()} as a tie-breaker for distinct instances whose hash
	 * codes collide.
	 * <p>
	 * A {@link Term} with a smaller hash code is considered smaller; if hash codes are equal, terms are ordered
	 * lexicographically by their {@code toString()} value.
	 */
	public final static Comparator<Term> HASH_BASED_COMPERATOR = (arg0, arg1) -> {
		if (arg0 == arg1) {
			return 0;
		}
		if (arg0.hashCode() == arg1.hashCode()) {
			return arg0.toString().compareTo(arg1.toString());
		}
		return Integer.compare(arg0.hashCode(), arg1.hashCode());
	};

	/**
	 * Dangerous! A function may be commutative in some theory but it is not in e.g., QF_UF
	 *
	 * @param name
	 *            The String that is usually returned by FunctionSymbol#getName
	 * @return
	 */
	public static boolean isKnownToBeCommutative(final String name) {
		return COMMUTATIVE_OPERATORS.contains(name);
	}

	public static Term[] sortByHashCode(final Term... params) {
		final Term[] sortedParams = params.clone();
		Arrays.sort(sortedParams, HASH_BASED_COMPERATOR);
		return sortedParams;
	}

	public static Term term(final Script script, final String funcname, final String[] indices, final Sort returnSort,
			final Term... params) {
		if (isKnownToBeCommutative(funcname)) {
			return script.term(funcname, indices, returnSort, sortByHashCode(params));
		}
		return script.term(funcname, indices, returnSort, params);
	}

	public static boolean isInCommuhashNormalForm(final Term term) {
		final Predicate<Term> property = (x -> !rootInCommuhashNormalForm(x));
		return !new SubtermPropertyChecker(property).isSatisfiedBySomeSubterm(term);
	}

	private static boolean rootInCommuhashNormalForm(final Term term) {
		final boolean result;
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			if (COMMUTATIVE_OPERATORS.contains(appTerm.getFunction().getName())) {
				result = areParamsSorted(appTerm.getParameters());
			} else {
				result = true;
			}
		} else {
			result = true;
		}
		return result;
	}

	private static boolean areParamsSorted(final Term[] params) {
		final Term[] sorted = sortByHashCode(params);
		return Arrays.equals(params, sorted);
	}

}
