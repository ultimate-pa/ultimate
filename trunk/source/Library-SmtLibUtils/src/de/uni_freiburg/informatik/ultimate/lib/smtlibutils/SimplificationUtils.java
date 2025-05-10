/*
 * Copyright (C) 2022-2025 Matthias Heizmann (matthias.heizmann@iste.uni-stuttgart.de)
 * Copyright (C) 2022-2025 University of Freiburg
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

import java.math.BigInteger;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Provides auxiliary methods for the simplification of SMT formulas.
 *
 * @author Matthias Heizmann (matthias.heizmann@iste.uni-stuttgart.de)
 *
 */
public final class SimplificationUtils {

	private SimplificationUtils() {
		// Prevent instantiation of this utility class
	}

	@FunctionalInterface
	public interface ValidityCheck {
		/**
		 * @return LBool.UNSAT is each of the terms is valid, LBool.SAT if at least one of terms is not valid,
		 *         LBool.UKNOWN if we were unable to decide validity for at least one of the terms.
		 */
		LBool isValid(Term... terms);
	}

	/**
	 * If term contains a subterm of the form `(mod t k)` and we know that in this context t is greater than or equal to
	 * 0 `(<= 0 t)` and t is strictly smaller than k `(< t k)` then we can replace `(mod t k)` by t.
	 *
	 * @param validityCheck
	 *            A function that checks whether `(<= 0 t)` and `(< t k)` are valid in the current context.
	 *
	 * @return The original input if no simplification was possible.
	 */
	public static Term tryModSimplification(final ManagedScript mgdScript, final ValidityCheck validityCheck,
			final Term term) {
		final Set<ApplicationTerm> subTerms = SmtUtils.extractApplicationTerms("mod", term, true);
		if (subTerms.isEmpty()) {
			return term;
		}
		final Map<Term, Term> substitutionMapping = new HashMap<>();
		for (final Term subTerm : subTerms) {
			ModTerm modTerm = ModTerm.of(subTerm);
			final Term originalDivident = modTerm.getDivident();
			{
				// Check if we can apply the simplification recursively
				final Term divident = modTerm.getDivident();
				final Term tmp = tryModSimplification(mgdScript, validityCheck, divident);
				if (tmp != divident) {
					// divided was simplified
					modTerm = new ModTerm(tmp, modTerm.getDivisor());
				}
			}
			final Term dividentGeq0 = SmtUtils.geq(mgdScript.getScript(), modTerm.getDivident(), SmtUtils
					.constructIntegerValue(mgdScript.getScript(), SmtSortUtils.getIntSort(mgdScript), BigInteger.ZERO));
			final Term dividentSmallerDivisor =
					SmtUtils.less(mgdScript.getScript(), modTerm.getDivident(), modTerm.getDivisor());
			final LBool modIsSuperfluous = validityCheck.isValid(dividentGeq0, dividentSmallerDivisor);
			if (modIsSuperfluous == LBool.UNSAT) {
				substitutionMapping.put(subTerm, modTerm.getDivident());
			} else if (originalDivident != modTerm.getDivident()) {
				substitutionMapping.put(originalDivident, modTerm.getDivident());
			}
		}
		if (substitutionMapping.isEmpty()) {
			return term;
		}
		return Substitution.apply(mgdScript, substitutionMapping, term);
	}

}
