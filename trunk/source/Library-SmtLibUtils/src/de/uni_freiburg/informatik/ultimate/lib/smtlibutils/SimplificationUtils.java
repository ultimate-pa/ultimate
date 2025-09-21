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
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.MultiDimensionalSelectOverNestedStore;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation;
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

	/**
	 * Use equalities of the form `x=l` (where x is a constant symbol or variable and l is a number) to substitute all
	 * occurrences of x by the number l.
	 *
	 * @param context
	 *            Term that we check for equalities. This term is not added to the result. E.g., in the
	 *            {@link PolyPacSimplificationTermWalker} this is the critical constraint.
	 * @param term
	 *            Term in which we apply the substitution.
	 */
	public static Term applyConstantFolding(final ManagedScript mgdScript, final Term context, final Term term) {
		final Map<Term, Term> substitutionMapping = new HashMap<>();
		for (final Term conjunct : SmtUtils.getConjuncts(context)) {
			if (!SmtUtils.isFunctionApplication(conjunct, "=")) {
				continue;
			}
			final PolynomialRelation polyRel = PolynomialRelation.of(mgdScript.getScript(), conjunct);
			if (polyRel != null) {
				final SolvedBinaryRelation sbr = polyRel.isSimpleEquality(mgdScript.getScript());
				if (sbr != null) {
					substitutionMapping.put(sbr.getLeftHandSide(), sbr.getRightHandSide());
				}
			}
		}
		if (substitutionMapping.isEmpty()) {
			return term;
		}
		return Substitution.apply(mgdScript, substitutionMapping, term);
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

	/**
	 * Try to apply a select-over-store simplification. Use the context in which we consider the current formula to
	 * infer whether indices are similar or distinct.
	 *
	 * TODO 20250510 Matthias: Could be extended to cases where we have select-over-store in indices or values. Could be
	 * extended to store-over-store.
	 *
	 */
	public static Term tryArraySimplification(final ManagedScript mgdScript, final ValidityCheck validityCheck,
			final Term term) {
		final List<MultiDimensionalSelectOverNestedStore> list =
				MultiDimensionalSelectOverNestedStore.extractMultiDimensionalSelectOverNestedStore(term, true);
		if (list.isEmpty()) {
			return term;
		}
		final Map<Term, Term> substitutionMapping = new HashMap<>();
		for (final MultiDimensionalSelectOverNestedStore mdsons : list) {
			if (mdsons.getNestedStore().getValues().size() != 1) {
				continue;
			}
			final ArrayIndex storeIndex = mdsons.getNestedStore().getIndices().get(0);
			final ArrayIndex selectIndex = mdsons.getSelectIndex();
			final Term idxEquivalence =
					ArrayIndex.constructIndexEquality(mgdScript.getScript(), storeIndex, selectIndex);
			final LBool idxEquivalent = validityCheck.isValid(idxEquivalence);
			if (idxEquivalent == LBool.UNSAT) {
				substitutionMapping.put(mdsons.toTerm(mgdScript.getScript()),
						mdsons.getNestedStore().getValues().get(0));
				continue;
			}
			final LBool idxNotEquivalent = validityCheck.isValid(SmtUtils.not(mgdScript.getScript(), idxEquivalence));
			if (idxNotEquivalent == LBool.UNSAT) {
				final MultiDimensionalSelect mds =
						new MultiDimensionalSelect(mdsons.getNestedStore().getArray(), mdsons.getSelectIndex());
				substitutionMapping.put(mdsons.toTerm(mgdScript.getScript()), mds.toTerm(mgdScript.getScript()));
			}
		}
		if (substitutionMapping.isEmpty()) {
			return term;
		}
		return Substitution.apply(mgdScript, substitutionMapping, term);

	}

}
