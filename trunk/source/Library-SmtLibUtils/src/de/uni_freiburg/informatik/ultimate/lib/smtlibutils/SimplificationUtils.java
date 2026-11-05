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
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.MultiDimensionalNestedStore;
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
	public static Term applyConstantPropagation(final ManagedScript mgdScript, final Term context, final Term term) {
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
			final Term replaceTerm;
			replaceTerm = findReplacement(mgdScript, validityCheck, mdsons);
			if (replaceTerm != null) {
				substitutionMapping.put(mdsons.toTerm(mgdScript.getScript()), replaceTerm);
			}
		}
		if (substitutionMapping.isEmpty()) {
			return term;
		}
		final Term result = Substitution.apply(mgdScript, substitutionMapping, term);
		if (result == term) {
			throw new AssertionError("Substitution failed to change the term.");
		}
		return result;

	}

	private static Term findReplacement(final ManagedScript mgdScript, final ValidityCheck validityCheck,
			final MultiDimensionalSelectOverNestedStore mdsons) {
		final ArrayIndex selectIndex = mdsons.getSelectIndex();
		final ArrayList<ArrayIndex> storeIndices = new ArrayList<>(mdsons.getNestedStore().getIndices());
		final ArrayList<Term> storeValues = new ArrayList<>(mdsons.getNestedStore().getValues());
		for (int i = storeIndices.size() - 1; i >= 0; i--) {
			final ArrayIndex storeIndex = storeIndices.get(i);
			final LBool isEquivalentToSelectIndex;
			if (i > 0 || storeIndices.size() == 1) {
				// we can use this information if the current storeIndex is the outermost storeIndex or not the
				// innermost storeIndex.
				isEquivalentToSelectIndex = checkIndexEquivalence(mgdScript, validityCheck, storeIndex, selectIndex);
			} else {
				isEquivalentToSelectIndex = null;
			}
			// we are currently at the last store, we check equivalence to select index
			if ((i == storeIndices.size() - 1) && (isEquivalentToSelectIndex == LBool.UNSAT)) {
				// select reads from this position
				return storeValues.get(i);
			}
			final LBool differentFromSelectIndex =
					checkIndexNotEquals(mgdScript, validityCheck, selectIndex, storeIndex);
			if (differentFromSelectIndex == LBool.UNSAT) {
				// select reads from different position, we can remove this store
				storeIndices.remove(i);
				storeValues.remove(i);
			} else {
				for (int j = i + 1; j < storeIndices.size(); j++) {
					final ArrayIndex laterStoreIndex = storeIndices.get(j);
					final LBool similarThanLaterStoreIndex =
							checkIndexEquivalence(mgdScript, validityCheck, storeIndex, laterStoreIndex);
					if (similarThanLaterStoreIndex == LBool.UNSAT) {
						// we can remove the current store, because it is overwritten by a later store
						storeIndices.remove(i);
						storeValues.remove(i);
						break;
					}
				}
			}
			if (i > 0 && isEquivalentToSelectIndex == LBool.UNSAT) {
				// We can remove all preceding stores, because the select reads from this position.
				// So we remove the elements from 0 to i-1 (inclusive) from the lists.
				storeIndices.subList(0, i - 1).clear();
				storeValues.subList(0, i - 1).clear();
				break;
			}
		}
		if (storeIndices.isEmpty()) {
			final MultiDimensionalSelect mds =
					new MultiDimensionalSelect(mdsons.getNestedStore().getArray(), mdsons.getSelectIndex());
			return mds.toTerm(mgdScript.getScript());
		}
		if (storeIndices.size() == mdsons.getNestedStore().getIndices().size()) {
			// cannot simplify this select-over-store
			return null;
		}
		final MultiDimensionalNestedStore mdns =
				new MultiDimensionalNestedStore(mdsons.getNestedStore().getArray(), storeIndices, storeValues);
		final MultiDimensionalSelectOverNestedStore mdsons2 =
				new MultiDimensionalSelectOverNestedStore(mdsons.getSelectIndex(), mdns);
		return mdsons2.toTerm(mgdScript.getScript());
	}

	/**
	 *
	 * @return LBool.UNSAT if we can prove that the two indices are equal.
	 */
	private static LBool checkIndexEquivalence(final ManagedScript mgdScript, final ValidityCheck validityCheck,
			final ArrayIndex idx1, final ArrayIndex idx2) {
		final Term idxEquivalence = ArrayIndex.constructIndexEquality(mgdScript.getScript(), idx1, idx2);
		final LBool idxEquivalent = validityCheck.isValid(idxEquivalence);
		return idxEquivalent;
	}

	/**
	 *
	 * @return LBool.UNSAT if we can prove that the two indices are distinct.
	 */
	private static LBool checkIndexNotEquals(final ManagedScript mgdScript, final ValidityCheck validityCheck,
			final ArrayIndex idx1, final ArrayIndex idx2) {
		assert idx1.size() == idx2.size();
		boolean resultForSomeEntryIsUnknown = false;
		for (int i = 0; i < idx1.size(); i++) {
			final Term negatedEntryEquivalence = SmtUtils.not(mgdScript.getScript(),
					SmtUtils.binaryEquality(mgdScript.getScript(), idx1.get(i), idx2.get(i)));
			final LBool idxEntryNotEquivalent = validityCheck.isValid(negatedEntryEquivalence);
			if (idxEntryNotEquivalent == LBool.UNSAT) {
				return LBool.UNSAT;
			}
			if (idxEntryNotEquivalent == LBool.UNKNOWN) {
				resultForSomeEntryIsUnknown = true;
			}
		}
		if (resultForSomeEntryIsUnknown) {
			return LBool.UNKNOWN;
		}
		return LBool.SAT;
	}

}
