/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
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
import java.util.Arrays;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Util;

/**
 * Brings Terms into a normal form where all parameters that of commutative functions (resp. functions for that this
 * class knows that they are commutative) are sorted according to their hash code. Furthermore all AffineRelations are
 * transformed into positive normal form.
 *
 * This can simplify terms, e.g., (or (and A B) (and B A)) will be simplified to (and A B) (except in the very rare case
 * where the hash code of A and B coincides).
 *
 * @author Matthias Heizmann
 *
 */
public class CommuhashNormalFormTransformer extends TermTransformer {

	/**
	 * Use an SMT solver to check equivalence of input and output. Note that this check can be questionable. We
	 * typically transform to CommuhashNormalForm after receiving a formula from an external source, e.g., Craig
	 * interpolants of an SMT solver. At this time there might temporarily other formulas on the solver's assertion
	 * stack and hamper the meaningfulness of this check test.
	 */
	private static final boolean DEBUG_CHECK_CORRECTNESS = false;
	private final Script mScript;

	private CommuhashNormalFormTransformer(final Script script) {
		mScript = script;
	}

	@Override
	public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] newArgs) {
		final String funcname = appTerm.getFunction().getName();
		if (CommuhashUtils.isKnownToBeCommutative(funcname)) {
			final Sort resultSort =
					appTerm.getFunction().isReturnOverload() ? appTerm.getFunction().getReturnSort() : null;
			final Term simplified = constructlocallySimplifiedTermWithSortedParams(funcname, null, resultSort, newArgs);
			setResult(simplified);
		} else {
			super.convertApplicationTerm(appTerm, newArgs);
		}
	}

	/**
	 * @param resultSort
	 *            must be non-null if and only if we have an explicitly instantiated polymorphic FunctionSymbol, i.e., a
	 *            function of the form (as <name> <sort>)
	 */
	private Term constructlocallySimplifiedTermWithSortedParams(final String funcname, final BigInteger[] indices,
			final Sort resultSort, final Term[] params) {
		final Term[] sortedParams = CommuhashUtils.sortByHashCode(params);
		final Term simplified =
				SmtUtils.unfTerm(mScript, funcname, SmtUtils.toStringArray(indices), resultSort, sortedParams);
		return simplified;
	}

	@Override
	public void postConvertQuantifier(final QuantifiedFormula old, final Term newBody) {
		final Term result = SmtUtils.quantifier(mScript, old.getQuantifier(),
				new HashSet<>(Arrays.asList(old.getVariables())), newBody);
		setResult(result);
	}

	public static Term apply(final Script script, final Term term) {
		final Term result = (new CommuhashNormalFormTransformer(script)).transform(term);
		assert (!DEBUG_CHECK_CORRECTNESS || Util.checkSat(script, script.term("distinct", term, result)) != LBool.SAT)
				: "CommuhashNormalForm transformation unsound";
		return result;
	}
}
