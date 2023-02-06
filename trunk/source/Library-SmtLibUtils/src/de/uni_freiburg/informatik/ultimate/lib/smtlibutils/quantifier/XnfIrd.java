/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class XnfIrd extends XjunctPartialQuantifierElimination {

	public XnfIrd(final ManagedScript script, final IUltimateServiceProvider services) {
		super(script, services);
	}

	@Override
	public String getName() {
		return "infinity restrictor drop";
	}

	@Override
	public String getAcronym() {
		return "IRD";
	}

	@Override
	public boolean resultIsXjunction() {
		return true;
	}

	@Override
	public Term[] tryToEliminate(final int quantifier, final Term[] dualJuncts, final Set<TermVariable> eliminatees) {
		final Iterator<TermVariable> it = eliminatees.iterator();
		Term[] result = dualJuncts;
		while (it.hasNext()) {
			final TermVariable tv = it.next();
			if (!SmtUtils.getFreeVars(Arrays.asList(result)).contains(tv)) {
				// case where var does not occur
				it.remove();
				continue;
			}
			final Term[] withoutTv = irdSimple(mMgdScript, quantifier, result, tv);
			if (withoutTv != null) {
				result = withoutTv;
				it.remove();
			}
		}
		return result;
	}

	/**
	 * If the application term contains only parameters param such that for each
	 * param one of the following holds and the third case applies at most once, we
	 * return all params that do not contain tv. 1. param does not contain tv 2.
	 * param is an AffineRelation such that tv is a variable of the AffineRelation
	 * and the function symbol is "distinct" and quantifier is ∃ or the function
	 * symbol is "=" and the quantifier is ∀ 3. param is an inequality
	 */
	public static Term[] irdSimple(final ManagedScript mgdScript, final int quantifier, final Term[] oldParams,
			final TermVariable tv) {
		final ArrayList<Term> paramsWithoutTv = new ArrayList<>();
		int numberOfAntiDer = 0;
		int numberOfUpperBounds = 0;
		int numberOfLowerBounds = 0;
		for (final Term oldParam : oldParams) {
			if (!Arrays.asList(oldParam.getFreeVars()).contains(tv)) {
				paramsWithoutTv.add(oldParam);
			} else {
				if (!SmtSortUtils.isNumericSort(tv.getSort()) && !SmtSortUtils.isBitvecSort(tv.getSort())) {
					return null;
				}
				final SolvedBinaryRelation sbr = solve(mgdScript, tv, quantifier, oldParam);
				if (sbr == null) {
					return null;
				}
				switch (sbr.getRelationSymbol()) {
				case EQ:
					if (quantifier == QuantifiedFormula.EXISTS) {
						// unable to eliminate quantifier
						return null;
					} else if (quantifier == QuantifiedFormula.FORALL) {
						// we may drop this parameter
						numberOfAntiDer++;
					} else {
						throw new AssertionError("unknown quantifier");
					}
					break;
				case DISTINCT:
					if (quantifier == QuantifiedFormula.EXISTS) {
						// we may drop this parameter
						numberOfAntiDer++;
					} else if (quantifier == QuantifiedFormula.FORALL) {
						// unable to eliminate quantifier
						return null;
					} else {
						throw new AssertionError("unknown quantifier");
					}
					break;
				case GREATER:
				case GEQ:
					if (numberOfUpperBounds > 0) {
						// unable to eliminate quantifier, only one direction of bounds is supported
						return null;
					}
					numberOfLowerBounds++;
					break;
				case LESS:
				case LEQ:
					if (numberOfLowerBounds > 0) {
						// unable to eliminate quantifier, only one direction of bounds is supported
						return null;
					}
					numberOfUpperBounds++;
					break;
				case BVULE:
				case BVULT:
				case BVUGE:
				case BVUGT:
				case BVSLE:
				case BVSLT:
				case BVSGE:
				case BVSGT:
					throw new AssertionError("cannot have been transformed to PolynomialRelation");
				default:
					throw new AssertionError("unknown functionSymbol");
				}
			}
		}
		final float numberOfDomainElements = underapproximateNumberOfDomainElements(tv.getSort());
		if (numberOfAntiDer >= numberOfDomainElements) {
			return null;
		}
		return paramsWithoutTv.toArray(new Term[paramsWithoutTv.size()]);
	}

	private static SolvedBinaryRelation solve(final ManagedScript mgdScript, final TermVariable tv,
			final int quantifier, final Term term) {
		final PolynomialRelation polyRel = PolynomialRelation.of(mgdScript.getScript(), term);
		if (polyRel == null) {
			// unable to eliminate quantifier
			return null;
		}
		final SolvedBinaryRelation sbr = polyRel.solveForSubject(mgdScript.getScript(), tv);
		return sbr;
	}

	private static float underapproximateNumberOfDomainElements(final Sort sort) {
		if (SmtSortUtils.isBoolSort(sort)) {
			return 2.0f;
		} else if (SmtSortUtils.isNumericSort(sort)) {
			return Float.POSITIVE_INFINITY;
		} else if (SmtSortUtils.isBitvecSort(sort)) {

			final BigInteger bitsize = new BigInteger(sort.getRealSort().getIndices()[0]);
			return (float) Math.pow(2.0f, bitsize.doubleValue());
		} else if (SmtSortUtils.isFloatingpointSort(sort)) {
			// TODO 2019-07-27 Matthias: This is not correct the FloatingPoint
			// theory does not have a value for each bitvector (e.g., there is
			// only one NaN.
			final BigInteger[] indices = SmtUtils.toBigIntegerArray(sort.getRealSort().getIndices());
			final BigInteger bitsize = indices[0].add(indices[1]);
			return (float) Math.pow(2.0f, bitsize.doubleValue());
		} else if (SmtSortUtils.isArraySort(sort)) {
			final Sort[] arg = sort.getRealSort().getArguments();
			assert arg.length == 2;
			final Sort indexSort = arg[0];
			final Sort valueSort = arg[1];
			return (float) Math.pow(underapproximateNumberOfDomainElements(indexSort),
					underapproximateNumberOfDomainElements(valueSort));
		} else {
			// unknown sort, but contains at least one element
			return 1.0f;
		}
	}

}
