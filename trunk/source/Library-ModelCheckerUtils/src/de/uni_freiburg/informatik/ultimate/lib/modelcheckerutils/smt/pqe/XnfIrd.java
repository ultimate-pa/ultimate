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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.pqe;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Iterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.AffineRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.BinaryEqualityRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.BinaryRelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.SolvedBinaryRelation.AssumptionForSolvability;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;

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
			// if (tv.getSort().isNumericSort()) {
			final Term[] withoutTv = irdSimple(mScript, quantifier, result, tv, mLogger);
			if (withoutTv != null) {
				mLogger.debug(new DebugMessage("eliminated quantifier via IRD for {0}", tv));
				result = withoutTv;
				it.remove();
			} else {
				mLogger.debug(new DebugMessage("not eliminated quantifier via IRD for {0}", tv));
			}
			// } else {
			// // ird is only applicable to variables of numeric sort
			// mLogger.debug(new DebugMessage("not eliminated quantifier via IRD for {0}", tv));
			// }
		}
		return result;
	}

	/**
	 * If the application term contains only parameters param such that for each param one of the following holds and
	 * the third case applies at most once, we return all params that do not contain tv. 1. param does not contain tv 2.
	 * param is an AffineRelation such that tv is a variable of the AffineRelation and the function symbol is "distinct"
	 * and quantifier is ∃ or the function symbol is "=" and the quantifier is ∀ 3. param is an inequality
	 *
	 * @param logger
	 */
	public static Term[] irdSimple(final Script script, final int quantifier, final Term[] oldParams,
			final TermVariable tv, final ILogger logger) {
		// assert tv.getSort().isNumericSort() : "only applicable for numeric sorts";

		final ArrayList<Term> paramsWithoutTv = new ArrayList<>();
		int inequalitiesWithTv = 0;
		int numberOfAntiDer = 0;
		for (final Term oldParam : oldParams) {
			if (!Arrays.asList(oldParam.getFreeVars()).contains(tv)) {
				paramsWithoutTv.add(oldParam);
			} else {
				if (!SmtSortUtils.isNumericSort(tv.getSort()) && !SmtSortUtils.isBitvecSort(tv.getSort())) {
					return null;
				}

				final AffineRelation affineRelation = AffineRelation.convert(script, oldParam);
				if (affineRelation == null) {
					// unable to eliminate quantifier
					return null;
				}
				if (!affineRelation.isVariable(tv)) {
					// unable to eliminate quantifier
					// tv occurs in affine relation but not as affine variable
					// it might occur inside a function or array.
					return null;
				}
				final boolean solveabelWoCaseDist = isSolvableWithoutCaseDistinction(script, tv, affineRelation);
				if (!solveabelWoCaseDist) {
					return null;
				}
				final RelationSymbol relationSymbol = affineRelation.getRelationSymbol();
				switch (relationSymbol) {
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
				case LESS:
				case LEQ:
					if (inequalitiesWithTv > 0) {
						// unable to eliminate quantifier, we may drop at most
						// one inequality
						return null;
					}
					inequalitiesWithTv++;
					// we may drop this parameter (but it has to be the
					// only dropped inequality
					break;
				default:
					throw new AssertionError("unknown functionSymbol");
				}
			}
		}
		// throw new AssertionError("ird ftw");
		final float numberOfDomainElements = underapproximateNumberOfDomainElements(tv.getSort());
		if (numberOfAntiDer >= numberOfDomainElements) {
			return null;
		}
		return paramsWithoutTv.toArray(new Term[paramsWithoutTv.size()]);
	}

	private static boolean isSolvableWithoutCaseDistinction(final Script script, final TermVariable tv,
			final AffineRelation affineRelation) {
		assert Arrays.equals(AssumptionForSolvability.values(), new AssumptionForSolvability[] {
				AssumptionForSolvability.INTEGER_DIVISIBLE_BY_CONSTANT,
				AssumptionForSolvability.REAL_DIVISOR_NOT_ZERO }) : "A new value was added to enum and has to be considered here";
		final SolvedBinaryRelation sbr = affineRelation.solveForSubject(script, tv);
		if (sbr == null) {
			return false;
		} else {
			if (sbr.getAssumptionsMap().isEmpty()) {
				return true;
			} else {
				if (sbr.getAssumptionsMap().keySet()
						.equals(Collections.singleton(AssumptionForSolvability.INTEGER_DIVISIBLE_BY_CONSTANT))) {
					return true;
				} else {
					return false;
				}
			}
		}
	}

	private static float underapproximateNumberOfDomainElements(final Sort sort) {
		if (SmtSortUtils.isBoolSort(sort)) {
			return 2.0f;
		} else if (SmtSortUtils.isNumericSort(sort)) {
			return Float.POSITIVE_INFINITY;
		} else if (SmtSortUtils.isBitvecSort(sort)) {
			final BigInteger bitsize = sort.getRealSort().getIndices()[0];
			return (float) Math.pow(2.0f, bitsize.doubleValue());
		} else if (SmtSortUtils.isFloatingpointSort(sort)) {
			// TODO 2019-07-27 Matthias: This is not correct the FloatingPoint
			// theory does not have a value for each bitvector (e.g., there is
			// only one NaN.
			final BigInteger[] indices = sort.getRealSort().getIndices();
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

	/**
	 * @return true iff oldParam is a not equals relation (resp. quality for universal quantifier) such that one side is
	 *         the variable tv and tv does not occur on the other side.
	 */
	private static boolean isAntiDer(final Term oldParam, final TermVariable tv, final int quantifier) {
		final BinaryEqualityRelation ber = BinaryEqualityRelation.convert(oldParam);
		if (ber == null) {
			return false;
		}
		if ((quantifier == QuantifiedFormula.EXISTS && ber.getRelationSymbol() == RelationSymbol.DISTINCT)
				|| quantifier == QuantifiedFormula.FORALL && ber.getRelationSymbol() == RelationSymbol.EQ) {
			if ((ber.getLhs().equals(tv) && !Arrays.asList(ber.getRhs().getFreeVars()).contains(tv))
					|| ber.getRhs().equals(tv) && !Arrays.asList(ber.getLhs().getFreeVars()).contains(tv)) {
				// this is the antiDER case
				return true;
			}
			return false;
		}
		return false;
	}

}
