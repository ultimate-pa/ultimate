/*
 * Copyright (C) 2019 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
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
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.DerScout.DerApplicability;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.TreeHashRelation;

/**
 * @deprecated Superseded by {@link XnfScout}. We keep this class only for
 *             comparisons during debugging.
 *
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
@Deprecated
public class DerScout extends CondisTermTransducer<DerApplicability> {

	public enum Adk { ATOM, DISJUNCTION, CONJUNCTION;
		public static Adk getCorrespondingFiniteConnective(final int quantifier) {
			if (quantifier == QuantifiedFormula.EXISTS) {
				return Adk.DISJUNCTION;
			} else if (quantifier == QuantifiedFormula.FORALL) {
				return Adk.CONJUNCTION;
			} else {
				throw new AssertionError("unknown value " + quantifier);
			}
		}
		public static Adk getDualFiniteConnective(final int quantifier) {
			if (quantifier == QuantifiedFormula.EXISTS) {
				return Adk.CONJUNCTION;
			} else if (quantifier == QuantifiedFormula.FORALL) {
				return Adk.DISJUNCTION;
			} else {
				throw new AssertionError("unknown value " + quantifier);
			}
		}
	}
	public final TermVariable mEliminatee;
	public final Script mScript;
	public final int mQuantifier;



	public DerScout(final TermVariable eliminatee, final Script script, final int quantifier) {
		super();
		mEliminatee = eliminatee;
		mScript = script;
		mQuantifier = quantifier;
	}

	@Override
	protected DerApplicability transduceAtom(final Term term) {
		final BigInteger withoutDer;
		final BigInteger withoutVar;
		if (Arrays.asList(term.getFreeVars()).contains(mEliminatee)) {
			withoutVar = BigInteger.ZERO;
			final PolynomialRelation polyRel = PolynomialRelation.of(mScript, term);
			if (polyRel == null) {
				withoutDer = BigInteger.ONE;
			} else {
				final SolvedBinaryRelation sbr = polyRel.solveForSubject(mScript, mEliminatee);
				if (sbr == null) {
					withoutDer = BigInteger.ONE;
				} else {
					if (polyRel.getRelationSymbol() == QuantifierUtils.getDerOperator(mQuantifier)) {
						withoutDer = BigInteger.ZERO;
					} else {
						withoutDer = BigInteger.ONE;
					}
				}
			}
		} else {
			withoutDer = BigInteger.ONE;
			withoutVar = BigInteger.ONE;
		}
		return new DerApplicability(Adk.ATOM, BigInteger.ONE, withoutDer, withoutVar);
	}

	@Override
	protected DerApplicability transduceConjunction(final ApplicationTerm originalTerm,
			final List<DerApplicability> transducedArguments) {
		final Adk subTermConnective = Adk.DISJUNCTION;
		final Adk ownConnective = Adk.CONJUNCTION;
		final DerApplicability result;
		if (mQuantifier == QuantifiedFormula.EXISTS) {
			result = multiply(transducedArguments, subTermConnective, ownConnective);
		} else if (mQuantifier == QuantifiedFormula.FORALL) {
			result = add(transducedArguments, subTermConnective, ownConnective);
		} else {
			throw new AssertionError();
		}
		return result;
	}

	@Override
	protected DerApplicability transduceDisjunction(final ApplicationTerm originalTerm,
			final List<DerApplicability> transducedArguments) {
		final Adk subTermConnective = Adk.CONJUNCTION;
		final Adk ownConnective = Adk.DISJUNCTION;
		final DerApplicability result;
		if (mQuantifier == QuantifiedFormula.EXISTS) {
			result = add(transducedArguments, subTermConnective, ownConnective);
		} else if (mQuantifier == QuantifiedFormula.FORALL) {
			result = multiply(transducedArguments, subTermConnective, ownConnective);
		} else {
			throw new AssertionError();
		}
		return result;
	}

	private static DerApplicability multiply(final List<DerApplicability> transducedArguments, final Adk subTermConnective,
			final Adk ownConnective) throws AssertionError {
		BigInteger cases = BigInteger.ONE;
		BigInteger withoutDer = BigInteger.ONE;
		BigInteger withoutVar = BigInteger.ONE;
		for (final DerApplicability input : transducedArguments) {
			if (input.getAdk() == Adk.ATOM || input.getAdk() == subTermConnective) {
				cases = cases.multiply(input.getCases());
				withoutDer = withoutDer.multiply(input.getWithoutDerCases());
				withoutVar = withoutVar.multiply(input.getWithoutVarCases());
			} else {
				throw new AssertionError("expected conjuntion-disjunction alternation");
			}
		}
		return new DerApplicability(ownConnective, cases, withoutDer, withoutVar);
	}
	private static DerApplicability add(final List<DerApplicability> transducedArguments, final Adk subTermConnective,
			final Adk ownConnective) throws AssertionError {
		BigInteger cases = BigInteger.ZERO;
		BigInteger withoutDer = BigInteger.ZERO;
		BigInteger withoutVar = BigInteger.ZERO;
		for (final DerApplicability input : transducedArguments) {
			if (input.getAdk() == Adk.ATOM || input.getAdk() == subTermConnective) {
				cases = cases.add(input.getCases());
				withoutDer = withoutDer.add(input.getWithoutDerCases());
				withoutVar = withoutVar.add(input.getWithoutVarCases());
			} else {
				throw new AssertionError("expected conjuntion-disjunction alternation");
			}
		}
		return new DerApplicability(ownConnective, cases, withoutDer, withoutVar);
	}



	private static List<Integer> computeMaximum(final List<Integer> list1, final List<Integer> list2) {
		List<Integer> larger;
		List<Integer> smaller;
		if (list1.size() >= list2.size()) {
			larger = list1;
			smaller = list2;
		} else {
			larger = list2;
			smaller = list1;
		}
		for (int i=0; i<smaller.size(); i++) {
			larger.set(i, Integer.max(larger.get(i), smaller.get(i)));
		}
		return larger;
	}


	public static class DerApplicability {
		private final Adk mAdk;
		private final BigInteger mCases;
		private final BigInteger mWitoutDerCases;
		private final BigInteger mWithoutVarCases;

		public DerApplicability(final Adk adk, final BigInteger cases, final BigInteger withoutDerCases,
				final BigInteger withoutVarCases) {
			super();
			mAdk = adk;
			mCases = cases;
			mWitoutDerCases = withoutDerCases;
			mWithoutVarCases = withoutVarCases;
		}

		public Adk getAdk() {
			return mAdk;
		}

		public BigInteger getCases() {
			return mCases;
		}

		public BigInteger getWithoutDerCases() {
			return mWitoutDerCases;
		}

		public BigInteger getWithoutVarCases() {
			return mWithoutVarCases;
		}

		@Override
		public String toString() {
			return mAdk.toString() + mCases + "/" + mWitoutDerCases + "/" + mWithoutVarCases;
		}

	}

	/**
	 * Heuristic for selecting an eliminatee that preferably can be eliminated and
	 * that can be eliminated with a preferably small blowup of the formula's size.
	 */
	public static TermVariable selectBestEliminatee(final Script script, final int quantifier,
			final List<TermVariable> eliminatees, final List<Term> currentDualFiniteParams) {
		if (eliminatees.size() == 1) {
			return eliminatees.iterator().next();
		}
		final Map<TermVariable, BigInteger> score =
				computeDerApplicabilityScore(script, quantifier, eliminatees, currentDualFiniteParams);
		// final Map<TermVariable, Long> inhabitedParamTreesizes = computeTreesizeOfInhabitedParams(eliminatees,
		// currentDualFiniteParams);
		final TreeHashRelation<BigInteger, TermVariable> tr = new TreeHashRelation<>();
		tr.reverseAddAll(score);
		final Entry<BigInteger, HashSet<TermVariable>> best = tr.entrySet().iterator().next();
		return best.getValue().iterator().next();
	}

	private static Map<TermVariable, BigInteger> computeDerApplicabilityScore(final Script script, final int quantifier,
			final List<TermVariable> eliminatees, final List<Term> currentDualFiniteParams) {
		final Term correspondingFiniteJunction =
				QuantifierUtils.applyDualFiniteConnective(script, quantifier, currentDualFiniteParams);
		final Map<TermVariable, BigInteger> result = new HashMap<>();
		for (final TermVariable eliminatee : eliminatees) {
			final DerApplicability da =
					new DerScout(eliminatee, script, quantifier).transduce(correspondingFiniteJunction);
			final BigInteger score = da.getWithoutDerCases().subtract(da.getWithoutVarCases());
			result.put(eliminatee, score);
		}
		return result;
	}


	public static int computeRecommendation(final Script script, final Set<TermVariable> eliminatees, final Term[] dualFiniteParams,
			final int quantifier) {

		final Map<TermVariable, List<DerApplicability>> map = new HashMap<>();
		for (final TermVariable eliminatee : eliminatees) {
			final List<DerApplicability> list = new ArrayList<DerApplicability>();
			for (final Term param : dualFiniteParams) {
				final DerApplicability da = new DerScout(eliminatee, script, quantifier)
						.transduce(param);
				list.add(da);
			}
			final DerApplicability appl = multiply(list, Adk.getCorrespondingFiniteConnective(quantifier), Adk.getDualFiniteConnective(quantifier));
			final BigInteger nonElimCases = appl.getWithoutDerCases().subtract(appl.getWithoutVarCases());
			final boolean eliminationGuarantee = nonElimCases.equals(BigInteger.ZERO);
			if (eliminationGuarantee) {
				map.put(eliminatee, list);
			}
		}
		final double[] paramScore = new double[dualFiniteParams.length];
		for (final Entry<TermVariable, List<DerApplicability>> entry : map.entrySet()) {
			int i = 0;
			for (final DerApplicability appl : entry.getValue()) {
				final BigInteger derCases = appl.getCases().subtract(appl.getWithoutDerCases());
				final Rational derCasedRat = Rational.valueOf(derCases, BigInteger.ONE);
				final Rational casesRat = Rational.valueOf(appl.getCases(), BigInteger.ONE);
				final double eliminateeScore = SmtUtils.approximateAsDouble(derCasedRat.div(casesRat));
				paramScore[i] += eliminateeScore;
				i++;
			}
		}
		double currentMax = paramScore[0];
		int currentMaxIndex = 0;
		for (int i=1;i<paramScore.length;i++) {
			if (paramScore[i] > currentMax) {
				currentMaxIndex = i;
				currentMax = paramScore[i];
			}
		}
		assert currentMax >= 0.0;
		if (currentMax > 0.0) {
			return currentMaxIndex;
		} else {
			return - 1;
		}
	}
}
