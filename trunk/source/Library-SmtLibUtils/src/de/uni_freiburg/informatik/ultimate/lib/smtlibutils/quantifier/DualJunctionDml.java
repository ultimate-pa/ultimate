/*
 /*
 /*
 /*
 * Copyright (C) 2022 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2022 Katharina Wagner
 * Copyright (C) 2022 University of Freiburg
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
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IteRemover;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AffineTermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.ArithmeticUtils;

/**
 * Div-mod liberation (DML) for conjunctions (resp. disjunctions). <br>
 *
 * TODO: PolyPac, DER, PolyPac for each candidate. Drop candidates where DER is not successful and x occurred on
 * disjunction. Rationale: elimination only after distributivity anyway.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Katharina Wagner
 */
public class DualJunctionDml extends DualJunctionQuantifierElimination {

	private static final boolean POSTPONE_ELIMINATEES_NOT_YET_PROMISING = true;
	/**
	 * Looks very useful and is required for some benchmarks but had surprisingly bad effects on
	 * {@link QuantifierEliminationDivModCrafted#bvToIntFoxExists04} (which are by now solved by another optimization).
	 */
	private static final boolean EXCLUDE_CORRESPONDING_FINITE_JUNCTIONS = true;
	/**
	 * Omit `div` eliminations where we think that an elimination of the new auxiliary variables is unlikely. Currently:
	 * Omit if the absolut value of the coefficient of the eliminatee is one. <br />
	 * TODO Matthias 20230312: Maybe we can do the elimination additionally if the eliminatee occurs only in one
	 * dualJunct.
	 */
	private static final boolean OMIT_NON_PROMISING_DIV_ELIMINATIONS = true;

	public DualJunctionDml(final ManagedScript script, final IUltimateServiceProvider services) {
		super(script, services);
	}

	@Override
	public String getName() {
		return "div mod liberation";
	}

	@Override
	public String getAcronym() {
		return "DML";
	}

	public List<DmlPossibility> findAllDmlPossibilities(final EliminationTask inputEt) {
		final List<DmlPossibility> result = new ArrayList<>();
		final Term[] dualFiniteJuncts = QuantifierUtils.getDualFiniteJuncts(inputEt.getQuantifier(), inputEt.getTerm());
		for (final TermVariable eliminatee : inputEt.getEliminatees()) {
			boolean eliminateeOccursInCorrespondingFiniteJunction = false;
			for (final Term dualJunct : dualFiniteJuncts) {
				if (QuantifierUtils.isCorrespondingFiniteJunction(inputEt.getQuantifier(), dualJunct)
						&& EXCLUDE_CORRESPONDING_FINITE_JUNCTIONS) {
					// If this is e.g., a disjunction in a conjunction, we skip the conjunct.
					// Rationale, we will take care of this after applying distributivity and then
					// our chances are higher that the newly introduced variables can be eliminated.
					if (Arrays.asList(dualJunct.getFreeVars()).contains(eliminatee)) {
						eliminateeOccursInCorrespondingFiniteJunction = true;
					}
					continue;
				}
				final boolean onlyOutermost = false;
				final Set<ApplicationTerm> divModSubterms =
						SmtUtils.extractApplicationTerms(Set.of("div", "mod"), dualJunct, onlyOutermost);
				for (final ApplicationTerm appTerm : divModSubterms) {
					assert appTerm.getFunction().getApplicationString().equals("div")
							|| appTerm.getFunction().getApplicationString().equals("mod");
					assert appTerm.getParameters().length == 2;
					final BigInteger divisorAsBigInteger;
					{
						final Term divisorAsTerm = appTerm.getParameters()[1];
						final Rational divisorAsRational = SmtUtils.tryToConvertToLiteral(divisorAsTerm);
						if (divisorAsRational == null) {
							// nonlinear term
							continue;
						}
						assert !divisorAsRational.numerator().equals(BigInteger.ZERO);
						assert divisorAsRational.denominator().equals(BigInteger.ONE);
						if (divisorAsRational.isNegative()) {
							throw new AssertionError("UltimateNormalForm makes sure that divisors are non-negative");
						}
						divisorAsBigInteger = divisorAsRational.numerator();
					}
					final Term dividentAsTerm = appTerm.getParameters()[0];
					if (!Arrays.asList(dividentAsTerm.getFreeVars()).contains(eliminatee)) {
						continue;
					}
					final CoeffcientEliminateeOffset ceo =
							CoeffcientEliminateeOffset.of(mScript, eliminatee, dividentAsTerm);
					if (ceo == null) {
						continue;
					}
					final BigInteger gcd = divisorAsBigInteger.gcd(ceo.getCoefficient());
					if (gcd.compareTo(BigInteger.ZERO) <= 0) {
						throw new AssertionError("Expected that GCD is always positive");
					}
					if (!gcd.equals(BigInteger.valueOf(1))) {
						// TODO 20230226 Matthias: Think about an extension for the GCD≠1 case.
						continue;
					}
					final BigInteger inverse;
					{
						final BigInteger tmp =
								ArithmeticUtils.multiplicativeInverse(ceo.getCoefficient(), divisorAsBigInteger);
						// In order to simplify other parts of the algorithm, we want to make sure that
						// the multiplication of coefficient and inverse is always positive. Hence, if
						// the coefficient was negative, we have to take a negative inverse.
						if (ceo.getCoefficient().compareTo(BigInteger.ZERO) < 0) {
							inverse = tmp.subtract(divisorAsBigInteger.abs());
						} else {
							inverse = tmp;
						}
					}
					final DmlPossibility dmlPossibility =
							new DmlPossibility(appTerm.getFunction().getApplicationString(), ceo, divisorAsBigInteger,
									dualJunct, inverse, appTerm, eliminateeOccursInCorrespondingFiniteJunction);
					result.add(dmlPossibility);
				}
			}
		}
		return result;
	}

	@Override
	public EliminationResult tryToEliminate(final EliminationTask inputEt) {
		final List<DmlPossibility> possibilities = findAllDmlPossibilities(inputEt);
		if (possibilities.isEmpty()) {
			return null;
		}
		final TreeSet<EliminationResult> candidates = new TreeSet<>();
		for (final DmlPossibility dmlPossibility : possibilities) {
			final EliminationResult er1;
			if (dmlPossibility.getFunName().equals("mod")) {
				er1 = applyElimination(inputEt, dmlPossibility);
			} else if (dmlPossibility.getFunName().equals("div")) {
				if (OMIT_NON_PROMISING_DIV_ELIMINATIONS
						&& !dmlPossibility.getCoefficient().abs().equals(BigInteger.ONE)) {
					continue;
				}
				er1 = applyElimination(inputEt, dmlPossibility);
			} else {
				throw new AssertionError();
			}
			final EliminationResult er2 = tryImmediateDer(er1);
			assert er2.getNewEliminatees().size() <= 2;
			if (POSTPONE_ELIMINATEES_NOT_YET_PROMISING
					&& dmlPossibility.doesEliminateeOccurInCorrespondingFiniteJunction()
					&& er2.getNewEliminatees().size() > 0) {
				// DER could not eliminate something an the eliminatee occurred inside a
				// correspondingFiniteJunction, hence the elimination should be delayed until
				// inner correspondingFiniteJunctions are resolved by distributivity.
				continue;
			} else {
				candidates.add(er2);
			}
		}
		if (!candidates.isEmpty()) {
			return candidates.iterator().next();
		}
		return null;
	}

	/**
	 * Try to eliminate something via DER. Return input if impossible.
	 */
	private EliminationResult tryImmediateDer(final EliminationResult er) {
		final EliminationTask newIntegrated = er.integrateNewEliminatees();
		final DualJunctionDer der = new DualJunctionDer(mMgdScript, mServices, false);
		final EliminationResult afterDer = der.tryToEliminate(newIntegrated);
		final EliminationResult result;
		if (afterDer == null) {
			result = er;
		} else {
			if (!afterDer.getNewEliminatees().isEmpty()) {
				throw new AssertionError("DER cannot add new eliminatees");
			}
			result = extractNewEliminatees(afterDer.getEliminationTask(), er.getNewEliminatees());
		}
		return result;
	}

	/**
	 * Given an {@link EliminationTask} whose set of eliminatees may "accidentally" contain some "newEliminatees",
	 * remove the newEliminatees from the {@link EliminationTask} and add the ones that are really there separately to
	 * an {@link EliminationResult}.
	 */
	private EliminationResult extractNewEliminatees(final EliminationTask et, final Set<TermVariable> newEliminatees) {
		final Set<TermVariable> originalEliminatees =
				et.getEliminatees().stream().filter(x -> !newEliminatees.contains(x)).collect(Collectors.toSet());
		final Set<TermVariable> occuingNewEliminatees =
				et.getEliminatees().stream().filter(x -> newEliminatees.contains(x)).collect(Collectors.toSet());
		final EliminationTask eliminationTask =
				new EliminationTask(et.getQuantifier(), originalEliminatees, et.getTerm(), et.getContext());
		return new EliminationResult(eliminationTask, occuingNewEliminatees);
	}

	private EliminationResult applyElimination(final EliminationTask inputEt, final DmlPossibility pmt)
			throws AssertionError {
		final TermVariable y = mMgdScript.constructFreshTermVariable("y", SmtSortUtils.getIntSort(mScript));
		final TermVariable z = mMgdScript.constructFreshTermVariable("z", SmtSortUtils.getIntSort(mScript));
		final Term divisor =
				SmtUtils.constructIntegerValue(mScript, SmtSortUtils.getIntSort(mScript), pmt.getDivisor());
		final Term inverse =
				SmtUtils.constructIntegerValue(mScript, SmtSortUtils.getIntSort(mScript), pmt.getInverse());
		final Term replacedDivMod;
		if (pmt.getFunName().equals("mod")) {
			replacedDivMod = applyModElimination(inputEt, pmt, y, z, divisor, inverse);
		} else if (pmt.getFunName().equals("div")) {
			replacedDivMod = applyDivElimination(inputEt, pmt, y, z, divisor, inverse);
		} else {
			throw new AssertionError();
		}
		final Term simplifiedResultTerm =
				SmtUtils.simplify(mMgdScript, replacedDivMod, mServices, SimplificationTechnique.POLY_PAC);
		final Set<TermVariable> remainingEliminatees = new HashSet<>(inputEt.getEliminatees());
		remainingEliminatees.remove(pmt.getEliminate());
		final EliminationTask eliminationTask = new EliminationTask(inputEt.getQuantifier(), remainingEliminatees,
				simplifiedResultTerm, inputEt.getContext());
		final Set<TermVariable> newEliminatees = new HashSet<>();
		newEliminatees.add(y);
		newEliminatees.add(z);
		final EliminationResult resultWithoutXInMod = new EliminationResult(eliminationTask, newEliminatees);
		return resultWithoutXInMod;
	}

	private Term applyModElimination(final EliminationTask inputEt, final DmlPossibility pmt, final TermVariable y,
			final TermVariable z, final Term divisor, final Term inverse) {
		final Term modReplaced = replaceModTerm(inputEt, pmt, z, divisor);
		final Term eliminateeReplaced;
		{
			// product1: y*k
			final Term product1 = SmtUtils.mul(mScript, SmtSortUtils.getIntSort(mScript), divisor, y);
			// product2: a⁻1*z
			final Term product2 = SmtUtils.mul(mScript, SmtSortUtils.getIntSort(mScript), inverse, z);
			// sum1: y*k + a⁻1*z
			final Term sum = SmtUtils.sum(mScript, SmtSortUtils.getIntSort(mScript), product1, product2);
			final Map<Term, Term> substitutionMapping = Collections.singletonMap(pmt.getEliminate(), sum);
			eliminateeReplaced = Substitution.apply(mMgdScript, substitutionMapping, modReplaced);
		}
		final Term interval = constructInterval(inputEt.getQuantifier(), z, divisor);
		return QuantifierUtils.applyDualFiniteConnective(mScript, inputEt.getQuantifier(), eliminateeReplaced,
				interval);
	}

	private Term dissolveIte(final Term termWithIte) {
		final Term iteRemoved = new IteRemover(mMgdScript).transform(termWithIte);
		return new NnfTransformer(mMgdScript, mServices, QuantifierHandling.KEEP).transform(iteRemoved);
	}

	private Term constructInterval(final int quantifier, final TermVariable z, final Term divisor) {
		final Term zeroAsTerm =
				SmtUtils.constructIntegerValue(mScript, SmtSortUtils.getIntSort(mScript), BigInteger.ZERO);
		final Term result;
		if (quantifier == QuantifiedFormula.EXISTS) {
			// lowerBoundExists: 0 <= z
			final Term lowerBoundExists = SmtUtils.geq(mScript, z, zeroAsTerm);
			// upperBoundExists: z < k
			final Term upperBoundExists = SmtUtils.less(mScript, z, divisor);
			result = SmtUtils.and(mScript, lowerBoundExists, upperBoundExists);
		} else if (quantifier == QuantifiedFormula.FORALL) {
			// upperBoundForall: z < 0
			final Term upperBoundForall = SmtUtils.less(mScript, z, zeroAsTerm);
			// lowerBoundForall: k <= z
			final Term lowerBoundForall = SmtUtils.geq(mScript, z, divisor);
			result = SmtUtils.or(mScript, upperBoundForall, lowerBoundForall);
		} else {
			throw new AssertionError("Illegal Quantifier");
		}
		return result;
	}

	private Term replaceModTerm(final EliminationTask inputEt, final DmlPossibility pmt, final TermVariable z,
			final Term divisorAsTerm) {
		final Term modTermReplacement;
		if (SmtUtils.tryToConvertToLiteral(pmt.getOffset()) != null
				&& SmtUtils.tryToConvertToLiteral(pmt.getOffset()).equals(Rational.ZERO)) {
			modTermReplacement = z;
		} else {
			// modTerm: b mod k
			final Term modTerm = SmtUtils.mod(mScript, pmt.getOffset(), divisorAsTerm);
			// sum: z + (b mod k)
			final Term sum = SmtUtils.sum(mScript, SmtSortUtils.getIntSort(mScript), z, modTerm);
			// subtraction: z + (b mod k) - k
			final Term subtraction = SmtUtils.minus(mScript, sum, divisorAsTerm);
			// conditionalOfIte: z + (b mod k) >= k
			final Term conditionalOfIte = SmtUtils.geq(mScript, sum, divisorAsTerm);
			modTermReplacement = SmtUtils.ite(mScript, conditionalOfIte, subtraction, sum);
		}
		final Map<Term, Term> substitutionMaping = Collections.singletonMap(pmt.getDmlSubterm(), modTermReplacement);
		return dissolveIte(Substitution.apply(mMgdScript, substitutionMaping, inputEt.getTerm()));
	}

	/**
	 * Replace `(a*x+b) div K` by `IF ((b mod k) + z < K) THEN ay + (b div k) + nz ELSE ay + (b div k) + nz + 1`
	 */
	private Term replaceDivTerm(final EliminationTask inputEt, final DmlPossibility pmt, final TermVariable y,
			final TermVariable z, final Term divisor, final Term n) {
		// div1 = b div k
		final Term div1 = SmtUtils.divInt(mScript, pmt.getOffset(),
				SmtUtils.constructIntegerValue(mScript, SmtSortUtils.getIntSort(mScript), pmt.getDivisor()));
		// product2 = a*y
		final Term product2 = SmtUtils.mul(mScript, SmtSortUtils.getIntSort(mScript),
				SmtUtils.constructIntegerValue(mScript, SmtSortUtils.getIntSort(mScript), pmt.getCoefficient()), y);
		// sum2 = ay + (b div k)
		final Term sum2 = SmtUtils.sum(mScript, SmtSortUtils.getIntSort(mScript), product2, div1);
		// product3 = nz
		final Term product3 = SmtUtils.mul(mScript, SmtSortUtils.getIntSort(mScript), n, z);
		// sumBeforeFinal = ay + (b div k) + nz
		final Term sumBeforeFinal = SmtUtils.sum(mScript, SmtSortUtils.getIntSort(mScript), sum2, product3);

		final Term divTermReplacement;
		if (SmtUtils.tryToConvertToLiteral(pmt.getOffset()) != null
				&& SmtUtils.tryToConvertToLiteral(pmt.getOffset()).equals(Rational.ZERO)) {
			divTermReplacement = sumBeforeFinal;
		} else {
			// mod1 = b mod k
			final Term mod1 = SmtUtils.mod(mScript, pmt.getOffset(),
					SmtUtils.constructIntegerValue(mScript, SmtSortUtils.getIntSort(mScript), pmt.getDivisor()));
			final Term sum4 = SmtUtils.sum(mScript, SmtSortUtils.getIntSort(mScript), mod1, z);
			final Term iIsZero = SmtUtils.less(mScript, sum4, divisor);
			final Term ifTerm = iIsZero;
			final Term thenTerm = sumBeforeFinal;
			final Term one = SmtUtils.constructIntegerValue(mScript, SmtSortUtils.getIntSort(mScript), BigInteger.ONE);
			final Term elseTerm = SmtUtils.sum(mScript, sumBeforeFinal.getSort(), sumBeforeFinal, one);
			// conditionalOfIte: z + (b mod k) >= k
			divTermReplacement = SmtUtils.ite(mScript, ifTerm, thenTerm, elseTerm);
		}
		final Map<Term, Term> substitutionMaping = Collections.singletonMap(pmt.getDmlSubterm(), divTermReplacement);
		return dissolveIte(Substitution.apply(mMgdScript, substitutionMaping, inputEt.getTerm()));
	}

	private Term applyDivElimination(final EliminationTask inputEt, final DmlPossibility pmt, final TermVariable y,
			final TermVariable z, final Term divisor, final Term inverse) {
		final Term n;
		{
			final BigInteger aAsBigInteger = pmt.getCoefficient();
			final BigInteger aTimesInverse = aAsBigInteger.multiply(pmt.getInverse());
			final BigInteger nAsBigInteger = aTimesInverse.divide(pmt.getDivisor());
			final BigInteger remainderG = aTimesInverse.mod((pmt.getDivisor()).abs());
			assert (aTimesInverse.equals(nAsBigInteger.multiply(pmt.getDivisor()).add(BigInteger.ONE)));
			final BigInteger absRemainderG = remainderG.abs();
			final int absIntRemainderG = absRemainderG.intValue();
			if (absIntRemainderG != 1) {
				throw new AssertionError("Remainder not 1");
			}
			n = SmtUtils.constructIntegerValue(mScript, SmtSortUtils.getIntSort(mScript), nAsBigInteger);
		}

		final Term divReplaced = replaceDivTerm(inputEt, pmt, y, z, divisor, n);
		final Term eliminateeReplaced;
		{
			// product1: y*k
			final Term product1 = SmtUtils.mul(mScript, SmtSortUtils.getIntSort(mScript),
					SmtUtils.constructIntegerValue(mScript, SmtSortUtils.getIntSort(mScript), pmt.getDivisor()), y);
			// product5 = a⁻1*z
			final Term product5 = SmtUtils.mul(mScript, SmtSortUtils.getIntSort(mScript), inverse, z);
			// sum1 = y'*k + a⁻1*z
			final Term sum1 = SmtUtils.sum(mScript, SmtSortUtils.getIntSort(mScript), product1, product5);
			final Map<Term, Term> substitutionMapping = Collections.singletonMap(pmt.getEliminate(), sum1);
			eliminateeReplaced = Substitution.apply(mMgdScript, substitutionMapping, divReplaced);
		}
		final Term interval = constructInterval(inputEt.getQuantifier(), z, divisor);
		return QuantifierUtils.applyDualFiniteConnective(mScript, inputEt.getQuantifier(), eliminateeReplaced,
				interval);
	}

	/**
	 * Represents a term of the form `(+ (* a x) b)`, where
	 * <li>x is the {@link TermVariable} that we want to eliminate, hence called eliminatee,
	 * <li>a is some non-zero integer (called coeffcient of x)
	 * <li>b is some term that must not contain x (called offset).
	 */
	private static class CoeffcientEliminateeOffset {
		final BigInteger mCoefficient;
		final TermVariable mEliminatee;
		final Term mOffset;

		private CoeffcientEliminateeOffset(final BigInteger coefficient, final TermVariable eliminatee,
				final Term offset) {
			super();
			mCoefficient = coefficient;
			mEliminatee = eliminatee;
			mOffset = offset;
		}

		public BigInteger getCoefficient() {
			return mCoefficient;
		}

		public TermVariable getEliminatee() {
			return mEliminatee;
		}

		public Term getOffset() {
			return mOffset;
		}

		public static CoeffcientEliminateeOffset of(final Script script, final TermVariable eliminatee,
				final Term term) {
			final AffineTerm affineTerm = (AffineTerm) new AffineTermTransformer(script).transform(term);
			final Map<Term, Rational> varToCoeff = affineTerm.getVariable2Coefficient();
			final Map<Term, Rational> offsetAsAffineTermMap = new HashMap<>();
			for (final Entry<Term, Rational> entry : varToCoeff.entrySet()) {
				if (entry.getKey() != eliminatee) {
					offsetAsAffineTermMap.put(entry.getKey(), entry.getValue());
				}
			}
			final AffineTerm offsetAsAffineTerm =
					new AffineTerm(affineTerm.getSort(), affineTerm.getConstant(), offsetAsAffineTermMap);
			final Term bAsTerm = offsetAsAffineTerm.toTerm(script);
			if (Arrays.asList(bAsTerm.getFreeVars()).contains(eliminatee)) {
				return null;
			}
			final Rational coefficient = varToCoeff.get(eliminatee);
			if (coefficient == null) {
				return null;
			}
			assert coefficient.denominator().equals(BigInteger.ONE);
			return new CoeffcientEliminateeOffset(coefficient.numerator(), eliminatee, bAsTerm);
		}
	}

	/**
	 * Represents a subterm of the form `(op (+ (* a x) b) K)`, where
	 * <ul>
	 * <li>`op` is either "div" or "mod",
	 * <li>x is the {@link TermVariable} that we want to eliminate, hence called eliminatee,
	 * <li>a is some non-zero integer (called coeffcient of x) that is coprime to K,
	 * <li>b is some term (called offset) that must not contain x,
	 * <li>K is some positive integer that we call the divisor. </ ul> <br />
	 * This subterm will be one candidate for an elimination of x via {@link DualJunctionDml} and contains additional
	 * data that supports the elimination.
	 */
	private static class DmlPossibility {
		/**
		 * Either "div" or "mod"
		 */
		private final String mFunName;
		final BigInteger mDivisor;
		/**
		 * The dualJunct of the elimination input that contains the div/mod subterm we will replace.
		 */
		final Term mContainingDualJunct;
		/**
		 * Term that is the inverse of a in the ring of integers modulo the divisor. The inverse exists always because a
		 * and the divisor are coprime. I.e., this is a term such that (a*mInverse%K)=1 holds.
		 */
		final BigInteger mInverse;
		/**
		 * div/mod subterm that we will replace.
		 */
		final Term mDmlSubterm;
		private final CoeffcientEliminateeOffset mCeo;
		private final boolean mEliminateeOccursInCorrespondingFiniteJunction;

		DmlPossibility(final String funName, final CoeffcientEliminateeOffset ceo, final BigInteger divisor,
				final Term containingDualJunct, final BigInteger inverse, final Term dmlSubterm,
				final boolean eliminateeOccursInCorrespondingFiniteJunction) {
			if (!funName.equals("div") && !funName.equals("mod")) {
				throw new IllegalArgumentException("Neither div nor mod");
			}
			if (funName.equals("mod") && ceo.getCoefficient().compareTo(BigInteger.ZERO) <= 0) {
				throw new IllegalArgumentException("For mod, the coefficient must be positive");
			}
			if (divisor.compareTo(BigInteger.ZERO) < 0) {
				throw new AssertionError("Negative divisors should have been replaced by our normal form.");
			}
			mCeo = ceo;
			mFunName = funName;
			mDivisor = divisor;
			mContainingDualJunct = containingDualJunct;
			mInverse = inverse;
			mDmlSubterm = dmlSubterm;
			mEliminateeOccursInCorrespondingFiniteJunction = eliminateeOccursInCorrespondingFiniteJunction;
		}

		public String getFunName() {
			return mFunName;
		}

		public BigInteger getInverse() {
			return mInverse;
		}

		// The formula containing mod / div is of the form F(ax+b mod k) / F(ax+b div
		// k), i.e. getA() returns
		// the coefficient of x
		public BigInteger getCoefficient() {
			return mCeo.getCoefficient();
		}

		public Term getContainingDualJunct() {
			return mContainingDualJunct;
		}

		// The formula containing mod / div is of the form F(ax+b mod k) / F(ax+b div
		// k), i.e. getB() returns
		// any additional terms which do not contain the quantified variable x
		public Term getOffset() {
			return mCeo.getOffset();
		}

		public TermVariable getEliminate() {
			return mCeo.getEliminatee();
		}

		public Term getDmlSubterm() {
			return mDmlSubterm;
		}

		public BigInteger getDivisor() {
			return mDivisor;
		}

		public boolean doesEliminateeOccurInCorrespondingFiniteJunction() {
			return mEliminateeOccursInCorrespondingFiniteJunction;
		}

	}

}