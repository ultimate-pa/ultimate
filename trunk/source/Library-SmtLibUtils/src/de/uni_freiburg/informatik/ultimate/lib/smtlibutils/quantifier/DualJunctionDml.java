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
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IteRemover;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SubTermFinder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AffineTermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.ArithmeticUtils;

/**
 * Div-mod liberation (DML) for conjunctions (resp. disjunctions). <br>
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Katharina Wagner
 */
public class DualJunctionDml extends DualJunctionQuantifierElimination {

	private static final boolean ENABLE_DIV_ELIMINATION = true;
	//
	/**
	 * TODO 20230305 Matthias: Looks very useful but has surprisingly bad effects on
	 * {@link QuantifierEliminationDivModCrafted#bvToIntFoxExists04}.
	 *
	 */
	private static final boolean EXCLUDE_CORRESPONDING_FINITE_JUNCTIONS = false;

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
			for (final Term dualJunct : dualFiniteJuncts) {
				if (QuantifierUtils.isCorrespondingFiniteJunction(inputEt.getQuantifier(), dualJunct)
						&& EXCLUDE_CORRESPONDING_FINITE_JUNCTIONS) {
					// If this is e.g., a disjunction in a conjunction, we skip the conjunct.
					// Rationale, we will take care of this after applying distributivity and then
					// our chances are higher that the newly introduced variables can be eliminated.
					continue;
				}
				final Predicate<Term> isDivModTerm = (x -> isDivModTerm(x));
				final boolean onlyOutermost = false;
				final Set<Term> divModSubterms = SubTermFinder.find(dualJunct, isDivModTerm, onlyOutermost);
				for (final Term subterm : divModSubterms) {
					final ApplicationTerm appTerm = (ApplicationTerm) subterm;
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
					final CoeffcientEliminateeOffset ceo = CoeffcientEliminateeOffset.of(mScript, eliminatee,
							dividentAsTerm);
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
						final BigInteger tmp = ArithmeticUtils.multiplicativeInverse(ceo.getCoefficient(),
								divisorAsBigInteger);
						// In order to simplify other parts of the algorithm, we want to make sure that
						// the multiplication of coefficient and inverse is always positive. Hence, if
						// the coefficient was negative, we have to take a negative inverse.
						if (ceo.getCoefficient().compareTo(BigInteger.ZERO) < 0) {
							inverse = tmp.subtract(divisorAsBigInteger.abs());
						} else {
							inverse = tmp;
						}
					}
					final DmlPossibility dmlPossibility = new DmlPossibility(
							appTerm.getFunction().getApplicationString(), ceo, divisorAsBigInteger, dualJunct, inverse,
							subterm);
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
			final EliminationResult er;
			if (dmlPossibility.getFunName().equals("mod")) {
				er = applyModElimination(inputEt, dmlPossibility);
			} else if (dmlPossibility.getFunName().equals("div")) {
				if (!ENABLE_DIV_ELIMINATION) {
					continue;
				}
				er = applyDivEliminationWithSmallRemainder(inputEt, dmlPossibility);
			} else {
				throw new AssertionError();
			}
			candidates.add(er);
		}
		if (!candidates.isEmpty()) {
			return candidates.iterator().next();
		}
		return null;
	}

	private EliminationResult applyModElimination(final EliminationTask inputEt, final DmlPossibility pmt)
			throws AssertionError {
		final TermVariable y = mMgdScript.constructFreshTermVariable("y", SmtSortUtils.getIntSort(mScript));
		final TermVariable z = mMgdScript.constructFreshTermVariable("z", SmtSortUtils.getIntSort(mScript));
		final Term divisorAsTerm = SmtUtils.constructIntegerValue(mScript, SmtSortUtils.getIntSort(mScript),
				pmt.getDivisor());
		final Term inverseAsTerm = SmtUtils.constructIntegerValue(mScript, SmtSortUtils.getIntSort(mScript),
				pmt.getInverse());
		final Term modTermReplacement;
		if (SmtUtils.tryToConvertToLiteral(pmt.getOffset()) != null
				&& SmtUtils.tryToConvertToLiteral(pmt.getOffset()).equals(Rational.ZERO)) {
			modTermReplacement = z;
		} else {
			// mod3 = b mod k
			final Term mod3 = SmtUtils.mod(mScript, pmt.getOffset(), divisorAsTerm);
			// sum4 = z + (b mod k)
			final Term sum4 = SmtUtils.sum(mScript, SmtSortUtils.getIntSort(mScript), z, mod3);
			// substr1 = z + (b mod k) - k
			final Term substr1 = SmtUtils.minus(mScript, sum4, divisorAsTerm);
			// conditionalOfIte = z + (b mod k) >= k
			final Term conditionalOfIte = SmtUtils.geq(mScript, sum4, divisorAsTerm);
			modTermReplacement = SmtUtils.ite(mScript, conditionalOfIte, substr1, sum4);
		}
		final BigInteger zeroAsBigInteger = BigInteger.valueOf(0);
		final Term zeroAsTerm = SmtUtils.constructIntegerValue(mScript, SmtSortUtils.getIntSort(mScript),
				zeroAsBigInteger);
		final Map<Term, Term> sub3 = new HashMap<Term, Term>();
		sub3.put(pmt.getDmlSubterm(), modTermReplacement);
		Term termAfterFirstSubstitution = Substitution.apply(mMgdScript, sub3, inputEt.getTerm());
		if (inputEt.getQuantifier() == QuantifiedFormula.EXISTS) {
			// lowerBoundExists = z >= 0
			final Term lowerBoundExists = SmtUtils.geq(mScript, z, zeroAsTerm);
			// upperBoundExists = z < k
			final Term upperBoundExists = SmtUtils.less(mScript, z, divisorAsTerm);
			termAfterFirstSubstitution = SmtUtils.and(mScript, termAfterFirstSubstitution, lowerBoundExists);
			termAfterFirstSubstitution = SmtUtils.and(mScript, termAfterFirstSubstitution, upperBoundExists);
		} else if (inputEt.getQuantifier() == QuantifiedFormula.FORALL) {
			// upperBoundForall = z < 0
			final Term upperBoundForall = SmtUtils.less(mScript, z, zeroAsTerm);
			// lowerBoundForall = z >= k
			final Term lowerBoundForall = SmtUtils.geq(mScript, z, divisorAsTerm);
			termAfterFirstSubstitution = SmtUtils.or(mScript, termAfterFirstSubstitution, upperBoundForall);
			termAfterFirstSubstitution = SmtUtils.or(mScript, termAfterFirstSubstitution, lowerBoundForall);
		} else {
			throw new AssertionError("Illegal Quantifier");
		}

		final Term termWithRemovedITE = new IteRemover(mMgdScript).transform(termAfterFirstSubstitution);
		// product1 = y'*k
		final Term product1 = SmtUtils.mul(mScript, SmtSortUtils.getIntSort(mScript), divisorAsTerm, y);
		// product2 = a⁻1*z
		final Term product2 = SmtUtils.mul(mScript, SmtSortUtils.getIntSort(mScript), inverseAsTerm, z);
		// sum1 = y'*k + a⁻1*z
		final Term sum1 = SmtUtils.sum(mScript, SmtSortUtils.getIntSort(mScript), product1, product2);
		final Map<Term, Term> sub1 = new HashMap<Term, Term>();
		sub1.put(pmt.getEliminate(), sum1);
		final Term resultTerm = Substitution.apply(mMgdScript, sub1, termWithRemovedITE);
		final NnfTransformer termNnf = new NnfTransformer(mMgdScript, mServices, QuantifierHandling.KEEP);
		final Term resultTermNnf = termNnf.transform(resultTerm);
		final Set<TermVariable> remainingEliminatees = new HashSet<>(inputEt.getEliminatees());
		remainingEliminatees.remove(pmt.getEliminate());
		final EliminationTask eliminationTask = new EliminationTask(inputEt.getQuantifier(), remainingEliminatees,
				resultTermNnf, inputEt.getContext());
		final Set<TermVariable> newEliminatees = new HashSet<>();
		newEliminatees.add(y);
		newEliminatees.add(z);
		final EliminationResult resultWithoutXInMod = new EliminationResult(eliminationTask, newEliminatees);
		return resultWithoutXInMod;
	}

	public EliminationResult helpReturnForEliminatingDiv(final EliminationTask inputEt, final DmlPossibility pmt,
			final Map<Term, Term> sub1, final Term termJunctSubst, final TermVariable y, final TermVariable z) {
		final Term[] dualFiniteJuncts = QuantifierUtils.getDualFiniteJuncts(inputEt.getQuantifier(), inputEt.getTerm());
		final BigInteger zeroAsBigInteger = BigInteger.valueOf(0);
		final Term zeroAsTerm = SmtUtils.constructIntegerValue(mScript, SmtSortUtils.getIntSort(mScript),
				zeroAsBigInteger);
		Term termAfterFirstSubstitution = QuantifierUtils.getAbsorbingElement(mScript, inputEt.getQuantifier());
		for (final Term junct : dualFiniteJuncts) {
			if (!(junct == pmt.getContainingDualJunct())) {
				termAfterFirstSubstitution = QuantifierUtils.applyDualFiniteConnective(mScript, inputEt.getQuantifier(),
						termAfterFirstSubstitution, junct);
			}
		}
		termAfterFirstSubstitution = QuantifierUtils.applyDualFiniteConnective(mScript, inputEt.getQuantifier(),
				termAfterFirstSubstitution, termJunctSubst);
		if (inputEt.getQuantifier() == QuantifiedFormula.EXISTS) {
			// lowerBoundExists = z >= 0
			final Term lowerBoundExists = SmtUtils.geq(mScript, z, zeroAsTerm);
			// upperBoundExists = z < k
			final Term upperBoundExists = SmtUtils.less(mScript, z,
					SmtUtils.constructIntegerValue(mScript, SmtSortUtils.getIntSort(mScript), pmt.getDivisor().abs()));
			termAfterFirstSubstitution = SmtUtils.and(mScript, termAfterFirstSubstitution, lowerBoundExists);
			termAfterFirstSubstitution = SmtUtils.and(mScript, termAfterFirstSubstitution, upperBoundExists);
		} else if (inputEt.getQuantifier() == QuantifiedFormula.FORALL) {
			// upperBoundForall = z < 0
			final Term upperBoundForall = SmtUtils.less(mScript, z, zeroAsTerm);
			// lowerBoundForall = z >= k
			final Term lowerBoundForall = SmtUtils.geq(mScript, z,
					SmtUtils.constructIntegerValue(mScript, SmtSortUtils.getIntSort(mScript), pmt.getDivisor().abs()));
			termAfterFirstSubstitution = SmtUtils.or(mScript, termAfterFirstSubstitution, upperBoundForall);
			termAfterFirstSubstitution = SmtUtils.or(mScript, termAfterFirstSubstitution, lowerBoundForall);
		} else {
			throw new AssertionError("Illegal Quantifier");
		}
		final Term resultTerm = Substitution.apply(mMgdScript, sub1, termAfterFirstSubstitution);
		final NnfTransformer TermNnf = new NnfTransformer(mMgdScript, mServices, QuantifierHandling.KEEP);
		final Term ResultTermNnf = TermNnf.transform(resultTerm);
		final Set<TermVariable> remainingEliminatees = new HashSet<>(inputEt.getEliminatees());
		remainingEliminatees.remove(pmt.getEliminate());
		final EliminationTask eliminationTask = new EliminationTask(inputEt.getQuantifier(), remainingEliminatees,
				ResultTermNnf, inputEt.getContext());
		final Set<TermVariable> newEliminatees = new HashSet<>();
		newEliminatees.add(y);
		newEliminatees.add(z);
		final EliminationResult resultWithoutXInDiv = new EliminationResult(eliminationTask, newEliminatees);
		return resultWithoutXInDiv;
	}

	private EliminationResult applyDivEliminationWithSmallA(final EliminationTask inputEt, final DmlPossibility pmt)
			throws AssertionError {
		final BigInteger aAsBigInteger = pmt.getCoefficient();
		final int aAsInt = aAsBigInteger.intValue();
		final BigInteger absOfAAsBigInteger = aAsBigInteger.abs();
		final int absAAsInt = absOfAAsBigInteger.intValue();
		if (absAAsInt > 8) {
			return null;
		}
		final TermVariable y = mMgdScript.constructFreshTermVariable("y", SmtSortUtils.getIntSort(mScript));
		final TermVariable z = mMgdScript.constructFreshTermVariable("z", SmtSortUtils.getIntSort(mScript));
		// product1 = y'*k
		final Term product1 = SmtUtils.mul(mScript, SmtSortUtils.getIntSort(mScript),
				SmtUtils.constructIntegerValue(mScript, SmtSortUtils.getIntSort(mScript), pmt.getDivisor()), y);
		// sum1 = y'*k + z
		final Term sum1 = SmtUtils.sum(mScript, SmtSortUtils.getIntSort(mScript), product1, z);
		final Map<Term, Term> sub1 = new HashMap<Term, Term>();
		sub1.put(pmt.getEliminate(), sum1);
		// div1 = b div k
		final Term div1 = SmtUtils.divInt(mScript, pmt.getOffset(),
				SmtUtils.constructIntegerValue(mScript, SmtSortUtils.getIntSort(mScript), pmt.getDivisor()));
		// product2 = a*y
		final Term product2 = SmtUtils.mul(mScript, SmtSortUtils.getIntSort(mScript),
				SmtUtils.constructIntegerValue(mScript, SmtSortUtils.getIntSort(mScript), pmt.getCoefficient()), y);
		// sum2 = ay + (b div k)
		final Term sum2 = SmtUtils.sum(mScript, SmtSortUtils.getIntSort(mScript), product2, div1);
		final List<Term> termJunctSubstList = new ArrayList<>();
		if (aAsInt > 0) {
			for (int i = 0; i < aAsInt; i++) {
				final BigInteger iAsBigInteger = BigInteger.valueOf(i);
				final Term iAsTerm = SmtUtils.constructIntegerValue(mScript, SmtSortUtils.getIntSort(mScript),
						iAsBigInteger);
				// sum3 = ay + (b div k) + i
				final Term sum3 = SmtUtils.sum(mScript, SmtSortUtils.getIntSort(mScript), sum2, iAsTerm);
				final Map<Term, Term> subJunct = new HashMap<Term, Term>();
				subJunct.put(pmt.getDmlSubterm(), sum3);
				final Term divConjunctSub = Substitution.apply(mMgdScript, subJunct, pmt.getContainingDualJunct());
				termJunctSubstList.add(divConjunctSub);
			}
		} else {
			for (int i = aAsInt; i < 1; i++) {
				final BigInteger iAsBigInteger = BigInteger.valueOf(i);
				final Term iAsTerm = SmtUtils.constructIntegerValue(mScript, SmtSortUtils.getIntSort(mScript),
						iAsBigInteger);
				// sum3 = ay + (b div k) + i
				final Term sum3 = SmtUtils.sum(mScript, SmtSortUtils.getIntSort(mScript), sum2, iAsTerm);
				final Map<Term, Term> subJunct = new HashMap<Term, Term>();
				subJunct.put(pmt.getDmlSubterm(), sum3);
				final Term divConjunctSub = Substitution.apply(mMgdScript, subJunct, pmt.getContainingDualJunct());
				termJunctSubstList.add(divConjunctSub);
			}
		}
		final Term termJunctSubst = QuantifierUtils.applyCorrespondingFiniteConnective(mScript, inputEt.getQuantifier(),
				termJunctSubstList);
		final EliminationResult resultWithoutXInDiv = helpReturnForEliminatingDiv(inputEt, pmt, sub1, termJunctSubst, y,
				z);
		return resultWithoutXInDiv;
	}

	private EliminationResult applyDivEliminationWithSmallRemainder(final EliminationTask inputEt,
			final DmlPossibility pmt) throws AssertionError {
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
		final Term nAsTerm = SmtUtils.constructIntegerValue(mScript, SmtSortUtils.getIntSort(mScript), nAsBigInteger);
		if (absIntRemainderG > 8) {
			return null;
		}
		final TermVariable y = mMgdScript.constructFreshTermVariable("y", SmtSortUtils.getIntSort(mScript));
		final TermVariable z = mMgdScript.constructFreshTermVariable("z", SmtSortUtils.getIntSort(mScript));
		final Term inverseAsTerm = SmtUtils.constructIntegerValue(mScript, SmtSortUtils.getIntSort(mScript),
				pmt.getInverse());
		final Term absDivisorAsTerm = SmtUtils.constructIntegerValue(mScript, SmtSortUtils.getIntSort(mScript),
				pmt.getDivisor().abs());
		// product1 = y'*k
		final Term product1 = SmtUtils.mul(mScript, SmtSortUtils.getIntSort(mScript),
				SmtUtils.constructIntegerValue(mScript, SmtSortUtils.getIntSort(mScript), pmt.getDivisor()), y);
		// product5 = a⁻1*z
		final Term product5 = SmtUtils.mul(mScript, SmtSortUtils.getIntSort(mScript), inverseAsTerm, z);
		// sum1 = y'*k + a⁻1*z
		final Term sum1 = SmtUtils.sum(mScript, SmtSortUtils.getIntSort(mScript), product1, product5);
		final Map<Term, Term> sub1 = new HashMap<Term, Term>();
		sub1.put(pmt.getEliminate(), sum1);
		// div1 = b div k
		final Term div1 = SmtUtils.divInt(mScript, pmt.getOffset(),
				SmtUtils.constructIntegerValue(mScript, SmtSortUtils.getIntSort(mScript), pmt.getDivisor()));
		// product2 = a*y
		final Term product2 = SmtUtils.mul(mScript, SmtSortUtils.getIntSort(mScript),
				SmtUtils.constructIntegerValue(mScript, SmtSortUtils.getIntSort(mScript), pmt.getCoefficient()), y);
		// sum2 = ay + (b div k)
		final Term sum2 = SmtUtils.sum(mScript, SmtSortUtils.getIntSort(mScript), product2, div1);
		// product3 = nz
		final Term product3 = SmtUtils.mul(mScript, SmtSortUtils.getIntSort(mScript), nAsTerm, z);
		// sumBeforeFinal = ay + (b div k) + nz
		final Term sumBeforeFinal = SmtUtils.sum(mScript, SmtSortUtils.getIntSort(mScript), sum2, product3);
		final List<Term> termJunctSubstList = new ArrayList<>();
		for (int i = 0; i <= absIntRemainderG; i++) {
			final BigInteger iAsBigInteger = BigInteger.valueOf(i);
			final Term iAsTerm = SmtUtils.constructIntegerValue(mScript, SmtSortUtils.getIntSort(mScript),
					iAsBigInteger);
			// sum3 = ay + (b div k) + nz + i
			final Term sum3 = SmtUtils.sum(mScript, SmtSortUtils.getIntSort(mScript), sumBeforeFinal, iAsTerm);
			final Map<Term, Term> subJunct = new HashMap<Term, Term>();
			subJunct.put(pmt.getDmlSubterm(), sum3);
			Term divConjunctSub = Substitution.apply(mMgdScript, subJunct, pmt.getContainingDualJunct());
			// mod1 = b mod k
			final Term mod1 = SmtUtils.mod(mScript, pmt.getOffset(),
					SmtUtils.constructIntegerValue(mScript, SmtSortUtils.getIntSort(mScript), pmt.getDivisor()));
			if (i == 0) {
				final Term sum4 = SmtUtils.sum(mScript, SmtSortUtils.getIntSort(mScript), mod1, z);
				Term iIsZero = SmtUtils.less(mScript, sum4, absDivisorAsTerm);
				iIsZero = QuantifierUtils.negateIfUniversal(mScript, inputEt.getQuantifier(), iIsZero);
				divConjunctSub = QuantifierUtils.applyDualFiniteConnective(mScript, inputEt.getQuantifier(),
						divConjunctSub, iIsZero);
			} else {
				final Term sum4 = SmtUtils.sum(mScript, SmtSortUtils.getIntSort(mScript), mod1, z);
				Term iIsOne = SmtUtils.leq(mScript, absDivisorAsTerm, sum4);
				iIsOne = QuantifierUtils.negateIfUniversal(mScript, inputEt.getQuantifier(), iIsOne);
				divConjunctSub = QuantifierUtils.applyDualFiniteConnective(mScript, inputEt.getQuantifier(),
						divConjunctSub, iIsOne);
			}
			termJunctSubstList.add(divConjunctSub);
		}
		final Term termJunctSubst = QuantifierUtils.applyCorrespondingFiniteConnective(mScript, inputEt.getQuantifier(),
				termJunctSubstList);
		final EliminationResult resultWithoutXInDiv = helpReturnForEliminatingDiv(inputEt, pmt, sub1, termJunctSubst, y,
				z);
		return resultWithoutXInDiv;
	}

	/**
	 * Return true if the input is `div` term or a `mod` term.
	 */
	private boolean isDivModTerm(final Term term) {
		if (term instanceof ApplicationTerm) {
			final FunctionSymbol fun = ((ApplicationTerm) term).getFunction();
			if (fun.getApplicationString().equals("div") || fun.getApplicationString().equals("mod")) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Represents a term of the form `(+ (* a x) b)`, where
	 * <li>x is the {@link TermVariable} that we want to eliminate, hence called
	 * eliminatee,
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
			final AffineTerm offsetAsAffineTerm = new AffineTerm(affineTerm.getSort(), affineTerm.getConstant(),
					offsetAsAffineTermMap);
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
	 * <li>x is the {@link TermVariable} that we want to eliminate, hence called
	 * eliminatee,
	 * <li>a is some non-zero integer (called coeffcient of x) that is coprime to K,
	 * <li>b is some term (called offset) that must not contain x,
	 * <li>K is some integer that we call the divisor. </ ul> <br /> This subterm will be
	 * one candidate for an elimination of x via {@link DualJunctionDml} and
	 * contains additional data that supports the elimination.
	 */
	private static class DmlPossibility {
		/**
		 * Either "div" or "mod"
		 */
		private final String mFunName;
		final BigInteger mDivisor;
		/**
		 * The dualJunct of the elimination input that contains the div/mod subterm we
		 * will replace.
		 */
		final Term mContainingDualJunct;
		/**
		 * Term that is the inverse of a in the ring of integers modulo the divisor. The
		 * inverse exists always because a and the divisor are coprime. I.e., this is a
		 * term such that (a*mInverse%K)=1 holds.
		 */
		final BigInteger mInverse;
		/**
		 * div/mod subterm that we will replace.
		 */
		final Term mDmlSubterm;
		private final CoeffcientEliminateeOffset mCeo;

		DmlPossibility(final String funName, final CoeffcientEliminateeOffset ceo, final BigInteger divisor,
				final Term containingDualJunct, final BigInteger inverse, final Term dmlSubterm) {
			if (!funName.equals("div") && !funName.equals("mod")) {
				throw new IllegalArgumentException("Neither div nor mod");
			}
			if (funName.equals("mod") && ceo.getCoefficient().compareTo(BigInteger.ZERO) <= 0) {
				throw new IllegalArgumentException("For mod, the coefficient must be positive");
			}
			mCeo = ceo;
			mFunName = funName;
			mDivisor = divisor;
			mContainingDualJunct = containingDualJunct;
			mInverse = inverse;
			mDmlSubterm = dmlSubterm;
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
	}

}