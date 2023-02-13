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
		final Term[] dualFiniteJuncts = QuantifierUtils.getDualFiniteJuncts(inputEt.getQuantifier(),
				inputEt.getTerm());
		for (final TermVariable eliminatee : inputEt.getEliminatees()) {
			// Iterate over all conjuncts
			for (final Term conjunct : dualFiniteJuncts) {
				final Predicate<Term> isDivModTerm = (x -> isDivModTerm(x));
				final boolean onlyOutermost = false;
				final Set<Term> divModSubterms = SubTermFinder.find(conjunct, isDivModTerm, onlyOutermost);
				for (final Term subterm : divModSubterms) {
					if (Arrays.asList(subterm.getFreeVars()).contains(eliminatee)) {
						final ApplicationTerm appTerm = (ApplicationTerm) subterm;
						assert appTerm.getFunction().getApplicationString().equals("div")
								|| appTerm.getFunction().getApplicationString().equals("mod");
						assert appTerm.getParameters().length == 2;
						final Term dividentAsTerm = appTerm.getParameters()[0];
						final Term divisorAsTerm = appTerm.getParameters()[1];
						if (!Arrays.asList(dividentAsTerm.getFreeVars()).contains(eliminatee)) {
							continue;
						}
						if (Arrays.asList(divisorAsTerm.getFreeVars()).contains(eliminatee)) {
							continue;
						}
						final AffineTerm dividentAsAffineTerm = (AffineTerm) new AffineTermTransformer(mScript)
								.transform(dividentAsTerm);
						final Map<Term, Rational> varToCoeff = dividentAsAffineTerm.getVariable2Coefficient();
						final Map<Term, Rational> bAsAffineTermMap = new HashMap<>();
						for (final Entry<Term, Rational> entry : varToCoeff.entrySet()) {
							if (entry.getKey() != eliminatee) {
								bAsAffineTermMap.put(entry.getKey(), entry.getValue());
							}
						}
						final AffineTerm bAsAffineTerm = new AffineTerm(dividentAsAffineTerm.getSort(),
								dividentAsAffineTerm.getConstant(), bAsAffineTermMap);
						final Term bAsTerm = bAsAffineTerm.toTerm(mScript);
						if (Arrays.asList(bAsTerm.getFreeVars()).contains(eliminatee)) {
							continue;
						}
						final Rational aAsRational = varToCoeff.get(eliminatee);
						if (aAsRational == null) {
							continue;
						}
						assert aAsRational.denominator().equals(BigInteger.ONE);
						final BigInteger aAsBigInteger = aAsRational.numerator();
						final AffineTerm divisorAsAffineTerm = (AffineTerm) new AffineTermTransformer(mScript)
								.transform(divisorAsTerm);
						final Rational divisorAsRational = divisorAsAffineTerm.getConstant();
						if (!divisorAsAffineTerm.getVariable2Coefficient().isEmpty()) {
							continue;
						}
						if (divisorAsRational.numerator().equals(BigInteger.valueOf(0))) {
							continue;
						}
						assert divisorAsRational.denominator().equals(BigInteger.ONE);
						final BigInteger divisorAsBigInteger = divisorAsRational.numerator();
						BigInteger inverse;
						final Term modConjunct = conjunct;
						final Term subtermWithMod = subterm;
						final TermVariable eliminate = eliminatee;
						if ((divisorAsBigInteger.gcd(aAsBigInteger)).equals(BigInteger.valueOf(1))) {
							inverse = ArithmeticUtils.extendedEuclidean(aAsBigInteger, divisorAsBigInteger);
							final DmlPossibility dmlPossibility = new DmlPossibility(
									appTerm.getFunction().getApplicationString(), aAsBigInteger, bAsTerm,
									divisorAsBigInteger, modConjunct, inverse, subtermWithMod, eliminate);
							result.add(dmlPossibility);
						}
					}
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
		// temporary solution: pick first mod term
		for (final DmlPossibility dmlPossibility : possibilities) {
			if (dmlPossibility.getFunName().equals("mod")) {
				return applyModElimination(inputEt, dmlPossibility);
			}
		}
		return null;
	}

	private EliminationResult applyModElimination(final EliminationTask inputEt, final DmlPossibility pmt)
			throws AssertionError {
		final Term[] conjuncts = QuantifierUtils.getDualFiniteJuncts(inputEt.getQuantifier(), inputEt.getTerm());
		final TermVariable y = mMgdScript.constructFreshTermVariable("y", SmtSortUtils.getIntSort(mScript));
		final TermVariable z = mMgdScript.constructFreshTermVariable("z", SmtSortUtils.getIntSort(mScript));
		final Term divisorAsTerm = SmtUtils.constructIntegerValue(mScript, SmtSortUtils.getIntSort(mScript),
				pmt.getDivisor());
		final Term inverseAsTerm = SmtUtils.constructIntegerValue(mScript, SmtSortUtils.getIntSort(mScript),
				pmt.getInverse());
		final Term aAsTerm = SmtUtils.constructIntegerValue(mScript, SmtSortUtils.getIntSort(mScript), pmt.getA());
		// product3 = a*x
		final Term product3 = SmtUtils.mul(mScript, SmtSortUtils.getIntSort(mScript), aAsTerm, pmt.getEliminate());
		// sum2 = a*x + b
		final Term sum2 = SmtUtils.sum(mScript, SmtSortUtils.getIntSort(mScript), product3, pmt.getB());
		// mod1 = a*x + b mod k
		final Term mod1 = SmtUtils.mod(mScript, sum2, divisorAsTerm);
		final Term modTermReplacement;
		if (SmtUtils.tryToConvertToLiteral(pmt.getB()) != null
				&& SmtUtils.tryToConvertToLiteral(pmt.getB()).equals(Rational.ZERO)) {
			modTermReplacement = z;
		} else {
			// mod3 = b mod k
			final Term mod3 = SmtUtils.mod(mScript, pmt.getB(), divisorAsTerm);
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
		// for A-Quantifier z < 0 and z >= k is necessary
		final Map<Term, Term> sub3 = new HashMap<Term, Term>();
		sub3.put(mod1, modTermReplacement);
		Term termAfterFirstSubstitution = QuantifierUtils.getAbsorbingElement(mScript, inputEt.getQuantifier());
		// Term termAfterFirstSubstitution = mScript.term("true");
		for (final Term conjunct : conjuncts) {
			if (conjunct == pmt.getContainingDualJunct()) {
				final Term modConjunctSub = Substitution.apply(mMgdScript, sub3, conjunct);
				termAfterFirstSubstitution = QuantifierUtils.applyDualFiniteConnective(mScript, inputEt.getQuantifier(),
						termAfterFirstSubstitution, modConjunctSub);
			} else {
				termAfterFirstSubstitution = QuantifierUtils.applyDualFiniteConnective(mScript, inputEt.getQuantifier(),
						termAfterFirstSubstitution, conjunct);
			}
		}
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
		final NnfTransformer TermNnf = new NnfTransformer(mMgdScript, mServices, QuantifierHandling.KEEP);
		final Term ResultTermNnf = TermNnf.transform(resultTerm);
		final Set<TermVariable> remainingEliminatees = new HashSet<>(inputEt.getEliminatees());
		remainingEliminatees.remove(pmt.getEliminate());
		final EliminationTask eliminationTask = new EliminationTask(inputEt.getQuantifier(), remainingEliminatees,
				ResultTermNnf, inputEt.getContext());
		final Set<TermVariable> newEliminatees = new HashSet<>();
		newEliminatees.add(y);
		newEliminatees.add(z);
		final EliminationResult resultWithoutXInMod = new EliminationResult(eliminationTask, newEliminatees);
		return resultWithoutXInMod;
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
	 * Represents a subterm of the form `(op (+ (* a x) b) K)`, where
	 * <li>`op` is either "div" or "mod",
	 * <li>x is the {@link TermVariable} that we want to eliminate, hence called
	 * eliminatee,
	 * <li>a is some integer (called coeffcient of x) that is coprime to K,
	 * <li>b is some term that must not contain x,
	 * <li>K is some integer that we call the divisor. This subterm will be one
	 * candidate for an elimination of x via {@link DualJunctionDml} and contains
	 * additional data that supports the elimination.
	 */
	private class DmlPossibility {
		/**
		 * Either "div" or "mod"
		 */
		private final String mFunName;
		/**
		 * Coefficient of eliminatee
		 */
		final BigInteger mA;
		/**
		 * Other summand besides a*x
		 */
		final Term mB;
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
		final TermVariable mEliminatee;

		DmlPossibility(final String funName, final BigInteger a, final Term b, final BigInteger divisor,
				final Term containingDualJunct, final BigInteger inverse, final Term dmlSubterm,
				final TermVariable eliminatee) {
			if (!funName.equals("div") && !funName.equals("mod")) {
				throw new IllegalArgumentException("Neither div nor mod");
			}
			if (funName.equals("mod") && a.compareTo(BigInteger.ZERO) <= 0) {
				throw new IllegalArgumentException("For mod, the coefficient must be positive");
			}

			mFunName = funName;
			mA = a;
			mB = b;
			mDivisor = divisor;
			mContainingDualJunct = containingDualJunct;
			mInverse = inverse;
			mDmlSubterm = dmlSubterm;
			mEliminatee = eliminatee;
		}

		public String getFunName() {
			return mFunName;
		}

		public BigInteger getInverse() {
			return mInverse;
		}

		// The formula containing mod is of the form F(ax+b mod k), i.e. getA() returns
		// the coefficient of x
		public BigInteger getA() {
			return mA;
		}

		public Term getContainingDualJunct() {
			return mContainingDualJunct;
		}

		// The formula containing mod is of the form F(ax+b mod k), i.e. getB() returns
		// any additional terms which do not contain the quantified variable x
		public Term getB() {
			return mB;
		}

		public TermVariable getEliminate() {
			return mEliminatee;
		}

		public Term getDmlSubterm() {
			return mDmlSubterm;
		}

		public BigInteger getDivisor() {
			return mDivisor;
		}
	}

}