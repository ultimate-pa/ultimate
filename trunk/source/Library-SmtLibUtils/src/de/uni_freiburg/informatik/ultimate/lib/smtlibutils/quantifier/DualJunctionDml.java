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
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
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
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.ArithmeticUtils;

/**
 * Div-mod liberation (DML) for conjunctions (resp. disjunctions).
 * <br>
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Katharina Wagner
 */
final class partsOfModTerm {
        final BigInteger mAAsBigInteger;
        final Term mBAsTerm;
        final BigInteger mDivisorAsBigInteger;
        final Term mModConjunct;
        final BigInteger mInverse;
        final Term mSubtermWithMod;
        final TermVariable mXEliminate;

        partsOfModTerm(final BigInteger mAAsBigInteger, final Term mBAsTerm, final BigInteger mDivisorAsBigInteger, final Term mModConjunct, final BigInteger mInverse, final Term mSubtermWithMod, final TermVariable mXEliminate) {
            this.mAAsBigInteger = mAAsBigInteger;
            this.mBAsTerm = mBAsTerm;
            this.mDivisorAsBigInteger = mDivisorAsBigInteger;
            this.mModConjunct = mModConjunct;
            this.mInverse = mInverse;
            this.mSubtermWithMod = mSubtermWithMod;
            this.mXEliminate = mXEliminate;
        }



	public BigInteger getInverse() {
		return mInverse;
	}

	public BigInteger getA() {
		return mAAsBigInteger;
	}

	public Term getModConjunct() {
		return mModConjunct;
	}

	public Term getB() {
		return mBAsTerm;
	}

	public TermVariable getXEliminate() {
		return mXEliminate;
	}

	public Term getSubtermWithMod() {
		return mSubtermWithMod;
	}

	public BigInteger getDivisor() {
		return mDivisorAsBigInteger;
	}

	}






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

    public partsOfModTerm findAllComponents(final EliminationTask inputEt) {
        final Term[] conjuncts = QuantifierUtils.getDualFiniteJunction(inputEt.getQuantifier(), inputEt.getTerm());
        for (final TermVariable eliminatee : inputEt.getEliminatees()) {
	    // Iterate over all conjuncts
			for (final Term conjunct : conjuncts) {
				final Set<Term> moduloSubterms;
				final Predicate<Term> isModTerm = (x -> isModTerm(x));
                final boolean onlyOutermost = false;
                moduloSubterms = SubTermFinder.find(conjunct, isModTerm, onlyOutermost);
				for (final Term subterm : moduloSubterms) {
					if (Arrays.asList(subterm.getFreeVars()).contains(eliminatee)) {
						final ApplicationTerm appTerm = (ApplicationTerm) subterm;
						assert appTerm.getFunction().getApplicationString().equals("mod");
						assert appTerm.getParameters().length == 2;
						final Term dividentAsTerm = appTerm.getParameters()[0];
						final Term divisorAsTerm = appTerm.getParameters()[1];
						if (!Arrays.asList(dividentAsTerm.getFreeVars()).contains(eliminatee)) {
							continue;
						}
						if (Arrays.asList(divisorAsTerm.getFreeVars()).contains(eliminatee)) {
							continue;
						}
						final AffineTerm dividentAsAffineTerm = (AffineTerm) new AffineTermTransformer(mScript).transform(dividentAsTerm);
						final Map<Term, Rational> varToCoeff = dividentAsAffineTerm.getVariable2Coefficient();
						final Map<Term, Rational> bAsAffineTermMap = new HashMap<>();
						for (final Entry<Term, Rational> entry : varToCoeff.entrySet()) {
							if (entry.getKey() != eliminatee) {
								bAsAffineTermMap.put(entry.getKey(), entry.getValue());
							}
						}
						final AffineTerm bAsAffineTerm = new AffineTerm(dividentAsAffineTerm.getSort(), dividentAsAffineTerm.getConstant(), bAsAffineTermMap);
						final Term bAsTerm = bAsAffineTerm.toTerm(mScript);
						if (Arrays.asList(bAsTerm.getFreeVars()).contains(eliminatee)) {
							continue;
						}
						final Rational aAsRational = varToCoeff.get(eliminatee);
						if (aAsRational == null) {
							continue;
						}
						final Rational bAsRational = dividentAsAffineTerm.getConstant();
						assert aAsRational.denominator().equals(BigInteger.ONE);
						BigInteger divisorAsBigInteger;
				        BigInteger aAsBigInteger;
				        BigInteger bAsBigInteger;
						aAsBigInteger = aAsRational.numerator();
						bAsBigInteger = bAsRational.numerator();
						final AffineTerm divisorAsAffineTerm = (AffineTerm) new AffineTermTransformer(mScript).transform(divisorAsTerm);
						final Rational divisorAsRational = divisorAsAffineTerm.getConstant();
						if (!divisorAsAffineTerm.getVariable2Coefficient().isEmpty()) {
							continue;
						}
						if (divisorAsRational.numerator().equals(BigInteger.valueOf(0))) {
                        	continue;
                        }
						assert divisorAsRational.denominator().equals(BigInteger.ONE);
                        divisorAsBigInteger = divisorAsRational.numerator();
                        Term modConjunct;
                        BigInteger inverse;
                        TermVariable xEliminate;
                        Term subtermWithMod;
                        modConjunct = conjunct;
                        subtermWithMod = subterm;
                        xEliminate = eliminatee;
                        if ((divisorAsBigInteger.gcd(aAsBigInteger)).equals(BigInteger.valueOf(1))) {
                        	inverse = ArithmeticUtils.extendedEuclidean(aAsBigInteger, divisorAsBigInteger);
                        	final partsOfModTerm returnSeven = new partsOfModTerm(aAsBigInteger, bAsTerm, divisorAsBigInteger, modConjunct, inverse, subtermWithMod, xEliminate);
                        	//final partsOfModTerm<BigInteger, BigInteger, BigInteger, Term, BigInteger, Term, TermVariable> returnSeven = new partsOfModTerm<>(aAsBigInteger, bAsBigInteger, divisorAsBigInteger, modConjunct, inverse, subtermWithMod, xEliminate);
                        	return returnSeven;
                        }
					}
				}
			}
        }
        return null;
    }







	@Override
	public EliminationResult tryToEliminate(final EliminationTask inputEt) {
        final Term[] conjuncts = QuantifierUtils.getDualFiniteJunction(inputEt.getQuantifier(), inputEt.getTerm());
        final partsOfModTerm inputSeven = findAllComponents(inputEt);
        //final partsOfModTerm<BigInteger, BigInteger, BigInteger, Term, BigInteger, Term, TermVariable> inputSeven = findAllComponents(inputEt);
        if (inputSeven == null){
        	return null;
        }
        final TermVariable y = mMgdScript.constructFreshTermVariable("y", SmtSortUtils.getIntSort(mScript));
	    final TermVariable z = mMgdScript.constructFreshTermVariable("z", SmtSortUtils.getIntSort(mScript));
	    BigInteger divisorAsBigInteger;
        BigInteger aAsBigInteger;
        final BigInteger bAsBigInteger;
        Term modConjunct;
        BigInteger inverse;
        Term subtermWithMod;
        TermVariable xEliminate;
        Term bAsTerm;
        aAsBigInteger = inputSeven.getA();
        //bAsBigInteger = inputSeven.getB();
        bAsTerm = inputSeven.getB();
        divisorAsBigInteger = inputSeven.getDivisor();
        modConjunct = inputSeven.getModConjunct();
        inverse = inputSeven.getInverse();
        subtermWithMod = inputSeven.getSubtermWithMod();
        xEliminate = inputSeven.getXEliminate();
        final Term divisorAsTerm = SmtUtils.constructIntegerValue(mScript, SmtSortUtils.getIntSort(mScript), divisorAsBigInteger);
        final Term inverseAsTerm = SmtUtils.constructIntegerValue(mScript, SmtSortUtils.getIntSort(mScript), inverse);
        //final Term bAsTerm = SmtUtils.constructIntegerValue(mScript, SmtSortUtils.getIntSort(mScript), bAsBigInteger);
        final Term aAsTerm = SmtUtils.constructIntegerValue(mScript, SmtSortUtils.getIntSort(mScript), aAsBigInteger);
        // product1 = y'*k
        final Term product1 = SmtUtils.mul(mScript, SmtSortUtils.getIntSort(mScript), divisorAsTerm, y);
        // product2 = a⁻1*z
        final Term product2 = SmtUtils.mul(mScript, SmtSortUtils.getIntSort(mScript), inverseAsTerm, z);
        // sum1 = y'*k + a⁻1*z
        final Term sum1 = SmtUtils.sum(mScript, SmtSortUtils.getIntSort(mScript), product1, product2);
        // product3 = a*x
        final Term product3 = SmtUtils.mul(mScript, SmtSortUtils.getIntSort(mScript), aAsTerm, xEliminate);
        // sum2 = a*x + b
        final Term sum2 = SmtUtils.sum(mScript, SmtSortUtils.getIntSort(mScript), product3, bAsTerm);
        // mod1 = a*x + b mod k
        final Term mod1 = SmtUtils.mod(mScript, sum2, divisorAsTerm);
        // sum3 = z + b
        final Term sum3 = SmtUtils.sum(mScript, SmtSortUtils.getIntSort(mScript), z, bAsTerm);
        // mod2 = z + b mod k
        //final Term mod2 = SmtUtils.mod(mScript, sum3, divisorAsTerm);
        final Map<Term, Term> sub1 = new HashMap<Term, Term>();
        sub1.put(xEliminate, sum1);
        Term termWithITE;
        // mod3 = b mod k
        final Term mod3 = SmtUtils.mod(mScript, bAsTerm, divisorAsTerm);
        // sum4 = z + (b mod k)
        final Term sum4 = SmtUtils.sum(mScript, SmtSortUtils.getIntSort(mScript),z, mod3);
        // substr1 = z + (b mod k) - k
        final Term substr1 = SmtUtils.minus(mScript, sum4, divisorAsTerm);
        // larger1 = z + (b mod k) >= k
        final Term larger1 = SmtUtils.geq(mScript, sum4, divisorAsTerm);
        termWithITE = SmtUtils.ite(mScript, larger1, substr1, sum4);
        final BigInteger zeroAsBigInteger = BigInteger.valueOf(0);
        final Term zeroAsTerm = SmtUtils.constructIntegerValue(mScript, SmtSortUtils.getIntSort(mScript), zeroAsBigInteger);
        // larger2 = z >= 0
        final Term larger2 = SmtUtils.geq(mScript, z, zeroAsTerm);
        // larger3 = z  < k
        final Term larger3 = SmtUtils.less(mScript, z, divisorAsTerm);
        final Map<Term, Term> sub3 = new HashMap<Term, Term>();
        sub3.put(mod1, termWithITE);
        Term termAfterFirstSubstitution = mScript.term("true");
        for (final Term conjunct : conjuncts) {
	        if (conjunct == modConjunct) {
               final Term modConjunctSub = Substitution.apply(mMgdScript, sub3, conjunct);
               termAfterFirstSubstitution = SmtUtils.and(mScript, termAfterFirstSubstitution, modConjunctSub);
	        }
	        else {
	           termAfterFirstSubstitution = SmtUtils.and(mScript, termAfterFirstSubstitution, conjunct);
	        }
        }
        termAfterFirstSubstitution = SmtUtils.and(mScript, termAfterFirstSubstitution, larger2);
        termAfterFirstSubstitution = SmtUtils.and(mScript, termAfterFirstSubstitution, larger3);
        final Term termWithRemovedITE = new IteRemover(mMgdScript).transform(termAfterFirstSubstitution);
        final Term resultTerm = Substitution.apply(mMgdScript, sub1, termWithRemovedITE);
        final NnfTransformer TermNnf = new NnfTransformer(mMgdScript, mServices, QuantifierHandling.KEEP);
        final Term ResultTermNnf = TermNnf.transform(resultTerm);
		final Set<TermVariable> remainingEliminatees = new HashSet<>(inputEt.getEliminatees());
		remainingEliminatees.remove(xEliminate);
		final EliminationTask eliminationTask = new EliminationTask(inputEt.getQuantifier(), remainingEliminatees,
				ResultTermNnf, inputEt.getContext());
		final Set<TermVariable> newEliminatees = new HashSet<>();
		newEliminatees.add(y);
		newEliminatees.add(z);
		final EliminationResult resultWithoutXInMod = new EliminationResult(eliminationTask, newEliminatees);
        return resultWithoutXInMod;
	}


	private boolean isModTerm(final Term term) {
		if (term instanceof ApplicationTerm) {
			if (((ApplicationTerm) term).getFunction().getApplicationString().equals("mod")) {
				return true;
			}
		}
		return false;
	}






}