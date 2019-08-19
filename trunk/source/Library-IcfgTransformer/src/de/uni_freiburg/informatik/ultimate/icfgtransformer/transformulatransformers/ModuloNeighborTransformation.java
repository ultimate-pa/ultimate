/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE IcfgTransformer library.
 * 
 * The ULTIMATE IcfgTransformer library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE IcfgTransformer library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.ApplicationTermFinder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.DagSizePrinter;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SubstitutionWithLocalSimplification;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;

/**
 * Replace e.g., (x % 256) == y by the following disjunction (0 <= x && x < 256) && x == y || (-256 <= x && x < 0) && (x
 * + 256) == y || (256 <= x && x < 256 + 256) && (x - 256) == y || (x < -256 || 256 + 256 <= x) && (x % 256) == y
 * 
 * @author Matthias Heizmann
 */
public class ModuloNeighborTransformation extends TransitionPreprocessor {
	public static final String DESCRIPTION = "Replace modulo operation by disjunction if divisor is a literal";

	/**
	 * Use assert statement to check if result is equivalent to the conjunction of input term and definition of
	 * auxiliary variables.
	 */
	private static final boolean CHECK_RESULT = true;

	private static final String MODULO_REPLACEMENT = "mod2";

	private final IUltimateServiceProvider mServices;

	private final boolean mUseNeibors;
	private static final boolean APPLY_ONLY_TO_TYPICAL_WRAPAROUD_CONSTANTS = true;
	private static final BigInteger BITLENGTH8_VALUE = BigInteger.valueOf(256);
	private static final BigInteger BITLENGTH16_VALUE = BigInteger.valueOf(65536);
	private static final BigInteger BITLENGTH32_VALUE = BigInteger.valueOf(4294967296L);
	private static final BigInteger BITLENGTH64_VALUE = new BigInteger("9223372036854775808");
	private static final BigInteger BITLENGTH128_VALUE = new BigInteger("340282366920938463463374607431768211456");

	public ModuloNeighborTransformation(final IUltimateServiceProvider services, final boolean useNeibors) {
		super();
		mServices = services;
		if (!useNeibors) {
			throw new UnsupportedOperationException("not yet implemented");
		}
		mUseNeibors = useNeibors;
	}

	@Override
	public String getDescription() {
		return DESCRIPTION;
	}

	@Override
	public ModifiableTransFormula process(final ManagedScript mgdScript, final ModifiableTransFormula tf)
			throws TermException {
		final Term newFormula = constructTerm(mgdScript, tf.getFormula());
		final ModifiableTransFormula result = new ModifiableTransFormula(tf);
		result.setFormula(newFormula);
		return result;
	}

	@Override
	public boolean checkSoundness(final Script script, final ModifiableTransFormula oldTF,
			final ModifiableTransFormula newTF) {
		return !(CHECK_RESULT && isIncorrect(script, oldTF.getFormula(), newTF.getFormula()));
	}

	/**
	 * Return true if we were able to prove that the result is incorrect. For this check we add to the input term the
	 * definition of the auxiliary variables.
	 */
	private boolean isIncorrect(final Script script, final Term input, final Term result) {
		return LBool.SAT == Util.checkSat(script, script.term("distinct", input, result));
	}

	private Term constructInRangeBounds(final Script script, final Term dividend, final Term divisor) {
		final Term geqZero = script.term("<=", SmtUtils.constructIntValue(script, BigInteger.ZERO), dividend);
		final Term ltDivisor = script.term("<", dividend, divisor);
		return script.term("and", geqZero, ltDivisor);
	}

	private Term constructInRangeResult(final Term dividend) {
		return dividend;
	}

	private Term constructLeftIntervalBounds(final Script script, final Term dividend, final Term divisor) {
		final Term geqLeftBound = script.term("<=", script.term("-", divisor), dividend);
		final Term ltZero = script.term("<", dividend, SmtUtils.constructIntValue(script, BigInteger.ZERO));
		return script.term("and", geqLeftBound, ltZero);
	}

	private Term constructLeftIntervalResult(final Script script, final Term dividend, final Term divisor) {
		return script.term("+", dividend, divisor);
	}

	private Term constructRightIntervalBounds(final Script script, final Term dividend, final Term divisor) {
		final Term geqLeftBound = script.term("<=", divisor, dividend);
		final Term lgtRightBound = script.term("<", dividend, script.term("+", divisor, divisor));
		return script.term("and", geqLeftBound, lgtRightBound);
	}

	private Term constructRightIntervalResult(final Script script, final Term dividend, final Term divisor) {
		return script.term("-", dividend, divisor);
	}

	private Term constructNoNeighborIntervalBounds(final Script script, final Term dividend, final Term divisor) {
		final Term lgtleftBoundofLeftInterval = script.term("<", dividend, script.term("-", divisor));
		final Term gtRightBoundofRightInterval = script.term("<=", script.term("+", divisor, divisor), dividend);
		return script.term("or", lgtleftBoundofLeftInterval, gtRightBoundofRightInterval);
	}

	private Term constructNoNeighborIntervalResult(final Script script, final Term dividend, final Term divisor) {
		return script.term(MODULO_REPLACEMENT, dividend, divisor);
	}

	private Term constructTerm(final ManagedScript mgdScript, Term term) {
		mgdScript.lock(this);
		mgdScript.push(this, 1);
		final Sort intSort = SmtSortUtils.getIntSort(mgdScript);
		/*
		 * Problem: nested mod terms the result contains also mod terms we cannot distinguish terms were already
		 * processed from those that were not simplification converts result back into input Solution: process one after
		 * the other replace mod in case 4 by new aux function symbol by mod2, simplify, replace mod2 by mod later
		 */
		mgdScript.declareFun(this, MODULO_REPLACEMENT, new Sort[] { intSort, intSort }, intSort);
		while (true) {
			final Set<ApplicationTerm> modTerms =
					new ApplicationTermFinder(Collections.singleton("mod"), false).findMatchingSubterms(term);
			if (modTerms.isEmpty()) {
				break;
			}
			if (!mServices.getProgressMonitorService().continueProcessing()) {
				throw new ToolchainCanceledException(this.getClass(), "removing " + modTerms.size()
						+ " modulo operations from term of size " + new DagSizePrinter(term).toString());
			}
			ApplicationTerm someModuloTermWithConstantDivisor = null;
			Term dividend = null;
			Term divisor = null;
			for (final ApplicationTerm modTerm : modTerms) {
				assert modTerm.getParameters().length == 2;
				dividend = modTerm.getParameters()[0];
				divisor = modTerm.getParameters()[1];
				if (divisor instanceof ConstantTerm && (!APPLY_ONLY_TO_TYPICAL_WRAPAROUD_CONSTANTS
						|| isWraparoundConstant((ConstantTerm) divisor))) {
					someModuloTermWithConstantDivisor = modTerm;
					break;
				}
				dividend = null;
				divisor = null;
			}
			if (someModuloTermWithConstantDivisor == null) {
				// no mod term with constant divisor left
				break;
			}
			final Script script = mgdScript.getScript();
			final List<Term> cases = new ArrayList<>();
			{
				final Map<Term, Term> substitutionMapping =
						Collections.singletonMap(someModuloTermWithConstantDivisor, constructInRangeResult(dividend));
				final Term case1 = SmtUtils.and(script, constructInRangeBounds(script, dividend, divisor),
						new SubstitutionWithLocalSimplification(mgdScript, substitutionMapping).transform(term));
				cases.add(case1);
			}
			{
				final Map<Term, Term> substitutionMapping = Collections.singletonMap(someModuloTermWithConstantDivisor,
						constructLeftIntervalResult(script, dividend, divisor));
				final Term case2 = SmtUtils.and(script, constructLeftIntervalBounds(script, dividend, divisor),
						new SubstitutionWithLocalSimplification(mgdScript, substitutionMapping).transform(term));
				cases.add(case2);
			}
			{
				final Map<Term, Term> substitutionMapping = Collections.singletonMap(someModuloTermWithConstantDivisor,
						constructRightIntervalResult(script, dividend, divisor));
				final Term case3 = SmtUtils.and(script, constructRightIntervalBounds(script, dividend, divisor),
						new SubstitutionWithLocalSimplification(mgdScript, substitutionMapping).transform(term));
				cases.add(case3);
			}
			{
				final Map<Term, Term> substitutionMapping = Collections.singletonMap(someModuloTermWithConstantDivisor,
						constructNoNeighborIntervalResult(script, dividend, divisor));
				final Term case4 = SmtUtils.and(script, constructNoNeighborIntervalBounds(script, dividend, divisor),
						new SubstitutionWithLocalSimplification(mgdScript, substitutionMapping).transform(term));
				cases.add(case4);
			}
			term = SmtUtils.or(script, cases);

		}
		term = SmtUtils.simplify(mgdScript, term, mServices, SimplificationTechnique.SIMPLIFY_DDA);

		while (true) {
			final Set<ApplicationTerm> auxModTerms =
					new ApplicationTermFinder(Collections.singleton(MODULO_REPLACEMENT), false)
							.findMatchingSubterms(term);
			if (auxModTerms.isEmpty()) {
				break;
			}
			final ApplicationTerm auxModTerm = auxModTerms.iterator().next();
			assert auxModTerm.getFunction().getName().equals(MODULO_REPLACEMENT) : "wrong function";
			assert auxModTerm.getParameters().length == 2;
			final Term dividend = auxModTerm.getParameters()[0];
			final Term divisor = auxModTerm.getParameters()[1];
			final Term modTerm = mgdScript.getScript().term("mod", dividend, divisor);
			final Map<Term, Term> substitutionMapping = Collections.singletonMap(auxModTerm, modTerm);
			term = new SubstitutionWithLocalSimplification(mgdScript, substitutionMapping).transform(term);
		}
		mgdScript.pop(this, 1);
		mgdScript.unlock(this);
		return term;

	}

	private boolean isWraparoundConstant(final ConstantTerm constant) {
		final Object value = constant.getValue();
		if (value instanceof Rational) {
			return isWraparoudBigInteger(((Rational) value).numerator());
		} else if (value instanceof BigInteger) {
			return isWraparoudBigInteger((BigInteger) value);
		} else {
			throw new UnsupportedOperationException("value has type " + value.getClass().getSimpleName());
		}
	}

	private boolean isWraparoudBigInteger(final BigInteger bigInt) {
		return bigInt.equals(BITLENGTH8_VALUE) || bigInt.equals(BITLENGTH16_VALUE) || bigInt.equals(BITLENGTH32_VALUE)
				|| bigInt.equals(BITLENGTH64_VALUE) || bigInt.equals(BITLENGTH128_VALUE);
	}

}
