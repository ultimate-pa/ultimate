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

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ApplicationTermFinder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SubstitutionWithLocalSimplification;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * 
 * @author Matthias Heizmann
 */
public class ModuloNeighborTransformation extends TransitionPreprocessor {
	public static final String DESCRIPTION = "Replace modulo operation by disjunction if divisor is a literal";

	/**
	 * Use assert statement to check if result is equivalent to the conjunction
	 * of input term and definition of auxiliary variables.
	 */
	private static final boolean CHECK_RESULT = !true;

	private final boolean mUseNeibors;

	/**
	 * Constructor
	 */
	public ModuloNeighborTransformation(final boolean useNeibors) {
		super();
		mUseNeibors = useNeibors;
	}

	@Override
	public String getDescription() {
		return DESCRIPTION;
	}

	@Override
	public ModifiableTransFormula process(final ManagedScript mgdScript, final ModifiableTransFormula tf) throws TermException {
		final Term newFormula = constructTerm(mgdScript, tf.getFormula());
		tf.setFormula(newFormula);
		return tf;
	}

	@Override
	public boolean checkSoundness(final Script script, final ModifiableTransFormula oldTF,
			final ModifiableTransFormula newTF) {
		return !(CHECK_RESULT && isIncorrect(script, oldTF.getFormula(), newTF.getFormula()));
	}

	/**
	 * Return true if we were able to prove that the result is incorrect. For
	 * this check we add to the input term the definition of the auxiliary
	 * variables.
	 */
	private boolean isIncorrect(final Script script, final Term input, final Term result) {
		return LBool.SAT == Util.checkSat(script, script.term("distinct", input, result));
	}


	private Term constructInRangeBounds(final Script script, final Term dividend, final Term divisor) {
		final Term geqZero = script.term("<=", script.numeral(BigInteger.ZERO), dividend);
		final Term ltDivisor = script.term("<", dividend, divisor);
		return script.term("and", geqZero, ltDivisor);
	}
	
	private Term constructInRangeResult(final Term dividend) {
		return dividend;
	}
	
	private Term constructLeftIntervalBounds(final Script script, final Term dividend, final Term divisor) {
		final Term geqLeftBound = script.term("<=", script.term("-", divisor), dividend);
		final Term ltZero = script.term("<", dividend, script.numeral(BigInteger.ZERO));
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
		return script.term("and", lgtleftBoundofLeftInterval, gtRightBoundofRightInterval);
	}
	
	
	
	private Term constructTerm(final ManagedScript mgdScript, Term term) {
		while (true) {
			final Set<ApplicationTerm> modTerms = new ApplicationTermFinder(Collections.singleton("mod"), false).findMatchingSubterms(term);
			if (modTerms.isEmpty()) {
				break;
			}
			ApplicationTerm some = null;
			Term dividend = null;
			Term divisor = null;
			for (final ApplicationTerm modTerm : modTerms) {
				assert modTerm.getParameters().length == 2;
				dividend = modTerm.getParameters()[0];
				divisor = modTerm.getParameters()[1];
				if (divisor instanceof ConstantTerm) {
					some = modTerm;
					break;
				} else {
					dividend = null;
					divisor = null;
				}
			}
			if (some == null) {
				// no mod term with constant divisor left
				break;
			} else {
				final Script script = mgdScript.getScript();
				final List<Term> cases = new ArrayList<>();
				{
					final Map<Term, Term> substitutionMapping = Collections.singletonMap(some, constructInRangeResult(dividend));
					final Term case1 = Util.and(script, constructInRangeBounds(script, dividend, divisor),
							new SubstitutionWithLocalSimplification(mgdScript, substitutionMapping).transform(term));
					cases.add(case1);
				}
				{
					final Map<Term, Term> substitutionMapping = Collections.singletonMap(some, constructLeftIntervalResult(script, dividend, divisor));
					final Term case2 = Util.and(script, constructLeftIntervalBounds(script, dividend, divisor),
							new SubstitutionWithLocalSimplification(mgdScript, substitutionMapping).transform(term));
					cases.add(case2);
				}
				{
					final Map<Term, Term> substitutionMapping = Collections.singletonMap(some, constructRightIntervalResult(script, dividend, divisor));
					final Term case3 = Util.and(script, constructRightIntervalBounds(script, dividend, divisor),
							new SubstitutionWithLocalSimplification(mgdScript, substitutionMapping).transform(term));
					cases.add(case3);
				}
				{
					final Term case4 = constructNoNeighborIntervalBounds(script, dividend, divisor);
//							Util.and(script, constructNoNeighborIntervalBounds(script, dividend, divisor),
//							some);
					cases.add(case4);
				}
				term = SmtUtils.or(script, cases);
			}
			
		}
		return term;
	
	}


}
