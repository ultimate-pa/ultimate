/*
 * Copyright (C) 2017 Jill Enke (enkei@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr;

import java.math.BigDecimal;
import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;

public class FastUPRTermTransformer extends NonRecursive {

	private Term mCurrentTerm;
	private final Script mScript;

	/**
	 *
	 * @param script
	 *            The {@link Script} to use for {@link Term} transformation.
	 */
	public FastUPRTermTransformer(final Script script) {
		mScript = script;
	}

	private class RealToIntWalker implements NonRecursive.Walker {

		private final Term mTerm;

		RealToIntWalker(final Term term) {
			mTerm = term;
		}

		@Override
		public void walk(final NonRecursive engine) {
			((FastUPRTermTransformer) engine).realToIntWalk(mTerm);
		}

	}

	@Deprecated
	public Term transformToIntConstants(final Term term) {
		run(new RealToIntWalker(term));
		return mCurrentTerm;
	}

	@Deprecated
	private void realToIntWalk(final Term term) {
		if (term instanceof ConstantTerm) {
			final Object value = ((ConstantTerm) term).getValue();
			if (value instanceof BigDecimal) {
				mCurrentTerm = SmtUtils.constructIntValue(mScript, ((BigDecimal) value).toBigInteger());
			} else if (value instanceof BigInteger) {
				mCurrentTerm = term;
			} else {
				throw new AssertionError("Unknown value" + value.getClass().toString());
			}
		} else if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			final Term[] subTerms = new Term[appTerm.getParameters().length];
			for (int i = 0; i < appTerm.getParameters().length; i++) {
				enqueueWalker(new RealToIntWalker(appTerm.getParameters()[i]));
				subTerms[i] = mCurrentTerm;
			}
			mCurrentTerm = mScript.term(appTerm.getFunction().getName(), subTerms);
		} else if (term instanceof LetTerm) {
			final LetTerm letTerm = (LetTerm) term;
			final Term[] subTerms = new Term[letTerm.getValues().length];
			for (int i = 0; i < letTerm.getValues().length; i++) {
				enqueueWalker(new RealToIntWalker(letTerm.getValues()[i]));
				subTerms[i] = mCurrentTerm;
			}
			enqueueWalker(new RealToIntWalker(letTerm.getSubTerm()));
			final Term body = mCurrentTerm;
			mCurrentTerm = mScript.let(letTerm.getVariables(), subTerms, body);

		} else if (term instanceof QuantifiedFormula) {
			final QuantifiedFormula formula = (QuantifiedFormula) term;
			enqueueWalker(new RealToIntWalker(formula.getSubformula()));
			final Term body = mCurrentTerm;
			mCurrentTerm = mScript.quantifier(formula.getQuantifier(), formula.getVariables(), body);

		} else if (term instanceof AnnotatedTerm) {
			final AnnotatedTerm annTerm = (AnnotatedTerm) term;
			enqueueWalker(new RealToIntWalker(annTerm.getSubterm()));
			final Term body = mCurrentTerm;
			mCurrentTerm = mScript.annotate(body, annTerm.getAnnotations());

		} else if (term instanceof TermVariable) {
			mCurrentTerm = term;
		}

	}

	/**
	 * Tries to transform all ConstantTerms to ConstantTerms with
	 * {@link Sort.INT_SORT}.
	 *
	 * @param term
	 *            The term to be transformed.
	 * @return The transformed term.
	 */
	public Term transformToInt(final Term term) {
		if (term instanceof ConstantTerm) {
			final Object value = ((ConstantTerm) term).getValue();
			if (value instanceof Rational) {
				final Rational rational = (Rational) value;
				final BigInteger[] divideAndRemainder = rational.numerator().divideAndRemainder(rational.denominator());
				final BigInteger intValue;
				if (divideAndRemainder[1].equals(BigInteger.ZERO)) {
					intValue = divideAndRemainder[0];
				} else {
					throw new AssertionError("Can't Handle Reals.");
				}
				mCurrentTerm = SmtUtils.constructIntValue(mScript, intValue);
			} else if (value instanceof BigDecimal) {
				mCurrentTerm = SmtUtils.constructIntValue(mScript, ((BigDecimal) value).toBigIntegerExact());
			} else if (value instanceof BigInteger) {
				mCurrentTerm = term;
			} else {
				throw new AssertionError("Unknown value" + value.getClass().toString());
			}
		} else if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			final Term[] subTerms = new Term[appTerm.getParameters().length];
			for (int i = 0; i < appTerm.getParameters().length; i++) {
				subTerms[i] = transformToInt(appTerm.getParameters()[i]);
			}
			mCurrentTerm = mScript.term(appTerm.getFunction().getName(), subTerms);
		} else if (term instanceof LetTerm) {
			final LetTerm letTerm = (LetTerm) term;
			final Term[] subTerms = new Term[letTerm.getValues().length];
			for (int i = 0; i < letTerm.getValues().length; i++) {
				subTerms[i] = transformToInt(letTerm.getValues()[i]);
			}
			final Term body = transformToInt(letTerm.getSubTerm());
			mCurrentTerm = mScript.let(letTerm.getVariables(), subTerms, body);

		} else if (term instanceof QuantifiedFormula) {
			final QuantifiedFormula formula = (QuantifiedFormula) term;
			final Term body = transformToInt(formula.getSubformula());
			mCurrentTerm = mScript.quantifier(formula.getQuantifier(), formula.getVariables(), body);

		} else if (term instanceof AnnotatedTerm) {
			final AnnotatedTerm annTerm = (AnnotatedTerm) term;
			final Term body = transformToInt(annTerm.getSubterm());
			mCurrentTerm = mScript.annotate(body, annTerm.getAnnotations());

		} else if (term instanceof TermVariable) {
			mCurrentTerm = term;
		}
		return mCurrentTerm;
	}

	/**
	 * Replaces all occurences of a {@link TermVariable} in the term with
	 * another one.
	 * 
	 * @param term
	 *            The term to be transformed.
	 * @param toReplace
	 *            The variable to replace.
	 * @param replaceWith
	 *            The replacement variable.
	 * @return The transformed term.
	 */
	public Term replaceVar(final Term term, final TermVariable toReplace, final TermVariable replaceWith) {
		if (term instanceof ConstantTerm) {
			mCurrentTerm = term;
		} else if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			final Term[] subTerms = new Term[appTerm.getParameters().length];
			for (int i = 0; i < appTerm.getParameters().length; i++) {
				subTerms[i] = replaceVar(appTerm.getParameters()[i], toReplace, replaceWith);
			}
			mCurrentTerm = mScript.term(appTerm.getFunction().getName(), subTerms);
		} else if (term instanceof LetTerm) {
			final LetTerm letTerm = (LetTerm) term;
			final Term[] subTerms = new Term[letTerm.getValues().length];
			for (int i = 0; i < letTerm.getValues().length; i++) {
				subTerms[i] = replaceVar(letTerm.getValues()[i], toReplace, replaceWith);
			}
			final Term body = transformToInt(letTerm.getSubTerm());
			mCurrentTerm = mScript.let(letTerm.getVariables(), subTerms, body);

		} else if (term instanceof QuantifiedFormula) {
			final QuantifiedFormula formula = (QuantifiedFormula) term;
			final Term body = replaceVar(formula.getSubformula(), toReplace, replaceWith);
			mCurrentTerm = mScript.quantifier(formula.getQuantifier(), formula.getVariables(), body);

		} else if (term instanceof AnnotatedTerm) {
			final AnnotatedTerm annTerm = (AnnotatedTerm) term;
			final Term body = replaceVar(annTerm.getSubterm(), toReplace, replaceWith);
			mCurrentTerm = mScript.annotate(body, annTerm.getAnnotations());

		} else if (term instanceof TermVariable) {
			if (term.equals(toReplace)) {
				mCurrentTerm = replaceWith;
			} else {
				mCurrentTerm = term;
			}
		}
		return mCurrentTerm;
	}

	/**
	 * Converts any Term that is a {@link QuantifiedFormula} into an one with
	 * existential Quantifier.
	 *
	 * @param term
	 *            The term to be transformed.
	 * @return The transformed Term.
	 */
	public Term toExistential(final Term term) {
		if (!(term instanceof QuantifiedFormula)) {
			return term;
		}
		final QuantifiedFormula quantTerm = (QuantifiedFormula) term;
		if (quantTerm.getQuantifier() == QuantifiedFormula.EXISTS) {
			return term;
		}
		final Term notTerm = mScript.term("not", quantTerm.getSubformula());
		final Term existentialTerm = mScript.quantifier(QuantifiedFormula.EXISTS, quantTerm.getVariables(), notTerm);
		return mScript.term("not", existentialTerm);
	}

}
