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
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class RealToIntTransformer extends NonRecursive {

	Term mCurrentTerm;
	private final Script mScript;

	public RealToIntTransformer(Script script) {
		mScript = script;
	}

	private class RealToIntWalker implements NonRecursive.Walker {

		Term mTerm;

		RealToIntWalker(Term term) {
			mTerm = term;
		}

		@Override
		public void walk(NonRecursive engine) {
			((RealToIntTransformer) engine).realToIntWalk(mTerm);
		}

	}

	public Term transformToIntConstants(Term term) {
		run(new RealToIntWalker(term));
		return mCurrentTerm;
	}

	private void realToIntWalk(Term term) {
		if (term instanceof ConstantTerm) {
			final Object value = ((ConstantTerm) term).getValue();
			if (value instanceof BigDecimal) {
				mCurrentTerm = mScript.numeral(((BigDecimal) value).toBigInteger());
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

	public Term transformToInt(Term term) {
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
				mCurrentTerm = mScript.numeral(intValue);
			} else if (value instanceof BigDecimal) {
				mCurrentTerm = mScript.numeral(((BigDecimal) value).toBigIntegerExact());
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

}
