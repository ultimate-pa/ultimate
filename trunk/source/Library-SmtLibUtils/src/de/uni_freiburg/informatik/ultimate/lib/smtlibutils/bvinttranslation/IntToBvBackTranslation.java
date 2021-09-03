package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.bvinttranslation;

import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.BitvectorUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class IntToBvBackTranslation extends TermTransformer {
	private final ManagedScript mMgdScript;
	private final Script mScript;
	private final LinkedHashMap<Term, Term> mVariableMap; // Maps Int Var to Bv Var
	private final Set<Term> mConstraintSet; // Set of all constraints

	public IntToBvBackTranslation(final ManagedScript mgdscript, final LinkedHashMap<Term, Term> variableMap,
			final Set<Term> constraintSet) {
		mMgdScript = mgdscript;
		mScript = mgdscript.getScript();
		mVariableMap = variableMap;
		mConstraintSet = constraintSet;
	}

	@Override
	public void convert(final Term term) {
		if (mConstraintSet.contains(term)) {
			setResult(mScript.term("true"));
			return;
		}
		if (mVariableMap.containsKey(term)) {
			setResult(mVariableMap.get(term));
			return;
		} else if (term instanceof TermVariable) {
			throw new UnsupportedOperationException("Cannot translate AuxVars back to Bitvector Sort " + term);
		} else if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			if (appTerm.getParameters().length == 0) {
				if (SmtUtils.isConstant(appTerm)) {
					throw new UnsupportedOperationException("Cannot translate AuxVars back to Bitvector Sort " + term);
				}
			}
		}
		super.convert(term);
	}

	@Override
	public void postConvertQuantifier(final QuantifiedFormula old, final Term newBody) {
		// TODO
		super.postConvertQuantifier(old, newBody);
	}

	@Override
	public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] args) {
		final Term[] newargs = args;
		int width = 0;
		// Constraints are always true in BV Theory
		if (mConstraintSet.contains(appTerm)) {
			setResult(mScript.term("true"));
			return;
		}

		for (final Term argument : args) {
			if (!(argument instanceof ConstantTerm) && SmtSortUtils.isBitvecSort(argument.getSort())) {
				final int newwidth = Integer.valueOf(argument.getSort().getIndices()[0]);
				assert (width == 0) || (width == newwidth); // TODO extract concat etc
				width = newwidth;
			}
		}
		for (int i = 0; i < args.length; i++) {
			if (args[i] instanceof ConstantTerm) {
				newargs[i] = translateConst((ConstantTerm) args[i], width);
			}
		}

		final FunctionSymbol fsym = appTerm.getFunction();
		if (fsym.isIntern()) {
			switch (fsym.getName()) {
			case "=": {
				setResult(SmtUtils.equality(mScript, newargs[0], newargs[1]));
				return;
			}
			case "<": {
				setResult(BitvectorUtils.termWithLocalSimplification(mScript, "bvult", null, newargs[0], newargs[1]));
				return;
			}
			case "<=": {
				setResult(BitvectorUtils.termWithLocalSimplification(mScript, "bvule", null, newargs[0], newargs[1]));
				return;
			}
			case ">=": {
				setResult(BitvectorUtils.termWithLocalSimplification(mScript, "bvuge", null, newargs[0], newargs[1]));
				return;
			}
			case ">": {
				setResult(BitvectorUtils.termWithLocalSimplification(mScript, "bvugt", null, newargs[0], newargs[1]));
				return;
			}
			case "+": {
				setResult(BitvectorUtils.termWithLocalSimplification(mScript, "bvadd", null, newargs[0], newargs[1]));
				return;
			}
			case "*": {
				// x * pow of 2 left shift
				setResult(mScript.term("bvmul", newargs[0], newargs[1]));
				return;
			}
			case "-": {
				if (appTerm.getParameters().length == 1) {
					assert !(newargs[0] instanceof ConstantTerm);
					setResult(mScript.term("bvneg", newargs[0]));
					return;
				} else if (appTerm.getParameters().length == 2) {
					setResult(mScript.term("bvsub", newargs[0], newargs[1]));
					return;
				}

			}
			case "mod": {
				if (isMaxNumberPlusOne(appTerm.getParameters()[1], width)) { // mod maxNumber
					setResult(newargs[0]);
					return;
				}
				// if (isMaxNumberPlusOneHalf(appTerm.getParameters()[1], width)) { // mod (maxNumber / 2)
				// setResult(newargs[0]);
				// return;
				// }
				//no difference in test success between bvsmod and bvurem
				setResult(BitvectorUtils.termWithLocalSimplification(mScript, "bvsmod", null, newargs[0], newargs[1]));
				return;

			}
			case "div": {
				// x div pow of 2, rightshift
				assert width != 0;
				if (isMaxNumberPlusOne(appTerm.getParameters()[1], width)) {
					setResult(SmtUtils.rational2Term(mScript, Rational.ONE,
							SmtSortUtils.getBitvectorSort(mScript, width)));
					return;
				}

				if (isMaxNumberPlusOne(appTerm.getParameters()[1], width)) {
					setResult(SmtUtils.rational2Term(mScript, Rational.ONE,
							SmtSortUtils.getBitvectorSort(mScript, width)));
					return;
				}
				setResult(mScript.term("bvsdiv", newargs[0], newargs[1]));
				return;
			}
			case "abs": {
				throw new UnsupportedOperationException("Unexpected function in back-translation " + fsym.getName());
			}
			default:
				final Term[] translatedSubterms = new Term[appTerm.getParameters().length];
				for (int i = 0; i < appTerm.getParameters().length; i++) {
					translatedSubterms[i] = newargs[i];
				}
				setResult(SmtUtils.termWithLocalSimplification(mScript, fsym, translatedSubterms));
				return;

			}
		}

		super.convertApplicationTerm(appTerm, newargs);
	}

	private boolean isZero(final Term term) {
		if (term instanceof ConstantTerm) {
			final ConstantTerm cnst = (ConstantTerm) term;
			if (cnst.getValue().equals(Rational.ZERO)) {
				return true;
			}
		}
		return false;
	}

	private boolean isMaxNumberPlusOne(final Term term, final int width) {
		assert SmtSortUtils.isIntSort(term.getSort());
		if (term instanceof ConstantTerm) {
			final ConstantTerm ct = (ConstantTerm) term;
			final Rational rational = (Rational) ct.getValue();
			if (rational.equals(Rational.valueOf(BigInteger.TWO.pow(width), BigInteger.ONE))) {
				return true;
			}
			// negated maxnumber
			if (rational.isNegative()) {
				if (rational.negate().equals(Rational.valueOf(BigInteger.TWO.pow(width), BigInteger.ONE))) {
					return true;
				}
			}

		}
		return false;
	}

	private boolean isMaxNumberPlusOneHalf(final Term term, final int width) {
		assert SmtSortUtils.isIntSort(term.getSort());
		if (term instanceof ConstantTerm) {
			final ConstantTerm ct = (ConstantTerm) term;
			final Rational rational = (Rational) ct.getValue();
			if (rational.equals(Rational.valueOf(BigInteger.TWO.pow(width).divide(BigInteger.TWO), BigInteger.ONE))) {
				return true;
			}
			// negated maxnumber
			if (rational.isNegative()) {
				if (rational.negate()
						.equals(Rational.valueOf(BigInteger.TWO.pow(width).divide(BigInteger.TWO), BigInteger.ONE))) {
					return true;
				}
			}

		}
		return false;
	}

	private Term translateConst(final ConstantTerm value, final int width) {
		assert value.getValue() instanceof Rational;
		if (((Rational) value.getValue()).isNegative()) {
			return mScript.term("bvneg", SmtUtils.rational2Term(mScript, (Rational) value.getValue(),
					SmtSortUtils.getBitvectorSort(mScript, width)));
		} else {
			return SmtUtils.rational2Term(mScript, (Rational) value.getValue(),
					SmtSortUtils.getBitvectorSort(mScript, width));
		}
	}
}
