package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.bvinttranslation;

import java.math.BigInteger;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.UnfTransformer;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class TranslationConstrainer {
	private final ManagedScript mMgdScript;
	private final Script mScript;
	private FunctionSymbol mIntand;

	enum Mode {
		SUM, BITWISE, LAZYSUM, LAZYBITWISE
	}

	private Mode mSetMode = Mode.SUM; // Default Mode

	private final HashSet<Term> mConstraintSet; // Set of all constraints
	private final HashSet<Term> mTvConstraintSet; // Set of all constraints for quantified variables

	public TranslationConstrainer(final ManagedScript mgdscript) {
		mMgdScript = mgdscript;
		mScript = mgdscript.getScript();

		mConstraintSet = new HashSet<Term>();
		mTvConstraintSet = new HashSet<Term>();
		// mTranslatedTerms = new HashMap<>();
		// mReversedTranslationMap = new HashMap<>();

		final Sort intSort = SmtSortUtils.getIntSort(mScript);
		final Sort[] functionsort = new Sort[2];
		functionsort[0] = intSort;
		functionsort[1] = intSort;

		if (mIntand == null) {
			if (mScript.getFunctionSymbol("intand") == null) {
				mScript.declareFun("intand", functionsort, intSort);
			}
			mIntand = mScript.getFunctionSymbol("intand");
		}
	}

	public HashSet<Term> getConstraints() {
		return mConstraintSet;
	}

	public HashSet<Term> getTvConstraints() {
		return mTvConstraintSet;
	}

	public void setBvandMode(final Mode mode) {
		mSetMode = mode;
	}

	public FunctionSymbol getIntAndFunctionSymbol() {
		return mIntand;
	}

	public void varConstraint(final Term bvterm, final Term intTerm) {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);
		final int width = Integer.valueOf(bvterm.getSort().getIndices()[0]);

		final Term translatedVar = intTerm;
		final Rational twoPowWidth = Rational.valueOf(BigInteger.valueOf(2).pow(width), BigInteger.ONE);
		final Rational twoPowWidthSubOne = twoPowWidth.sub(Rational.ONE);

		final Term lowerBound = mScript.term("<=", Rational.ZERO.toTerm(intSort), translatedVar);
		final Term upperBoundPaper =
				mScript.term("<", translatedVar, SmtUtils.rational2Term(mScript, twoPowWidth, intSort));
		final Term upperBound =
				mScript.term("<=", translatedVar, SmtUtils.rational2Term(mScript, twoPowWidthSubOne, intSort));
		mConstraintSet.add(lowerBound);
		mConstraintSet.add(upperBoundPaper);
	}

	public Term getTvConstraint(final TermVariable bvterm, final Term intTerm) {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);
		final int width = Integer.valueOf(bvterm.getSort().getIndices()[0]);
		final Rational twoPowWidth = Rational.valueOf(BigInteger.valueOf(2).pow(width), BigInteger.ONE);
		final Rational twoPowWidthSubOne = twoPowWidth.sub(Rational.ONE);

		final Term lowerBound = mScript.term("<=", Rational.ZERO.toTerm(intSort), intTerm);
		final Term upperBoundPaper = mScript.term("<", intTerm, SmtUtils.rational2Term(mScript, twoPowWidth, intSort));
		final Term upperBound =
				mScript.term("<=", intTerm, SmtUtils.rational2Term(mScript, twoPowWidthSubOne, intSort));
		mTvConstraintSet.add(lowerBound);
		mTvConstraintSet.add(upperBoundPaper);
		return mScript.term("and", lowerBound, upperBoundPaper);
	}

	public void bvandConstraint(final Term intTerm, final int width) {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);
		if (!SmtSortUtils.isIntSort(intTerm.getSort())) {
			throw new UnsupportedOperationException("Cannot create Constraints vor non-Int Sort Terms");
		}
		if (intTerm instanceof ApplicationTerm) {
			final ApplicationTerm apterm = (ApplicationTerm) intTerm;
			final Term translatedLHS = apterm.getParameters()[0];
			final Term translatedRHS = apterm.getParameters()[1];

			final Rational twoPowWidth = Rational.valueOf(BigInteger.valueOf(2).pow(width), BigInteger.ONE);
			final Term lowerBound = mScript.term("<=", Rational.ZERO.toTerm(intSort), apterm);
			final Term upperBound = mScript.term("<", apterm, SmtUtils.rational2Term(mScript, twoPowWidth, intSort));
			final Term modeConstraint;
			Term lazy = mScript.term("true");
			switch (mSetMode) {
			case LAZYSUM: {
				lazy = bvandLAZYConstraints(width, translatedLHS, translatedRHS);
				modeConstraint = bvandSUMConstraints(width, translatedLHS, translatedRHS);
				break;
			}
			case SUM: {
				modeConstraint = bvandSUMConstraints(width, translatedLHS, translatedRHS);
				break;
			}
			case LAZYBITWISE: {
				lazy = bvandLAZYConstraints(width, translatedLHS, translatedRHS);
				modeConstraint = bvandBITWISEConstraints(width, translatedLHS, translatedRHS);
				break;
			}
			case BITWISE: {
				modeConstraint = bvandBITWISEConstraints(width, translatedLHS, translatedRHS);
				break;
			}
			default: {
				modeConstraint = bvandSUMConstraints(width, translatedLHS, translatedRHS);
			}
			}
			mConstraintSet.add(lowerBound);
			mConstraintSet.add(upperBound);
			mConstraintSet.add(lazy);

			// Important, to match with the backtranslation we also need to bring it in the same form here
			final UnfTransformer unfT = new UnfTransformer(mScript);
			final Term unfModeConstraint = unfT.transform(modeConstraint);
			mConstraintSet.add(unfModeConstraint);
		}
	}

	private Term bvandSUMConstraints(final int width, final Term translatedLHS, final Term translatedRHS) {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);
		final BigInteger two = BigInteger.valueOf(2);
		final Term[] sum = new Term[width];
		for (int i = 0; i < width; i++) { // width + 1?
			final Term twoPowI = SmtUtils.rational2Term(mScript, Rational.valueOf(two.pow(i), BigInteger.ONE), intSort);
			final Term one = SmtUtils.rational2Term(mScript, Rational.ONE, intSort);
			final Term zero = SmtUtils.rational2Term(mScript, Rational.ZERO, intSort);
			final Term ite = mScript.term("ite", mScript.term("=", isel(i, translatedLHS), isel(i, translatedRHS), one),
					one, zero);
			final Term mul = mScript.term("*", twoPowI, ite);
			sum[i] = mul;
		}
		return mScript.term("=", mScript.term(mIntand.getName(), translatedLHS, translatedRHS), mScript.term("+", sum));
	}

	private Term bvandBITWISEConstraints(final int width, final Term translatedLHS, final Term translatedRHS) {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);
		final Term[] and = new Term[width];
		for (int i = 0; i < width; i++) {
			final Term one = SmtUtils.rational2Term(mScript, Rational.ONE, intSort);
			final Term zero = SmtUtils.rational2Term(mScript, Rational.ZERO, intSort);
			final Term ite = mScript.term("ite", mScript.term("=", isel(i, translatedLHS), isel(i, translatedRHS), one),
					one, zero);
			final Term equals =
					mScript.term("=", isel(i, mScript.term(mIntand.getName(), translatedLHS, translatedRHS)), ite);
			and[i] = equals;
		}
		return mScript.term("and", and);
	}

	private Term bvandLAZYConstraints(final int width, final Term translatedLHS, final Term translatedRHS) {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);
		final Term zero = SmtUtils.rational2Term(mScript, Rational.ZERO, intSort);
		final Term maxNumber = SmtUtils.rational2Term(mScript,
				Rational.valueOf(BigInteger.valueOf(2).pow(width), BigInteger.ONE), intSort);
		final Term[] lazyConstraints = new Term[8];
		final Term intand = mScript.term(mIntand.getName(), translatedLHS, translatedRHS);
		// LHS upper Bound
		lazyConstraints[0] = mScript.term("<=", intand, translatedLHS);
		// RHS upper Bound
		lazyConstraints[1] = mScript.term("<=", intand, translatedRHS);
		// Idempotence
		lazyConstraints[2] = mScript.term("=>", mScript.term("=", translatedLHS, translatedRHS),
				mScript.term("=", intand, translatedLHS));
		// Symmetry
		lazyConstraints[3] = mScript.term("=", intand, mScript.term(mIntand.getName(), translatedRHS, translatedLHS));
		// LHS Zero
		lazyConstraints[4] =
				mScript.term("=>", mScript.term("=", translatedLHS, zero), mScript.term("=", intand, zero));
		// RHS Zero
		lazyConstraints[5] =
				mScript.term("=>", mScript.term("=", zero, translatedRHS), mScript.term("=", intand, zero));
		// LHS max number
		lazyConstraints[6] = mScript.term("=>", mScript.term("=", translatedLHS, maxNumber),
				mScript.term("=", intand, translatedRHS));
		// RHS max number
		lazyConstraints[7] = mScript.term("=>", mScript.term("=", maxNumber, translatedRHS),
				mScript.term("=", intand, translatedLHS));
		return mScript.term("and", lazyConstraints);
	}

	private Term isel(final int i, final Term term) {
		final Sort intSort = SmtSortUtils.getIntSort(mScript);
		final Term two =
				SmtUtils.rational2Term(mScript, Rational.valueOf(BigInteger.valueOf(2), BigInteger.ONE), intSort);
		final Term twoPowI = SmtUtils.rational2Term(mScript,
				Rational.valueOf(BigInteger.valueOf(2).pow(i), BigInteger.ONE), intSort);
		return mScript.term("mod", mScript.term("div", term, twoPowI), two);
	}
}
