package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.bitvector;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IProofTracker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofConstants;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.IPolynomialUnifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.Polynomial;

public class BvToIntUtils {

	private final Sort mInteger;
	IProofTracker mTracker;
	boolean mDealWithBvToNatAndNatToBvInPreprocessing;
	private final IPolynomialUnifier mPolyUnifier;

	public BvToIntUtils(Theory theory, final IProofTracker tracker,
			final boolean dealWithBvToNatAndNatToBvInPreprocessing, final IPolynomialUnifier polyUnifier) {
		mTracker = tracker;
		mInteger = theory.getSort(SMTLIBConstants.INT);
		mDealWithBvToNatAndNatToBvInPreprocessing = dealWithBvToNatAndNatToBvInPreprocessing;
		mPolyUnifier = polyUnifier;
	}

	/**
	 * Interpret bitvector as unsigned number, but optimize nested int_to_bv with
	 * constant parameter.
	 */
	public Term ubv2intOrConstant(final Term param) {
		final Theory theory = param.getTheory();
		if (param instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) param;
			if (appTerm.getFunction().getName() == SMTLIBConstants.INT_TO_BV
					&& appTerm.getParameters()[0] instanceof ConstantTerm) {
				final ConstantTerm constant = (ConstantTerm) appTerm.getParameters()[0];
				Rational value = (Rational) constant.getValue();
				final Rational maxNumber = pow2(Integer.parseInt(appTerm.getFunction().getIndices()[0]));
				value = value.add(maxNumber.mul(value.div(maxNumber).floor()).negate());
				return value.toTerm(constant.getSort());
			}
		}
		return theory.term(SMTLIBConstants.UBV_TO_INT, param);
	}

	/**
	 * Interpret bitvector as unsigned number.
	 */
	public Term ubv2int(final Term param, boolean mod) {
		final Theory theory = param.getTheory();
		return theory.term(SMTLIBConstants.UBV_TO_INT, param);
	}

	/**
	 * Interpret bitvector as signed number.
	 */
	public Term sbv2int(final Term param) {
		final Theory theory = param.getTheory();
		return theory.term(SMTLIBConstants.SBV_TO_INT, param);
	}

	public Term int2bv(final Term param, final String[] width) {
		final Theory theory = param.getTheory();
		assert param.getSort().isNumericSort();
		final Polynomial arg0 = new Polynomial(param);
		final Rational maxNumber = pow2(Integer.parseInt(width[0]));
		arg0.mod(maxNumber);
		final Sort sort = param.getSort();
		final Term inner = mPolyUnifier.unifyPolynomial(arg0, sort);
		if (inner instanceof ApplicationTerm
				&& ((ApplicationTerm) inner).getFunction().getName() == SMTLIBConstants.UBV_TO_INT
				&& ((ApplicationTerm) inner).getParameters()[0].getSort().getIndices()[0] == width[0]) {
			return ((ApplicationTerm) inner).getParameters()[0];
		}
		return theory.term(SMTLIBConstants.INT_TO_BV, width, null, inner);
	}

	public Term normalizeMod(final Term lhs, final Rational maxNumber) {
		final Theory theory = lhs.getTheory();
		final Sort sort = lhs.getSort();
		final Polynomial arg0 = new Polynomial(lhs);
		arg0.mod(maxNumber);
		final Term div = arg0.isConstant() ? arg0.getConstant().div(maxNumber).floor().toTerm(sort)
				: theory.term("div", arg0.toTerm(sort), maxNumber.toTerm(sort));
		arg0.add(maxNumber.negate(), div);
		return arg0.toTerm(sort);
	}

	private Rational pow2(int exponent) {
		return Rational.valueOf(BigInteger.ONE.shiftLeft(exponent), BigInteger.ONE);
	}

	/*
	 * transforms a bitvector constant c to nat2bv(c')
	 */
	public Term translateBvConstantTerm(final ConstantTerm term) {
		assert term.getSort().isBitVecSort();
		final Theory theory = term.getTheory();
		return int2bv(translateConstant(term.getValue(), theory.getNumericSort()), term.getSort().getIndices());
	}

	/*
	 * Gets as Input the value of a bit-vec const and returns an integer constant
	 */
	private Term translateConstant(final Object value, Sort intSort) {
		BigInteger constValue;
		if (value instanceof String) {
			String bitString = (String) value;
			if (bitString.startsWith("#b")) {
				bitString = (String) value;
				constValue = new BigInteger(bitString.substring(2), 2);
			} else if (bitString.startsWith("#x")) {
				constValue = new BigInteger(bitString.substring(2), 16);
			} else {
				throw new UnsupportedOperationException("Unexpected constant type");
			}
		} else if (value instanceof BigInteger) {
			constValue = (BigInteger) value;
		} else {
			throw new UnsupportedOperationException("Unexpected constant type");
		}
		final Term intConst = Rational.valueOf(constValue, BigInteger.ONE).toTerm(intSort);
		return intConst;
	}

	public Term trackBvRewrite(Term convertedApp, Term translationResult,
			Annotation functionAnnotation) {
		return mTracker.transitivity(convertedApp,
				mTracker.buildRewrite(mTracker.getProvedTerm(convertedApp), translationResult, functionAnnotation));
	}

	public int log2(int number) {
		int log = 0;
		while (number >= (1L << log)) {
			log++;
		}
		return log - 1;
	}

	public Term translateBvshl(final IProofTracker tracker, final FunctionSymbol fsym, final Term convertedApp) {
		final Theory theory = convertedApp.getTheory();
		final Term provedTerm = tracker.getProvedTerm(convertedApp);
		final Term[] params = ((ApplicationTerm) provedTerm).getParameters();
		final Term translatedLHS = ubv2int(params[0], false);
		final Term translatedRHS = ubv2intOrConstant(params[1]);
		final int width = Integer.valueOf(fsym.getReturnSort().getIndices()[0]);
		final Term zero = theory.rational(Rational.ZERO, mInteger);
		final Term transformedAsInt;
		if (translatedRHS instanceof ConstantTerm) {
			final Rational shiftValue = (Rational) ((ConstantTerm) translatedRHS).getValue();
			assert shiftValue.denominator() == BigInteger.ONE && shiftValue.signum() >= 0;
			if (shiftValue.numerator().compareTo(BigInteger.valueOf(width)) >= 0) {
				transformedAsInt = zero;
			} else {
				assert shiftValue.numerator().bitLength() <= 32;
				final int shiftAsInt = shiftValue.numerator().intValue();
				final Polynomial multiply = new Polynomial();
				multiply.add(pow2(shiftAsInt), translatedLHS);
				transformedAsInt = multiply.toTerm(mInteger);
			}
		} else {
			final int logWidth = log2(width);
			final Polynomial shift = new Polynomial(translatedRHS);
			Term result = translatedLHS;
			for (int i = logWidth; i >= 0; i--) {
				final Rational shiftStep = Rational.valueOf(1 << i, 1);
				final Polynomial compare = new Polynomial();
				compare.add(shiftStep);
				compare.add(Rational.MONE, shift);
				final Term cond = theory.term("<=", compare.toTerm(mInteger), zero);
				shift.add(Rational.ONE, theory.term("ite", cond, shiftStep.negate().toTerm(mInteger), zero));
				final Polynomial multiply = new Polynomial();
				multiply.add(pow2(1 << i), result);
				result = theory.term("ite", cond, multiply.toTerm(mInteger), result);
			}
			transformedAsInt = result;
		}
		return trackBvRewrite(convertedApp, int2bv(transformedAsInt, fsym.getReturnSort().getIndices()),
				ProofConstants.RW_BVSHL2INT);
	}

	public Term translateBvshr(final IProofTracker tracker, final FunctionSymbol fsym, final Term convertedApp) {
		final Theory theory = convertedApp.getTheory();
		final Term provedTerm = tracker.getProvedTerm(convertedApp);
		final Term[] params = ((ApplicationTerm) provedTerm).getParameters();
		final int width = Integer.valueOf(fsym.getReturnSort().getIndices()[0]);
		// nat2bv[m](bv2nat([[s]]) div 2^(bv2nat([[t]])))
		final boolean isArith = fsym.getName() == SMTLIBConstants.BVASHR;
		final Term translatedLHS = isArith ? sbv2int(params[0]) : ubv2int(params[0], true);
		final Term translatedRHS = ubv2intOrConstant(params[1]);

		final Term zero = theory.rational(Rational.ZERO, mInteger);
		final Term transformedAsInt;
		if (translatedRHS instanceof ConstantTerm) {
			final Rational shiftValue = (Rational) ((ConstantTerm) translatedRHS).getValue();
			assert shiftValue.denominator() == BigInteger.ONE && shiftValue.signum() >= 0;
			if (shiftValue.numerator().compareTo(BigInteger.valueOf(width)) >= 0) {
				transformedAsInt = zero;
			} else {
				assert shiftValue.numerator().bitLength() <= 32;
				final int shiftAsInt = shiftValue.numerator().intValue();
				if (shiftAsInt == 0) {
					transformedAsInt = translatedLHS;
				} else {
					transformedAsInt = theory.term(SMTLIBConstants.DIV, translatedLHS,
							pow2(shiftAsInt).toTerm(mInteger));
				}
			}
		} else {
			final int logWidth = log2(width);
			final Polynomial shift = new Polynomial(translatedRHS);
			Term result = translatedLHS;
			for (int i = logWidth; i >= 0; i--) {
				final Rational shiftStep = Rational.valueOf(1 << i, 1);
				final Polynomial compare = new Polynomial();
				compare.add(shiftStep);
				compare.add(Rational.MONE, shift);
				final Term cond = theory.term("<=", compare.toTerm(mInteger), zero);
				shift.add(Rational.ONE, theory.term("ite", cond, shiftStep.negate().toTerm(mInteger), zero));
				final Term divide = theory.term(SMTLIBConstants.DIV, result, pow2(1 << i).toTerm(mInteger));
				result = theory.term("ite", cond, divide, result);
			}
			transformedAsInt = result;
		}
		return trackBvRewrite(convertedApp, int2bv(transformedAsInt, fsym.getReturnSort().getIndices()),
				isArith ? ProofConstants.RW_BVASHR2INT : ProofConstants.RW_BVLSHR2INT);
	}

	public Term translateRelations(final IProofTracker tracker, final FunctionSymbol fsym, final Term convertedApp) {
		final Theory theory = convertedApp.getTheory();
		final Term[] params = ((ApplicationTerm) tracker.getProvedTerm(convertedApp)).getParameters();


		final Term transformed;
		final Annotation proofRule;
		String newFsym;
		boolean isSigned;
		assert fsym.isIntern();
		switch (fsym.getName()) {
		case "distinct":
			newFsym = "distinct";
			isSigned = false;
			proofRule = ProofConstants.RW_BVEQ2INT;
			break;
		case "=":
			newFsym = "=";
			isSigned = false;
			proofRule = ProofConstants.RW_BVEQ2INT;
			break;
		case "bvult":
			newFsym = "<";
			isSigned = false;
			proofRule = ProofConstants.RW_BVULT2INT;
			break;
		case "bvule":
			newFsym = "<=";
			isSigned = false;
			proofRule = ProofConstants.RW_BVULE2INT;
			break;
		case "bvugt":
			newFsym = ">";
			isSigned = false;
			proofRule = ProofConstants.RW_BVUGT2INT;
			break;
		case "bvuge":
			newFsym = ">=";
			isSigned = false;
			proofRule = ProofConstants.RW_BVUGE2INT;
			break;
		case "bvslt":
			newFsym = "<";
			isSigned = true;
			proofRule = ProofConstants.RW_BVSLT2INT;
			break;
		case "bvsle":
			newFsym = "<=";
			isSigned = true;
			proofRule = ProofConstants.RW_BVSLE2INT;
			break;
		case "bvsgt":
			newFsym = ">";
			isSigned = true;
			proofRule = ProofConstants.RW_BVSGT2INT;
			break;
		case "bvsge":
			newFsym = ">=";
			isSigned = true;
			proofRule = ProofConstants.RW_BVSGE2INT;
			break;
		default:
			throw new AssertionError("unexpected relation");
		}
		final Term[] translatedArgs = new Term[params.length];
		for (int i = 0; i < params.length; i++) {
			translatedArgs[i] = isSigned ? sbv2int(params[i]) : ubv2int(params[i], true);
		}
		transformed = theory.term(newFsym, translatedArgs);
		return trackBvRewrite(convertedApp, transformed, proofRule);
	}

	// Bring a number into unsigned or signed range of a bitvector.
	private final Term applyMod(final int width, Term integerTerm, boolean isSigned) {
		final Theory theory = integerTerm.getTheory();
		// signed(x) = (x+2^{k-1}) mod 2^k - 2^{k-1}
		final Rational signBit = pow2(width - 1);
		final Rational maxNumber = pow2(width);

		final Polynomial poly = new Polynomial(integerTerm);
		if (isSigned) {
			poly.add(signBit);
		}
		poly.mod(maxNumber);
		final Term shiftedX = poly.toTerm(mInteger);
		if (!poly.isConstant()) {
			poly.add(maxNumber.negate(), theory.term(SMTLIBConstants.DIV, shiftedX, maxNumber.toTerm(mInteger)));
		}
		if (isSigned) {
			poly.add(signBit.negate());
		}
		return poly.toTerm(mInteger);
	}

	public Term bitBlastAndConstant(final Term lhs, final Rational rhs, int width) {
		final Theory theory = lhs.getTheory();
		assert rhs.isIntegral();
		BigInteger mask = rhs.numerator();
		final Polynomial result = new Polynomial();
		if (lhs instanceof ConstantTerm) {
			final Rational lhsRat = (Rational) ((ConstantTerm) lhs).getValue();
			assert lhsRat.isIntegral();
			final BigInteger value = lhsRat.numerator().and(mask);
			return Rational.valueOf(value, BigInteger.ONE).toTerm(mInteger);
		}

		while (true) {
			final int low = mask.getLowestSetBit();
			if (low >= width || low < 0) {
				break;
			}
			final BigInteger powLow = BigInteger.ONE.shiftLeft(low);
			mask = mask.add(powLow);
			if (low == 0) {
				result.add(Rational.ONE, lhs);
			} else {
				final Rational powLowRat = Rational.valueOf(powLow, BigInteger.ONE);
				result.add(powLowRat, theory.term(SMTLIBConstants.DIV, lhs, powLowRat.toTerm(mInteger)));
			}
			final int high = mask.getLowestSetBit();
			if (high >= width || high < 0) {
				break;
			}
			final BigInteger powHigh = BigInteger.ONE.shiftLeft(high);
			mask = mask.subtract(powHigh);
			final Rational powHighRat = Rational.valueOf(powHigh, BigInteger.ONE);
			result.add(powHighRat.negate(), theory.term(SMTLIBConstants.DIV, lhs, powHighRat.toTerm(mInteger)));
		}
		return result.toTerm(mInteger);
	}

	public Term bitBlastAnd(final Term lhs, final Term rhs, int width) {
		final Theory theory = lhs.getTheory();
		if (rhs instanceof ConstantTerm) {
			return bitBlastAndConstant(lhs, (Rational) ((ConstantTerm) rhs).getValue(), width);
		}
		if (lhs instanceof ConstantTerm) {
			return bitBlastAndConstant(rhs, (Rational) ((ConstantTerm) lhs).getValue(), width);
		}
		final Term one = theory.rational(Rational.ONE, mInteger);
		final Term zero = theory.rational(Rational.ZERO, mInteger);
		final Polynomial poly = new Polynomial();

		for (int i = 0; i < width; i++) {
			final Term ite = theory.term("ite", theory.term("=", isel(i, lhs), one), isel(i, rhs), zero);
			poly.add(pow2(i), ite);
		}
		return poly.toTerm(mInteger);
	}

	public Term translateBvandSum(final IProofTracker tracker, final FunctionSymbol fsym, final Term convertedApp) {
		final Sort bvSort = fsym.getReturnSort();
		final int width = Integer.valueOf(bvSort.getIndices()[0]);
		final Term[] params = ((ApplicationTerm) tracker.getProvedTerm(convertedApp)).getParameters();

		final Term lhs = ubv2intOrConstant(params[0]);
		final Term rhs = ubv2intOrConstant(params[1]);

		final Term transformed = int2bv(bitBlastAnd(lhs, rhs, width), bvSort.getIndices());
		return trackBvRewrite(convertedApp, transformed, ProofConstants.RW_BVBLAST);
	}

	// Term that picks the bit at position "i" of integer term "term"
	// interpreted as binary
	private Term isel(final int i, final Term term) {
		final Theory theory = term.getTheory();
		final Sort intSort = theory.getSort(SMTLIBConstants.INT);
		final Term two = theory.rational(Rational.TWO, intSort);
		final Term twoPowI = theory.rational(Rational.valueOf(BigInteger.valueOf(2).pow(i), BigInteger.ONE), intSort);
		return theory.term("mod", theory.term("div", term, twoPowI), two);
	}

	public Term translateBvor(final IProofTracker tracker, final FunctionSymbol fsym, final Term convertedApp) {
		final Term[] params = ((ApplicationTerm) tracker.getProvedTerm(convertedApp)).getParameters();
		final Term lhs = ubv2intOrConstant(params[0]);
		final Term rhs = ubv2intOrConstant(params[1]);
		final Sort bvSort = fsym.getReturnSort();
		final int width = Integer.valueOf(bvSort.getIndices()[0]);
		final Polynomial poly = new Polynomial(lhs);
		poly.add(Rational.ONE, rhs);
		poly.add(Rational.MONE, bitBlastAnd(lhs, rhs, width));
		final Term transformed = int2bv(poly.toTerm(mInteger), bvSort.getIndices());
		return trackBvRewrite(convertedApp, transformed, ProofConstants.RW_BVBLAST);
	}

	public Term translateBvxor(final IProofTracker tracker, final FunctionSymbol fsym, final Term convertedApp) {
		final Term[] params = ((ApplicationTerm) tracker.getProvedTerm(convertedApp)).getParameters();
		final Term lhs = ubv2intOrConstant(params[0]);
		final Term rhs = ubv2intOrConstant(params[1]);
		final Sort bvSort = fsym.getReturnSort();
		final int width = Integer.valueOf(bvSort.getIndices()[0]);
		final Polynomial poly = new Polynomial(lhs);
		poly.add(Rational.ONE, rhs);
		poly.add(Rational.TWO.negate(), bitBlastAnd(lhs, rhs, width));
		final Term transformed = int2bv(poly.toTerm(mInteger), bvSort.getIndices());
		return trackBvRewrite(convertedApp, transformed, ProofConstants.RW_BVBLAST);
	}

	public Term translateBvToInt(final IProofTracker tracker, final FunctionSymbol fsym, final Term convertedApp) {
		final Theory theory = fsym.getTheory();
		final Term[] params = ((ApplicationTerm) tracker.getProvedTerm(convertedApp)).getParameters();
		final int inputWidth = Integer.valueOf(params[0].getSort().getIndices()[0]);
		if (params[0] instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) params[0];
			if (appTerm.getFunction().getName() == SMTLIBConstants.ITE) {
				// lift ite.
				final Term[] iteParams = appTerm.getParameters();
				final Term newTerm = theory.term(SMTLIBConstants.ITE, iteParams[0], theory.term(fsym, iteParams[1]),
						theory.term(fsym, iteParams[2]));
				return trackBvRewrite(convertedApp, newTerm, ProofConstants.RW_BVLIFTITE);
			}
			if (appTerm.getFunction().getName() == SMTLIBConstants.INT_TO_BV) {
				final Term intArg = appTerm.getParameters()[0];
				final boolean isSigned = fsym.getName() == SMTLIBConstants.SBV_TO_INT;
				final Term transformed = applyMod(inputWidth, intArg, isSigned);
				return trackBvRewrite(convertedApp, transformed, ProofConstants.RW_BV2NAT);
			}
		}
		if (fsym.getName() == SMTLIBConstants.SBV_TO_INT) {
			// normalize to UBV_TO_INT
			final Term intArg = ubv2int(params[0], true);
			final Term transformed = applyMod(inputWidth, intArg, true);
			return trackBvRewrite(convertedApp, transformed, ProofConstants.RW_BV2NAT);
		} else {
			// nothing to do.
			return convertedApp;
		}
	}

	public Term translateIntToBv(IProofTracker tracker, FunctionSymbol fsym, Term convertedApp) {
		final Term appTerm = tracker.getProvedTerm(convertedApp);
		final Term[] params = ((ApplicationTerm) appTerm).getParameters();
		final Term rhs = int2bv(params[0], fsym.getReturnSort().getIndices());
		if (rhs == appTerm) {
			return convertedApp;
		} else {
			return trackBvRewrite(convertedApp, rhs, ProofConstants.RW_NAT2BV);
		}
	}
}
