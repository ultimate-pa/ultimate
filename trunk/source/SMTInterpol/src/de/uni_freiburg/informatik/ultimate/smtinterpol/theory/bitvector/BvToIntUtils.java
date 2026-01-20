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
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IProofTracker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofConstants;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.Polynomial;

public class BvToIntUtils extends BvUtils {

	private final Sort mInteger;
	IProofTracker mTracker;
	boolean mDealWithBvToNatAndNatToBvInPreprocessing;

	public BvToIntUtils(Theory theory, final IProofTracker tracker,
			final boolean dealWithBvToNatAndNatToBvInPreprocessing) {
		mTracker = tracker;
		mInteger = theory.getSort(SMTLIBConstants.INT);
		mDealWithBvToNatAndNatToBvInPreprocessing = dealWithBvToNatAndNatToBvInPreprocessing;
	}

	/*
	 * Deals with the uninterpreted function symbol bv2nat. Call this instead of
	 * theory.term(SMTLIBConstants.BV_TO_INT, param); Does local simplifications,
	 * without using pushTerm to go throu the term again. Replaces bv2nat by a
	 * modulo in most cases
	 *
	 * At the end bv2nat should only be around uninterpreted functions (constants
	 * variables, selects, ...)
	 *
	 * TODO
	 *
	 * Case Switch, param is nat2bv (return param of nat2bv), param is constant,
	 *
	 */
	public Term ubv2int(final Term param, boolean mod) {
		final Theory theory = param.getTheory();
		assert param.getSort().isBitVecSort();
		if (param instanceof ApplicationTerm && mDealWithBvToNatAndNatToBvInPreprocessing) {
			final ApplicationTerm apParam = (ApplicationTerm) param;
			if (apParam.getFunction().getName().equals(SMTLIBConstants.INT_TO_BV)) {
				final Term argument = apParam.getParameters()[0];
				if (mod) {
					final int width = Integer.valueOf(apParam.getSort().getIndices()[0]);
					final Rational maxNumber = pow2(width);
					if (argument instanceof ConstantTerm) {
						final Rational rat = (Rational) ((ConstantTerm) argument).getValue();
						return rat.sub(maxNumber.mul(rat.div(maxNumber).floor())).toTerm(mInteger);
					} else {
						return theory.term("mod", argument, maxNumber.toTerm(mInteger));
					}
				} else {
					return argument;
				}
			}
			if (apParam.getFunction().getName().equals("ite")) {
				return theory.term("ite", apParam.getParameters()[0], ubv2int(apParam.getParameters()[1], mod),
						ubv2int(apParam.getParameters()[2], mod));
			}
		}
		return theory.term(SMTLIBConstants.UBV_TO_INT, param);
	}

	public Term int2bv(final Term param, final String[] width) {
		final Theory theory = param.getTheory();
		assert param.getSort().isNumericSort();
		return theory.term(SMTLIBConstants.INT_TO_BV, width, null, param);
	}

	public Term normalizeMod(final Term lhs, final Rational maxNumber) {
		final Theory theory = lhs.getTheory();
		final Sort sort = lhs.getSort();
		final SMTAffineTerm arg0 = new SMTAffineTerm(lhs);
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

	public Term translateBvArithmetic(final IProofTracker tracker, final FunctionSymbol fsym,
			final Term convertedApp) {
		final Term provedTerm = tracker.getProvedTerm(convertedApp);
		final Term[] params = ((ApplicationTerm) provedTerm).getParameters();
		Annotation proofRule = null;
		final Polynomial poly = new Polynomial(ubv2int(params[0], false));
		final Polynomial secondParam = new Polynomial(ubv2int(params[1], false));
		switch (fsym.getName()) {
		case "bvadd": {
			poly.add(Rational.ONE, secondParam);
			proofRule = ProofConstants.RW_BVADD2INT;
			break;
		}
		case "bvsub": {
			poly.add(Rational.MONE, secondParam);
			proofRule = ProofConstants.RW_BVSUB2INT;
			break;
		}
		case "bvmul": {
			poly.mul(secondParam);
			proofRule = ProofConstants.RW_BVMUL2INT;
			break;
		}
		default:
			throw new UnsupportedOperationException(
					"Not an artihmetic BitVector Function: " + fsym.getName());
		}
		Term transformed = poly.toTerm(mInteger);
		transformed = int2bv(transformed, params[0].getSort().getIndices());
		return trackBvRewrite(convertedApp, transformed, proofRule);
	}

	// nat2bv[m](2^m - bv2nat([[s]]))
	public Term translateBvNeg(final IProofTracker tracker, final FunctionSymbol fsym, final Term convertedApp) {
		final Term provedTerm = mTracker.getProvedTerm(convertedApp);
		final Term[] params = ((ApplicationTerm) provedTerm).getParameters();
		// nat2bv[m](-bv2nat([[s]]))
		final Polynomial poly = new Polynomial();
		poly.add(Rational.MONE, ubv2int(params[0], false));
		final Term negResult = poly.toTerm(mInteger);
		Term transformed;
		transformed = int2bv(negResult, params[0].getSort().getIndices());
		return trackBvRewrite(convertedApp, transformed, ProofConstants.RW_BVNEG2INT);
	}

	public Term translateBvNot(final IProofTracker tracker, final FunctionSymbol fsym, final Term convertedApp) {
		final Term provedTerm = mTracker.getProvedTerm(convertedApp);
		final Term[] params = ((ApplicationTerm) provedTerm).getParameters();
		final int widthInt = Integer.valueOf(fsym.getReturnSort().getIndices()[0]);
		// We optimize for unsigned mode. not is more likely to be used on unsigned.
		// nat2bv[m](2^k-1-bv2nat([[s]]))
		final Polynomial poly = new Polynomial();
		poly.add(pow2(widthInt).add(Rational.MONE));
		poly.add(Rational.MONE, ubv2int(params[0], false));
		final Term not = poly.toTerm(mInteger);
		final Term transformed = int2bv(not, params[0].getSort().getIndices());
		return trackBvRewrite(convertedApp, transformed, ProofConstants.RW_BVNOT2INT);
	}

	public Term translateConcat(final IProofTracker tracker, final FunctionSymbol fsym, final Term convertedApp) {
		final Term provedTerm = tracker.getProvedTerm(convertedApp);
		final Term[] params = ((ApplicationTerm) provedTerm).getParameters();
		final int widthInt = Integer.valueOf(params[1].getSort().getIndices()[0]); // width of second argument
		final Polynomial poly = new Polynomial();
		poly.add(pow2(widthInt), ubv2int(params[0], false));
		poly.add(Rational.ONE, ubv2int(params[1], true));
		final Term concat = poly.toTerm(mInteger);
		final Term transformed = int2bv(concat, fsym.getReturnSort().getIndices());
		return trackBvRewrite(convertedApp, transformed, ProofConstants.RW_CONCAT2INT);
	}

	public Term translateRepeat(final Term[] params, final FunctionSymbol fsym, final Term convertedApp) {
		assert params.length == 1 && fsym.getIndices().length == 1;
		final int repeatCount = Integer.parseInt(fsym.getIndices()[0]);
		final int bvWidth = Integer.valueOf(params[0].getSort().getIndices()[0]);
		final Rational magicMultiplier = pow2(repeatCount * bvWidth).add(Rational.MONE)
				.div(pow2(bvWidth).add(Rational.MONE));

		final Polynomial poly = new Polynomial();
		poly.add(magicMultiplier, ubv2int(params[0], false));
		final Term repeated = poly.toTerm(mInteger);
		final Term transformed = int2bv(repeated, fsym.getReturnSort().getIndices());
		return trackBvRewrite(convertedApp, transformed, ProofConstants.RW_REPEAT2INT);
	}

	public Term translateBvudiv(final IProofTracker tracker, final FunctionSymbol fsym, final Term convertedApp) {
		final Theory theory = convertedApp.getTheory();
		final Term provedTerm = tracker.getProvedTerm(convertedApp);
		final Term[] params = ((ApplicationTerm) provedTerm).getParameters();
		final int widthInt = Integer.valueOf(fsym.getReturnSort().getIndices()[0]);
		final BigInteger two = BigInteger.valueOf(2);
		// 2 pow width
		final Term maxNumberMinusOne = theory.rational(
				Rational.valueOf(two.pow(widthInt).subtract(BigInteger.ONE), BigInteger.ONE),
				theory.getSort(SMTLIBConstants.INT));

		final Term ifTerm = theory.term("=", ubv2int(params[1], true),
				theory.rational(Rational.ZERO, theory.getSort(SMTLIBConstants.INT)));
		final Term thenTerm = maxNumberMinusOne;
		final Term elseTerm = theory.term("div", ubv2int(params[0], true), ubv2int(params[1], true));
		final Term transformed = int2bv(theory.term("ite", ifTerm, thenTerm, elseTerm),
				fsym.getReturnSort().getIndices());

		return trackBvRewrite(convertedApp, transformed, ProofConstants.RW_BVUDIV2INT);
	}

	public Term translateBvurem(final IProofTracker tracker, final FunctionSymbol fsym, final Term convertedApp) {
		final Theory theory = convertedApp.getTheory();
		final Term provedTerm = tracker.getProvedTerm(convertedApp);
		final Term[] params = ((ApplicationTerm) provedTerm).getParameters();
		final Sort intSort = theory.getSort(SMTLIBConstants.INT);
		final Term lhs = ubv2int(params[0], true);
		final Term rhs = ubv2int(params[1], true);

		final Term ifTerm = theory.term("=", rhs, theory.rational(Rational.ZERO, intSort));
		final Term thenTerm = lhs;
		final Term elseTerm = theory.term("mod", lhs, rhs);

		final Term transformed = int2bv(theory.term("ite", ifTerm, thenTerm, elseTerm),
				fsym.getReturnSort().getIndices());

		return trackBvRewrite(convertedApp, transformed, ProofConstants.RW_BVUREM2INT);
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
		final Term translatedRHS = ubv2int(params[1], true);
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

	public Term translateBvlshr(final IProofTracker tracker, final FunctionSymbol fsym, final Term convertedApp) {
		final Theory theory = convertedApp.getTheory();
		final Term provedTerm = tracker.getProvedTerm(convertedApp);
		final Term[] params = ((ApplicationTerm) provedTerm).getParameters();
		final int width = Integer.valueOf(fsym.getReturnSort().getIndices()[0]);
		// nat2bv[m](bv2nat([[s]]) div 2^(bv2nat([[t]])))
		final Term translatedLHS = ubv2int(params[0], true);
		final Term translatedRHS = ubv2int(params[1], true);

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
				ProofConstants.RW_BVLSHR2INT);
	}

	public Term translateExtract(final IProofTracker tracker, final FunctionSymbol fsym, final Term convertedApp) {
		final Theory theory = convertedApp.getTheory();
		final Term provedTerm = tracker.getProvedTerm(convertedApp);
		final Term[] params = ((ApplicationTerm) provedTerm).getParameters();
		final Sort intSort = theory.getSort(SMTLIBConstants.INT);
		final Term translatedLHS = ubv2int(params[0], false);
		final int lowerIndex = Integer.parseInt(fsym.getIndices()[1]);
		final int upperIndex = Integer.parseInt(fsym.getIndices()[0]);
		final int extractedWidth = upperIndex - lowerIndex + 1;

		Term resultTerm;
		if (translatedLHS instanceof ConstantTerm) {
			final Rational modulus = pow2(extractedWidth);
			Rational result = (Rational) ((ConstantTerm) translatedLHS).getValue();
			result = result.div(pow2(lowerIndex)).floor();
			result = result.sub(modulus.mul(result.div(modulus).floor()));
			resultTerm = result.toTerm(intSort);
		} else {
			resultTerm = theory.term(SMTLIBConstants.DIV, translatedLHS, pow2(lowerIndex).toTerm(intSort));
		}

		final String[] newWidth = new String[1];
		newWidth[0] = String.valueOf(extractedWidth);

		final Term transformed = int2bv(resultTerm, newWidth);
		return trackBvRewrite(convertedApp, transformed, ProofConstants.RW_EXTRACT2INT);
	}

	public Term translateRelations(final IProofTracker tracker, final FunctionSymbol fsym, final Term convertedApp) {
		final Theory theory = convertedApp.getTheory();
		final Term[] params = ((ApplicationTerm) tracker.getProvedTerm(convertedApp)).getParameters();
		final int width = Integer.valueOf(params[0].getSort().getIndices()[0]);


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
			translatedArgs[i] = ubv2int(params[i], !isSigned);
			if (isSigned) {
				translatedArgs[i] = uts(width, translatedArgs[i]);
			}
		}
		transformed = theory.term(newFsym, translatedArgs);
		return trackBvRewrite(convertedApp, transformed, proofRule);
	}

	// unsigned to signed for relations
	private final Term uts(final int width, Term bv2natparam) {
		final Theory theory = bv2natparam.getTheory();
		// signed(x) = (x+2^{k-1}) mod 2^k - 2^{k-1}
		final Rational signBit = pow2(width - 1);
		final Rational maxNumber = pow2(width);

		if (bv2natparam instanceof ConstantTerm) {
			Rational value = (Rational) ((ConstantTerm) bv2natparam).getValue();
			value = value.sub(value.add(signBit).div(maxNumber).floor().mul(maxNumber));
			return value.toTerm(mInteger);
		} else {
			final Polynomial poly = new Polynomial(bv2natparam);
			poly.add(signBit);
			final Term shiftedX = poly.toTerm(mInteger);
			poly.add(maxNumber.negate(), theory.term(SMTLIBConstants.DIV, shiftedX, maxNumber.toTerm(mInteger)));
			poly.add(signBit.negate());
			return poly.toTerm(mInteger);
		}
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

		final Term lhs = ubv2int(params[0], false);
		final Term rhs = ubv2int(params[1], false);

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
		final Term lhs = ubv2int(params[0], false);
		final Term rhs = ubv2int(params[1], false);
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
		final Term lhs = ubv2int(params[0], false);
		final Term rhs = ubv2int(params[1], false);
		final Sort bvSort = fsym.getReturnSort();
		final int width = Integer.valueOf(bvSort.getIndices()[0]);
		final Polynomial poly = new Polynomial(lhs);
		poly.add(Rational.ONE, rhs);
		poly.add(Rational.TWO.negate(), bitBlastAnd(lhs, rhs, width));
		final Term transformed = int2bv(poly.toTerm(mInteger), bvSort.getIndices());
		return trackBvRewrite(convertedApp, transformed, ProofConstants.RW_BVBLAST);
	}

	public Term translateExtend(final IProofTracker tracker, final FunctionSymbol fsym, final Term convertedApp) {
		final Term[] params = ((ApplicationTerm) tracker.getProvedTerm(convertedApp)).getParameters();
		Term arg;
		Annotation proofRule;
		if (fsym.getName().equals(SMTLIBConstants.ZERO_EXTEND)) {
			arg = ubv2int(params[0], true);
			proofRule = ProofConstants.RW_ZEROEXTEND;
		} else {
			final int inputWidth = Integer.valueOf(params[0].getSort().getIndices()[0]);
			arg = uts(inputWidth, ubv2int(params[0], false));
			proofRule = ProofConstants.RW_SIGNEXTEND;
		}
		final Term transformed = int2bv(arg, fsym.getReturnSort().getIndices());
		return trackBvRewrite(convertedApp, transformed, proofRule);
	}

	public Term translateSbvToInt(final IProofTracker tracker, final FunctionSymbol fsym, final Term convertedApp) {
		final Term[] params = ((ApplicationTerm) tracker.getProvedTerm(convertedApp)).getParameters();
		Annotation proofRule;
		final int inputWidth = Integer.valueOf(params[0].getSort().getIndices()[0]);
		final Term transformed = uts(inputWidth, ubv2int(params[0], false));
		proofRule = ProofConstants.RW_BV_EXPAND_DEF;
		return trackBvRewrite(convertedApp, transformed, proofRule);
	}
}
