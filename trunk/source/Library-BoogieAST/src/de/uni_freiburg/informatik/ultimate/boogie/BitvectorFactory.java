/*
 * Copyright (C) 2021 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogiePrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitvectorConstant;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitvectorConstant.BitvectorConstantOperationResult;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitvectorConstant.BvOp;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitvectorConstant.ExtendOperation;

/**
 * Boogie does not provide native support for most bitvector operations of SMT-LIB. These operations are however very
 * helpful for modeling C programs. Hence we developed a convention based on the :smtdefined attibute that allows us to
 * give Boogie functions the semantics of SMT-LIB functions.
 * {@link https://github.com/ultimate-pa/ultimate/wiki/Boogie#attribute-defined-directives} Unfortunately, this was not
 * sufficient. We also have to be able to translate SMT functions back to Boogie functions. Because of that we want to
 * have a uniform construction for all function declarations and all function calls. This class provides these
 * constructions.
 *
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class BitvectorFactory {

	public static final String AUXILIARY_FUNCTION_PREFIX = "~";

	/**
	 * @return the matching {@link BvOp} value if the identifier represents a supported bitvector operation, or null if
	 *         it does not.
	 */
	public static BvOp getSupportedBitvectorOperation(final String identifier) {
		try {
			return BitvectorConstant.BvOp.valueOf(identifier);
		} catch (final IllegalArgumentException iae) {
			return null;
		}
	}

	public static String generateBoogieFunctionName(final BvOp bvop, final int bitsize) {
		if (bitsize <= 0) {
			throw new IllegalArgumentException();
		}
		switch (bvop) {
		case bvadd:
		case bvand:
		case bvashr:
		case bvlshr:
		case bvmul:
		case bvneg:
		case bvnot:
		case bvor:
		case bvsdiv:
		case bvsge:
		case bvsgt:
		case bvshl:
		case bvsle:
		case bvslt:
		case bvsmod:
		case bvsrem:
		case bvsub:
		case bvudiv:
		case bvuge:
		case bvugt:
		case bvule:
		case bvult:
		case bvurem:
		case bvxor:
			return AUXILIARY_FUNCTION_PREFIX + bvop.toString() + AUXILIARY_FUNCTION_PREFIX + bitsize;
		case concat:
		case extract:
			throw new IllegalArgumentException("Boogie has native support for this operation.");
		case sign_extend:
		case zero_extend:
			throw new IllegalArgumentException("Call method for extend.");
		default:
			throw new AssertionError("unknown value " + bvop);
		}
	}

	public static Expression constructUnaryOperation(final ILocation loc, final BvOp bvop, final Expression expr) {
		if (expr instanceof BitvecLiteral) {
			final BitvectorConstant bc = toConstant((BitvecLiteral) expr);
			final BitvectorConstantOperationResult resBc = BitvectorConstant.apply(bvop, bc);
			return toBitvectorLiteral(loc, resBc.getBvResult());
		}
		final String boogieFunctionName = generateBoogieFunctionName(bvop, isBitvectorSort(expr.getType()));
		final Expression func = ExpressionFactory.constructFunctionApplication(loc, boogieFunctionName,
				new Expression[] { expr }, (BoogieType) expr.getType());
		return func;
	}

	public static Expression constructBinaryOperationForMultipleArguments(final ILocation loc, final BvOp bvop,
			final Expression... exprs) {
		if (exprs.length <= 1) {
			throw new IllegalArgumentException("not binary");
		}
		Expression result = exprs[0];
		for (int i = 1; i < exprs.length; i++) {
			result = constructBinaryBitvectorOperation(loc, bvop, new Expression[] { result, exprs[i] });
		}
		return result;
	}

	/**
	 * Renames a function identifier by removing the first character and removing all occurrences of digits. This
	 * converts, e.g., ~bvadd32, to bvadd.
	 *
	 * @deprecated This is CTranslation-specific code that somehow survived the transport in this plugin.
	 */
	@Deprecated
	public static String getBitvectorSmtFunctionNameFromCFunctionName(final String name) {
		return name.substring(1).replaceAll("\\d+", "");
	}

	/**
	 *
	 * @param extension
	 *            number of bits that are added
	 */
	public static Expression constructExtendOperation(final ILocation loc, final ExtendOperation extendOperation,
			final BigInteger extension, final Expression operandExpression) {
		if (operandExpression instanceof BitvecLiteral) {
			final BitvectorConstant bc = toConstant((BitvecLiteral) operandExpression);
			final BitvectorConstant extendedBc;
			switch (extendOperation) {
			case sign_extend:
				extendedBc = BitvectorConstant.sign_extend(bc, extension);
				break;
			case zero_extend:
				extendedBc = BitvectorConstant.zero_extend(bc, extension);
				break;
			default:
				throw new AssertionError("unknown value " + extendOperation);
			}
			return ExpressionFactory.createBitvecLiteral(loc, extendedBc.getValue().toString(),
					extendedBc.getIndex().intValueExact());
		}
		if (operandExpression.getType() == null) {
			throw new UnsupportedOperationException("Need type to determine bitsize!");
		}
		final int inputBitsize = isBitvectorSort(operandExpression.getType());
		final int resultBitsize = BigInteger.valueOf(inputBitsize).add(extension).intValueExact();
		final BoogieType resultBoogieType = BoogieType.createBitvectorType(resultBitsize);
		final String fullFunctionName =
				BitvectorFactory.generateBoogieFunctionNameForExtend(extendOperation, inputBitsize, resultBitsize);
		return ExpressionFactory.constructFunctionApplication(loc, fullFunctionName,
				new Expression[] { operandExpression }, resultBoogieType);
	}

	public static String generateBoogieFunctionNameForExtend(final ExtendOperation extendOperation,
			final int inputBitsize, final int outputBitsize) {
		return String.join(AUXILIARY_FUNCTION_PREFIX, "", extendOperation.toString(), Integer.toString(outputBitsize),
				Integer.toString(inputBitsize));
	}

	public static Expression constructBinaryBitvectorOperation(final ILocation loc, final BvOp sbo,
			final Expression... args) {
		assert args.length == 2 : "Binary expression cannot have " + args.length + " arguments";
		// check if one of the arguments is a neutral or annihilating literal
		final BitvectorConstant left;
		if (args[0] instanceof BitvecLiteral) {
			left = toConstant((BitvecLiteral) args[0]);
			if (isNeutralLeft(sbo, left)) {
				return args[1];
			}
			if (isAnnihilatingLeft(sbo, left)) {
				return args[0];
			}
		} else {
			left = null;
		}
		final BitvectorConstant right;
		if (args[1] instanceof BitvecLiteral) {
			right = toConstant((BitvecLiteral) args[1]);
			if (isNeutralRight(sbo, right)) {
				return args[0];
			}
			if (isAnnihilatingRight(sbo, right)) {
				return args[1];
			}
		} else {
			right = null;
		}

		// if both arguments are literals, just compute the result
		if (left != null && right != null) {
			return computeBinaryBitvectorExpression(loc, sbo, left, right);
		}

		// we do nothing if both operands are non-constant
		// TODO: We could still do things like (op (op c1 x) (op c2 y)) --> (op c3 op(x y)) with c3 = (op c1 c2) for
		// certain ops
		if (left == null && right == null) {
			return constructBitvectorFunctionApplication(loc, sbo, args);
		}

		if (sbo.isCommutative()) {
			return simplifyBinaryAssociativeExpression(loc, sbo, args, left, right);
		}
		return constructBitvectorFunctionApplication(loc, sbo, args);
	}

	private static FunctionApplication simplifyBinaryAssociativeExpression(final ILocation loc, final BvOp bvop,
			final Expression[] args, final BitvectorConstant left, final BitvectorConstant right) {
		// if this operator is associative, we move literals to the left and check if
		// the right operand has the same
		// operator s.t. we can combine the literals to one.
		if (right == null && args[1] instanceof FunctionApplication) {
			final FunctionApplication rightFunApp = (FunctionApplication) args[1];
			final String rightFunId = rightFunApp.getIdentifier();
			final BvOp rightSbo = getSupportedBitvectorOperation(
					BitvectorFactory.getBitvectorSmtFunctionNameFromCFunctionName(rightFunId));
			if (bvop == rightSbo) {
				final Expression innerLeft = rightFunApp.getArguments()[0];
				if (innerLeft instanceof BitvecLiteral) {
					final Expression newConst =
							computeBinaryBitvectorExpression(loc, bvop, left, toConstant((BitvecLiteral) innerLeft));
					return constructBitvectorFunctionApplication(loc, bvop,
							new Expression[] { newConst, rightFunApp.getArguments()[1] });
				}

			}
			// TODO: There are additional cases where we could compute the result
		}
		if (left == null) {
			// we switch operands so that future calls on this function application can use
			// a simple check
			return simplifyBinaryAssociativeExpression(loc, bvop, new Expression[] { args[1], args[0] }, right, left);
		}
		return constructBitvectorFunctionApplication(loc, bvop, args);
	}

	private static Expression computeBinaryBitvectorExpression(final ILocation loc, final BvOp sbo,
			final BitvectorConstant left, final BitvectorConstant right) {
		if (sbo.isBoolean()) {
			final BitvectorConstantOperationResult result = BitvectorConstant.apply(sbo, left, right);
			assert result.isBoolean();
			return toBooleanLiteral(loc, result.getBooleanResult());
		}
		final BitvectorConstantOperationResult result = BitvectorConstant.apply(sbo, left, right);
		assert !result.isBoolean();
		return toBitvectorLiteral(loc, result.getBvResult());
	}

	static BitvectorConstant toConstant(final BitvecLiteral lit) {
		return new BitvectorConstant(new BigInteger(lit.getValue()), BigInteger.valueOf(lit.getLength()));
	}

	/**
	 * true iff bConst is annihilating (or absorbing) if it is the left operand of op, false otherwise
	 *
	 * If true, then (op bConst x) == bConst for any x
	 */
	private static boolean isAnnihilatingLeft(final BvOp op, final BitvectorConstant bConst) {
		switch (op) {
		case bvsdiv:
		case bvudiv:
		case bvsrem:
		case bvurem:
		case bvmul:
		case bvshl:
		case bvlshr:
			return bConst.isZero();
		case bvor:
		case bvand:
		case bvashr:
			// TODO: Add more elements
		case bvadd:
		case bvsub:
		case bvxor:
		case extract:
		case zero_extend:
		case bvneg:
		case bvnot:
		case bvsle:
		case bvslt:
		case bvuge:
		case bvugt:
		case bvule:
		case bvsge:
		case bvsgt:
		case bvult:
			return false;
		default:
			throw new UnsupportedOperationException("Currently unsupported: " + op);
		}
	}

	/**
	 * true iff bConst is annihilating (or absorbing) if it is the right operand of op, false otherwise
	 *
	 * If true, then (op x bConst) == bConst for any x
	 */
	private static boolean isAnnihilatingRight(final BvOp op, final BitvectorConstant bConst) {
		switch (op) {
		case bvadd:
		case bvor:
		case bvmul:
		case bvxor:
		case bvand:
			return isAnnihilatingLeft(op, bConst);
		case bvudiv:
		case bvashr:
		case bvlshr:
		case bvsrem:
		case bvurem:
		case bvsdiv:
		case bvshl:
		case bvsub:
		case extract:
		case zero_extend:
		case bvneg:
		case bvnot:
		case bvsle:
		case bvslt:
		case bvuge:
		case bvugt:
		case bvule:
		case bvsge:
		case bvsgt:
		case bvult:
			return false;
		default:
			throw new UnsupportedOperationException("Currently unsupported: " + op);
		}
	}

	/**
	 * true iff bConst is neutral if it is the left operand of op, false otherwise
	 *
	 * If true, then (op bConst x) == x for any x
	 */
	private static boolean isNeutralLeft(final BvOp op, final BitvectorConstant bConst) {
		// TODO: Add more left neutral elements
		switch (op) {
		case bvadd:
		case bvor:
			return bConst.isZero();
		case bvmul:
			return bConst.isOne();
		case bvand:
			// TODO: Is this correct?
			return bConst.equals(BitvectorConstant.maxValue(bConst.getIndex()));
		case bvxor:
		case bvudiv:
		case bvashr:
		case bvlshr:
		case bvsrem:
		case bvurem:
		case bvsdiv:
		case bvshl:
		case bvsub:
		case extract:
		case zero_extend:
		case bvneg:
		case bvnot:
		case bvsle:
		case bvslt:
		case bvuge:
		case bvugt:
		case bvule:
		case bvsge:
		case bvsgt:
		case bvult:
			return false;
		default:
			throw new UnsupportedOperationException("Currently unsupported: " + op);
		}
	}

	/**
	 * true iff bConst is neutral if it is the right operand of op, false otherwise
	 *
	 * If true, then (op x bConst) == x for any x
	 */
	private static boolean isNeutralRight(final BvOp op, final BitvectorConstant bConst) {
		switch (op) {
		case bvadd:
		case bvor:
		case bvmul:
		case bvxor:
		case bvand:
			return isNeutralLeft(op, bConst);
		case bvsub:
		case bvashr:
		case bvlshr:
		case bvshl:
			return bConst.isZero();
		case bvudiv:
		case bvsdiv:
			return bConst.isOne();
		case bvsrem:
		case bvurem:
		case extract:
		case zero_extend:
		case bvneg:
		case bvnot:
		case bvsle:
		case bvslt:
		case bvuge:
		case bvugt:
		case bvule:
		case bvsge:
		case bvsgt:
		case bvult:
			return false;
		default:
			throw new UnsupportedOperationException("Currently unsupported: " + op);
		}
	}

	private static BooleanLiteral toBooleanLiteral(final ILocation loc, final boolean value) {
		return new BooleanLiteral(loc, BoogieType.TYPE_BOOL, value);
	}

	private static BitvecLiteral toBitvectorLiteral(final ILocation loc, final BitvectorConstant bitvectorConstant) {
		final int length = bitvectorConstant.getIndex().intValueExact();
		return new BitvecLiteral(loc, BoogieType.createBitvectorType(length), bitvectorConstant.getValue().toString(),
				length);
	}

	private static int isBitvectorSort(final IBoogieType type) {
		final int result;
		if (type instanceof BoogiePrimitiveType) {
			final BoogiePrimitiveType bpType = (BoogiePrimitiveType) type;
			if (bpType.getTypeCode() > 0) {
				// is bitvector
				result = bpType.getTypeCode();
			} else {
				// not a bitvector
				result = -1;
			}
		} else {
			result = -1;
		}
		return result;
	}

	/**
	 * Construct function application for bitvector operation. No optimizations.
	 */
	private static FunctionApplication constructBitvectorFunctionApplication(final ILocation loc, final BvOp bvop,
			final Expression... arguments) {
		if (bvop.getArity() != arguments.length) {
			throw new IllegalArgumentException("Wrong number of arguments");
		}
		final BoogieType resultBoogieType;
		if (bvop.isBoolean()) {
			resultBoogieType = BoogieType.TYPE_BOOL;
		} else {
			resultBoogieType = (BoogieType) arguments[0].getType();
		}
		switch (bvop) {
		case bvadd:
		case bvand:
		case bvashr:
		case bvlshr:
		case bvmul:
		case bvneg:
		case bvnot:
		case bvor:
		case bvsdiv:
		case bvsge:
		case bvsgt:
		case bvshl:
		case bvsle:
		case bvslt:
		case bvsmod:
		case bvsrem:
		case bvsub:
		case bvudiv:
		case bvuge:
		case bvugt:
		case bvule:
		case bvult:
		case bvurem:
		case bvxor:
			final String boogieFunctionName = BitvectorFactory.generateBoogieFunctionName(bvop,
					BitvectorFactory.isBitvectorSort(arguments[0].getType()));
			return new FunctionApplication(loc, resultBoogieType, boogieFunctionName, arguments);
		case concat:
		case extract:
			throw new IllegalArgumentException("Boogie has native support for " + bvop);
		case sign_extend:
		case zero_extend:
			throw new IllegalArgumentException("Should be handled by extend method." + bvop);
		default:
			throw new AssertionError("unknown bvop " + bvop);
		}
	}

}
