/*
 * Copyright (C) 2025 Peter Ritter
 *
 * This file is part of the ULTIMATE LlvmirToBoogie plug-in.
 * It is used to monitor the parsing of LLVM IR files and to translate them into a Boogie AST.
 *
 * The ULTIMATE LlvmirToBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LlvmirToBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LlvmirToBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LlvmirToBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LlvmirToBoogie plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.declarations;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LlvmirLocation;

/**
 * Builders for the auxiliary Boogie functions aux#cdiv and aux#rem, which are used for the integer division and the
 * remainder of LLVM-IR.
 *
 * All methods only work on their parameters and do not access any state of the translation.
 */
public final class AuxFunctionBuilder {

	public static final String CDIV_IDENTIFIER = "aux#cdiv";
	public static final String REM_IDENTIFIER = "aux#rem";
	private static final String X_IDENTIFIER = "aux#x";
	private static final String Y_IDENTIFIER = "aux#y";
	private static final String MAX_FROM_BIT_LENGTH_IDENTIFIER = "aux#maxFromBitLength";
	private static final String IS_SIGNED_IDENTIFIER = "aux#isSigned";

	private AuxFunctionBuilder() {
		// utility class, not meant to be instantiated
	}

	/**
	 * Constructs the aux#cdiv function for signed and unsigned integer division.
	 *
	 * This method creates a FunctionDeclaration for the aux#cdiv function, which performs division while handling
	 * signedness and absolute values. It takes into account various cases of operand signs to ensure correct division
	 * results.
	 *
	 * @param location
	 *            The location in the source code where this function is defined.
	 * @return A FunctionDeclaration representing the aux#cdiv function.
	 */
	public static FunctionDeclaration constructCDivFunction(final LlvmirLocation location) {
		final SignedOperands operand = SignedOperands.create(location);

		final Expression noneAbsDiv = constructBinaryExpression(location, Operator.ARITHDIV, operand.x(), operand.y());
		final Expression bothAbsDiv =
				constructBinaryExpression(location, Operator.ARITHDIV, operand.xAbs(), operand.yAbs());
		final Expression xAbsDiv = constructBinaryExpression(location, Operator.ARITHDIV, operand.xAbs(), operand.y());
		final Expression yAbsDiv = constructBinaryExpression(location, Operator.ARITHDIV, operand.x(), operand.yAbs());

		final Expression resultIsNeg = new IfThenElseExpression(location, operand.xIsNeg(), xAbsDiv, yAbsDiv);
		final Expression negatedResult =
				constructBinaryExpression(location, Operator.ARITHMINUS, operand.zero(), resultIsNeg);
		final Expression resultIsPosBothNeg =
				new IfThenElseExpression(location, operand.bothNeg(), bothAbsDiv, negatedResult);
		final Expression resultIsPosNoneNeg =
				new IfThenElseExpression(location, operand.bothNonNeg(), noneAbsDiv, resultIsPosBothNeg);

		return constructAuxFunction(location, CDIV_IDENTIFIER, resultIsPosNoneNeg);
	}

	/**
	 * Constructs the aux#rem function for signed and unsigned integer remainder.
	 *
	 * This method creates a FunctionDeclaration for the aux#rem function, which computes the remainder while handling
	 * signedness and absolute values. It takes into account various cases of operand signs to ensure correct remainder
	 * results.
	 *
	 * @param location
	 *            The location in the source code where this function is defined.
	 * @return A FunctionDeclaration representing the aux#rem function.
	 */
	public static FunctionDeclaration constructRemainderFunction(final LlvmirLocation location) {
		final SignedOperands operand = SignedOperands.create(location);

		final Expression cdivCall = new FunctionApplication(location, CDIV_IDENTIFIER,
				new Expression[] { operand.x(), operand.y(), operand.maxFromBitLength(), operand.isSigned() });

		final Expression xValue =
				constructBinaryExpression(location, Operator.ARITHMINUS, operand.x(), operand.maxFromBitLength());
		final Expression yValue =
				constructBinaryExpression(location, Operator.ARITHMINUS, operand.y(), operand.maxFromBitLength());

		final Expression yMulCdiv = constructBinaryExpression(location, Operator.ARITHMUL, operand.y(), cdivCall);
		final Expression yAbsMulCdiv = constructBinaryExpression(location, Operator.ARITHMUL, operand.yAbs(), cdivCall);
		final Expression yValueMulCdiv = constructBinaryExpression(location, Operator.ARITHMUL, yValue, cdivCall);

		final Expression xMinusYMulCdiv =
				constructBinaryExpression(location, Operator.ARITHMINUS, operand.x(), yMulCdiv);
		final Expression xAbsMinusYAbsMulCdiv =
				constructBinaryExpression(location, Operator.ARITHMINUS, operand.xAbs(), yAbsMulCdiv);
		final Expression negatedXAbsMinusYAbsMulCdiv =
				constructBinaryExpression(location, Operator.ARITHMINUS, operand.zero(), xAbsMinusYAbsMulCdiv);
		final Expression xValueMinusYMulCdiv =
				constructBinaryExpression(location, Operator.ARITHMINUS, xValue, yMulCdiv);
		final Expression xMinusYValueMulCdiv =
				constructBinaryExpression(location, Operator.ARITHMINUS, operand.x(), yValueMulCdiv);

		final Expression resultOneNeg =
				new IfThenElseExpression(location, operand.xIsNeg(), xValueMinusYMulCdiv, xMinusYValueMulCdiv);
		final Expression resultBothNeg =
				new IfThenElseExpression(location, operand.bothNeg(), negatedXAbsMinusYAbsMulCdiv, resultOneNeg);
		final Expression resultNoneNeg =
				new IfThenElseExpression(location, operand.bothNonNeg(), xMinusYMulCdiv, resultBothNeg);

		return constructAuxFunction(location, REM_IDENTIFIER, resultNoneNeg);
	}

	/**
	 * The sub expressions that aux#cdiv and aux#rem have in common.
	 *
	 * A value x is negative if it is greater or equal than maxFromBitLength / (isSigned + 1). The abs expressions
	 * (maxFromBitLength - x) are the absolute values of negative operands.
	 */
	private record SignedOperands(Expression x, Expression y, Expression maxFromBitLength, Expression isSigned,
			Expression zero, Expression xIsNeg, Expression yIsNeg, Expression xAbs, Expression yAbs,
			Expression bothNonNeg, Expression bothNeg) {

		/**
		 * Constructs the common sub expressions with identifiers for the parameters of aux#cdiv and aux#rem.
		 *
		 * @param location
		 *            The location in the source code that is attached to the created Boogie AST nodes.
		 * @return The common sub expressions.
		 */
		static SignedOperands create(final LlvmirLocation location) {
			final Expression x = new IdentifierExpression(location, X_IDENTIFIER);
			final Expression y = new IdentifierExpression(location, Y_IDENTIFIER);
			final Expression maxFromBitLength = new IdentifierExpression(location, MAX_FROM_BIT_LENGTH_IDENTIFIER);
			final Expression isSigned = new IdentifierExpression(location, IS_SIGNED_IDENTIFIER);
			final Expression zero = new IntegerLiteral(location, "0");

			final Expression signedPlusOne = constructBinaryExpression(location, Operator.ARITHPLUS, isSigned,
					new IntegerLiteral(location, "1"));
			final Expression signedMaxFromBitLength =
					constructBinaryExpression(location, Operator.ARITHDIV, maxFromBitLength, signedPlusOne);

			final Expression xNonNeg = constructBinaryExpression(location, Operator.COMPLT, x, signedMaxFromBitLength);
			final Expression yNonNeg = constructBinaryExpression(location, Operator.COMPLT, y, signedMaxFromBitLength);
			final Expression xIsNeg = constructBinaryExpression(location, Operator.COMPGEQ, x, signedMaxFromBitLength);
			final Expression yIsNeg = constructBinaryExpression(location, Operator.COMPGEQ, y, signedMaxFromBitLength);

			final Expression xAbs = constructBinaryExpression(location, Operator.ARITHMINUS, maxFromBitLength, x);
			final Expression yAbs = constructBinaryExpression(location, Operator.ARITHMINUS, maxFromBitLength, y);

			final Expression bothNonNeg = constructBinaryExpression(location, Operator.LOGICAND, xNonNeg, yNonNeg);
			final Expression bothNeg = constructBinaryExpression(location, Operator.LOGICAND, xIsNeg, yIsNeg);
			return new SignedOperands(x, y, maxFromBitLength, isSigned, zero, xIsNeg, yIsNeg, xAbs, yAbs, bothNonNeg,
					bothNeg);
		}
	}

	/**
	 * Constructs a binary expression.
	 *
	 * @param location
	 *            The location in the source code that is attached to the expression.
	 * @param operator
	 *            The operator of the expression.
	 * @param left
	 *            The left operand.
	 * @param right
	 *            The right operand.
	 * @return The binary expression.
	 */
	private static BinaryExpression constructBinaryExpression(final LlvmirLocation location, final Operator operator,
			final Expression left, final Expression right) {
		return new BinaryExpression(location, operator, left, right);
	}

	/**
	 * Wraps the body into a function declaration with the signature (x, y, maxFromBitLength, isSigned) : int that is
	 * shared by aux#cdiv and aux#rem.
	 *
	 * @param location
	 *            The location in the source code that is attached to the declaration.
	 * @param identifier
	 *            The identifier of the function.
	 * @param body
	 *            The expression that defines the function.
	 * @return A FunctionDeclaration with the given identifier and body.
	 */
	private static FunctionDeclaration constructAuxFunction(final LlvmirLocation location, final String identifier,
			final Expression body) {
		final PrimitiveType intType = new PrimitiveType(location, "int");
		final VarList[] inParams = { new VarList(location, new String[] { X_IDENTIFIER }, intType),
				new VarList(location, new String[] { Y_IDENTIFIER }, intType),
				new VarList(location, new String[] { MAX_FROM_BIT_LENGTH_IDENTIFIER }, intType),
				// isSigned is 1 if signed, 0 if unsigned
				new VarList(location, new String[] { IS_SIGNED_IDENTIFIER }, intType) };
		final VarList outParam = new VarList(location, new String[] {}, intType);
		return new FunctionDeclaration(location, new Attribute[] {}, identifier, new String[] {}, inParams, outParam,
				body);
	}
}