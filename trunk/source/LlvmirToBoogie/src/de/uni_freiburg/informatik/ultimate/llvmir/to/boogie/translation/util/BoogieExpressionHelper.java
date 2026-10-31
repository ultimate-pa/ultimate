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
package de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util;

import java.math.BigInteger;
import java.util.List;

import org.antlr.v4.runtime.ParserRuleContext;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogiePrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LLVMIRParser;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LlvmirLocation;

/**
 * Stateless helper methods for the translation of LLVM IR to Boogie.
 *
 * The methods were moved unchanged out of the LlvmirToBoogieVisitor. They only read their parameters or the parse tree
 * and never access the state of the visitor.
 */
public final class BoogieExpressionHelper {

	public static final String LABEL_IDENTIFIER = "aux#label";
	public static final String UNDEF_IDENTIFIER = "aux#undef";

	private BoogieExpressionHelper() {
		// utility class, not meant to be instantiated
	}

	/**
	 * Unifies the identifier by removing colons and ensuring it starts with a valid character.
	 *
	 * This method is used to ensure that identifiers in the Boogie AST conform to the expected format.
	 *
	 * @param identifier
	 *            The identifier to be unified.
	 * @return A unified identifier string.
	 */
	public static String unifyIdentifier(final String identifier) {
		if (identifier == null || identifier.isEmpty()) {
			return identifier;
		}
		String result = identifier;
		result = result.replace(":", "");
		final char firstChar = result.charAt(0);
		if (result.startsWith("aux#")) {
			return result;
		} else if (Character.isLetterOrDigit(firstChar)) {
			return '#' + result;
		}
		return '#' + result.substring(1);
	}

	/**
	 * Constructs an expression from a value context, type context, and location.
	 *
	 * This method constructs an Expression based on the provided value context, type context, and location. It handles
	 * both local identifiers and constants, converting them into appropriate expressions.
	 *
	 * @param valueContext
	 *            The context containing the value to be converted into an expression.
	 * @param typeContext
	 *            The context containing the type information for the value.
	 * @param location
	 *            The location in the source code where this value is defined.
	 * @param isSigned
	 *            Indicates whether the value should be treated as signed or unsigned.
	 * @return An Expression representing the value.
	 * @throws AssertionError
	 *             if the value type is not supported.
	 */
	public static Expression constructExpressionFromValue(final LLVMIRParser.ValueContext valueContext,
			final ParserRuleContext typeContext, final LlvmirLocation location, final boolean isSigned)
			throws AssertionError {
		if (valueContext.LocalIdent() != null) {
			return constructIdentifierExpression(location, valueContext, typeContext);
		} else if (valueContext.constant() != null) {
			return constructExpressionFromConstant(valueContext.constant(), typeContext, location, isSigned);
		} else {
			throw new AssertionError("Unsupported value type: " + valueContext.getText());
		}
	}

	/**
	 * Constructs an expression from a constant value based on the provided constant context and type context.
	 *
	 * This method handles different types of constants (integer, boolean, undef) and constructs the corresponding
	 * expression. It also ensures that integer constants are adjusted to fit within the specified bit length.
	 *
	 * @param constantContext
	 *            The context containing the constant value.
	 * @param typeContext
	 *            The context containing the type information for the constant.
	 * @param location
	 *            The location in the source code where this constant is defined.
	 * @param isSigned
	 *            Indicates whether the constant should be treated as signed or unsigned.
	 * @return An Expression representing the constant value.
	 * @throws AssertionError
	 *             if the constant type is not supported.
	 */
	public static Expression constructExpressionFromConstant(final LLVMIRParser.ConstantContext constantContext,
			final ParserRuleContext typeContext, final LlvmirLocation location, final boolean isSigned)
			throws AssertionError {
		if (constantContext.intConst() != null) {
			if (typeContext.getText().equals("i1")) {
				return new BooleanLiteral(location, constantContext.intConst().getText().equals("1"));
			}
			final int bitLength = getBitLengthFromType(typeContext);
			final BigInteger constValue = BigInteger.valueOf(Long.parseLong(constantContext.intConst().getText()));
			final BigInteger modValue = euclideanMod(constValue, bitLength, isSigned);
			return new IntegerLiteral(location, modValue.toString());
		} else if (constantContext.boolConst() != null) {
			return new BooleanLiteral(location, constantContext.boolConst().getText().equals("true"));
		} else if (constantContext.undefConst() != null) {
			return new IdentifierExpression(location, UNDEF_IDENTIFIER);
		}
		throw new AssertionError("Unsupported constant type: " + constantContext.getText());
	}

	/**
	 * Constructs an identifier expression from a value context and type context.
	 *
	 * This method constructs an IdentifierExpression based on the provided value context and type context. It assumes
	 * that the value context contains a local identifier and uses the type context to determine the type of the
	 * identifier.
	 *
	 * @param location
	 *            The location in the source code where this identifier is defined.
	 * @param valueContext
	 *            The context containing the value to be converted into an identifier expression.
	 * @param typeContext
	 *            The context containing the type information for the identifier.
	 * @return An IdentifierExpression representing the local identifier.
	 * @throws AssertionError
	 *             if the value context does not contain a local identifier or if the contexts are null.
	 */
	public static IdentifierExpression constructIdentifierExpression(final LlvmirLocation location,
			final LLVMIRParser.ValueContext valueContext, final ParserRuleContext typeContext) throws AssertionError {
		if (valueContext == null || typeContext == null) {
			throw new AssertionError("Value context and type context must not be null.");
		}
		if (valueContext.LocalIdent() == null) {
			throw new AssertionError("Value context must contain a LocalIdent.");
		}

		final BoogiePrimitiveType type =
				typeContext.getText().equals("i1") ? BoogieType.TYPE_BOOL : BoogieType.TYPE_INT;
		final String operandName = valueContext.LocalIdent().getText();
		final DeclarationInformation.StorageClass storageClass =
				isParamInProcedure(unifyIdentifier(operandName), valueContext)
						? DeclarationInformation.StorageClass.PROC_FUNC_INPARAM
						: DeclarationInformation.StorageClass.LOCAL;
		final String procedureIdentifier = getProcedureIdentifierFromContext(valueContext);
		final DeclarationInformation declInfo = new DeclarationInformation(storageClass, procedureIdentifier);
		return new IdentifierExpression(location, type, unifyIdentifier(operandName), declInfo);
	}

	/**
	 * Constructs a bit length literal based on the provided bit length.
	 *
	 * This method creates an IntegerLiteral that represents (2^bitLength-isSigned).
	 *
	 * @param location
	 *            The location in the source code where this literal is defined.
	 * @param bitLength
	 *            The bit length for which to construct the literal.
	 * @param isSigned
	 *            Indicates whether the bit length is for a signed integer.
	 * @return An IntegerLiteral representing (2^bitLength-isSigned).
	 * @throws AssertionError
	 *             if the bit length is not a positive integer.
	 */
	public static IntegerLiteral constructBitLengthLiteral(final LlvmirLocation location, final int bitLength,
			final boolean isSigned) {
		if (bitLength <= 0) {
			throw new AssertionError("Bit length must be a positive integer.");
		}
		return new IntegerLiteral(location, BigInteger.ONE.shiftLeft(bitLength - (isSigned ? 1 : 0)).toString());
	}

	/**
	 * Constructs an expression that converts an unsigned integer to a signed integer based on the specified bit length.
	 *
	 * This method checks if the given expression is greater than or equal to the maximum value for the specified bit
	 * length. If it is, it subtracts the maximum value from the expression to convert it to a signed representation.
	 *
	 * @param expr
	 *            The expression to be converted.
	 * @param bitLength
	 *            The bit length for the conversion.
	 * @param location
	 *            The location in the source code where this conversion occurs.
	 * @return An IfThenElseExpression representing the signed conversion.
	 */
	public static Expression constructSignedExpression(final Expression expr, final int bitLength,
			final LlvmirLocation location) {
		final IntegerLiteral maxValueLiteral = new IntegerLiteral(location,
				BigInteger.ONE.shiftLeft(bitLength - 1).subtract(BigInteger.ONE).toString());
		final IntegerLiteral bitLengthLiteral =
				new IntegerLiteral(location, BigInteger.ONE.shiftLeft(bitLength).toString());
		final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.COMPGT, expr, maxValueLiteral);
		final BinaryExpression thenExpr = new BinaryExpression(location, Operator.ARITHMINUS, expr, bitLengthLiteral);
		final IfThenElseExpression ifThenElseExpr = new IfThenElseExpression(location, binaryExpr, thenExpr, expr);
		return ifThenElseExpr;
	}

	/**
	 * Computes the euclidean modulus of a value based on the specified bit length and signedness.
	 *
	 * This method calculates the modulus of a given value with respect to a power of two, ensuring that the result is
	 * always non-negative. It handles both signed and unsigned integers by adjusting the modulus accordingly.
	 *
	 * @param value
	 *            The value for which to compute the modulus.
	 * @param bitLength
	 *            The bit length to use for the modulus calculation.
	 * @param isSigned
	 *            Indicates whether the value is signed or unsigned.
	 * @return A BigInteger representing the non-negative modulus of the value.
	 */
	public static BigInteger euclideanMod(final BigInteger value, final int bitLength, final boolean isSigned) {
		final BigInteger modulus = BigInteger.ONE.shiftLeft(bitLength - (isSigned ? 1 : 0));
		return ((value.mod(modulus)).add(modulus)).mod(modulus);
	}

	/**
	 * Converts a string representation of a comparison operator to its corresponding Boogie operator.
	 *
	 * This method maps the LLVM IR comparison operators (like "eq", "ne", "sle", etc.) to their Boogie equivalents
	 * (like COMPEQ, COMPNEQ, COMPLEQ, etc.).
	 *
	 * @param operatorValue
	 *            The string representation of the comparison operator.
	 * @return The corresponding Boogie Operator.
	 * @throws AssertionError
	 *             if the operator is not supported.
	 */
	public static Operator getCompOperatorFromOperatorValue(final String operatorValue) {
		switch (operatorValue) {
		case "eq":
			return Operator.COMPEQ;
		case "ne":
			return Operator.COMPNEQ;
		case "sle":
		case "ule":
			return Operator.COMPLEQ;
		case "slt":
		case "ult":
			return Operator.COMPLT;
		case "sge":
		case "uge":
			return Operator.COMPGEQ;
		case "sgt":
		case "ugt":
			return Operator.COMPGT;
		default:
			throw new AssertionError("Unsupported operator: " + operatorValue);
		}
	}

	/**
	 * Constructs an assignment statement to assign a label index to the label variable.
	 *
	 * This method constructs an assignment statement that assigns the specified label index to the label variable
	 * identified by `LABEL_IDENTIFIER`.
	 *
	 * @param location
	 *            The location in the source code where this assignment occurs.
	 * @param labelIndex
	 *            The index of the label to be assigned.
	 * @return An AssignmentStatement object representing the assignment.
	 */
	public static AssignmentStatement constructLabelAssignment(final LlvmirLocation location, final int labelIndex) {
		final IntegerLiteral labelIndexLiteral = new IntegerLiteral(location, Integer.toString(labelIndex));
		final VariableLHS labelVar = new VariableLHS(location, LABEL_IDENTIFIER);
		return new AssignmentStatement(location, new LeftHandSide[] { labelVar },
				new Expression[] { labelIndexLiteral });
	}

	/**
	 * Retrieves the bit length from a type context.
	 *
	 * This method extracts the bit length from a type context, which can be either a ConcreteTypeContext or a
	 * TypeContext. It assumes that the type is an integer type (e.g., "i32") and returns the bit length as an integer.
	 *
	 * @param typeContext
	 *            The type context from which to extract the bit length.
	 * @return The bit length of the integer type.
	 * @throws AssertionError
	 *             if the type context is not supported.
	 */
	public static int getBitLengthFromType(final ParserRuleContext typeContext) throws AssertionError {
		if (typeContext instanceof LLVMIRParser.ConcreteTypeContext) {
			final String typeString = ((LLVMIRParser.ConcreteTypeContext) typeContext).intType().getText();
			return Integer.parseInt(typeString.substring(1));
		} else if (typeContext instanceof LLVMIRParser.TypeContext) {
			final String typeString = ((LLVMIRParser.TypeContext) typeContext).intType().getText();
			return Integer.parseInt(typeString.substring(1));
		}
		throw new AssertionError("Unsupported type context for bit length extraction.");
	}

	/**
	 * Retrieves the procedure identifier from the context by traversing the parent hierarchy.
	 *
	 * This method searches for the nearest FuncDefContext in the parent hierarchy of the given context and extracts the
	 * procedure identifier from its FuncHeaderContext.
	 *
	 * @param ctx
	 *            The context from which to start searching for the procedure identifier.
	 * @return The procedure identifier as a String.
	 * @throws AssertionError
	 *             if the context is null or if no FuncDefContext or GlobalIdent is found.
	 */
	public static String getProcedureIdentifierFromContext(final ParserRuleContext ctx) throws AssertionError {
		if (ctx == null) {
			throw new AssertionError("Context must not be null.");
		}
		LLVMIRParser.FuncDefContext funcDefCtx = null;
		ParserRuleContext tmpCtx = ctx;
		while (funcDefCtx == null) {
			if (tmpCtx.getParent() == null) {
				throw new AssertionError("No FuncDefContext found in the parent hierarchy");
			}
			if (tmpCtx.getParent() instanceof LLVMIRParser.FuncDefContext) {
				funcDefCtx = (LLVMIRParser.FuncDefContext) tmpCtx.getParent();
			} else {
				tmpCtx = tmpCtx.getParent();
			}
		}
		final LLVMIRParser.FuncHeaderContext funcHeaderCtx = funcDefCtx.funcHeader();
		if (funcHeaderCtx == null || funcHeaderCtx.GlobalIdent() == null) {
			throw new AssertionError("No FuncHeaderContext or GlobalIdent found for FuncHeaderContext");
		}
		return unifyIdentifier(funcHeaderCtx.GlobalIdent().getText());
	}

	/**
	 * Checks if a given identifier is a parameter in the procedure associated with the provided context.
	 *
	 * This method traverses the parent hierarchy of the given context to find the function definition and then checks
	 * if the specified identifier is listed as a parameter in that function.
	 *
	 * @param identifier
	 *            The identifier to check.
	 * @param ctx
	 *            The context from which to start searching for the function definition.
	 * @return true if the identifier is a parameter in the procedure; false otherwise.
	 * @throws AssertionError
	 *             if the context or identifier is null or empty, or if no function definition is found.
	 */
	public static boolean isParamInProcedure(final String identifier, final ParserRuleContext ctx)
			throws AssertionError {
		if (ctx == null || identifier == null || identifier.isEmpty()) {
			throw new AssertionError("Context and identifier must not be null or empty");
		}
		LLVMIRParser.FuncDefContext funcDefCtx = null;
		ParserRuleContext tmpCtx = ctx;
		while (funcDefCtx == null) {
			if (tmpCtx.getParent() == null) {
				throw new AssertionError("No FuncDefContext found in the parent hierarchy");
			}
			if (tmpCtx.getParent() instanceof LLVMIRParser.FuncDefContext) {
				funcDefCtx = (LLVMIRParser.FuncDefContext) tmpCtx.getParent();
			} else {
				tmpCtx = tmpCtx.getParent();
			}
		}
		final LLVMIRParser.FuncHeaderContext funcHeaderCtx = funcDefCtx.funcHeader();
		if (funcHeaderCtx == null) {
			throw new AssertionError("No FuncHeaderContext found for FuncDefContext");
		}
		final LLVMIRParser.ParamsContext params = funcHeaderCtx.params();
		for (final LLVMIRParser.ParamContext param : params.param()) {
			if (param.LocalIdent() != null && unifyIdentifier(param.LocalIdent().getText()).equals(identifier)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Retrieves the index of a label from the function body based on the provided identifier.
	 *
	 * This method traverses the parent hierarchy of the given context to find the function body and then searches for
	 * the label with the specified identifier within that function body.
	 *
	 * @param ctx
	 *            The context from which to start searching for the function body.
	 * @param incIdentifier
	 *            The identifier of the label to find.
	 * @return The index of the label in the function body.
	 * @throws AssertionError
	 *             if the context or identifier is null or empty, or if no label is found.
	 */
	public static int getLabelIndexFromFuncBody(final ParserRuleContext ctx, final String incIdentifier)
			throws AssertionError {
		if (ctx == null || incIdentifier == null || incIdentifier.isEmpty()) {
			throw new AssertionError("Context and identifier must not be null or empty");
		}
		LLVMIRParser.FuncBodyContext funcBodyCtx = null;
		ParserRuleContext tmpCtx = ctx;
		while (funcBodyCtx == null) {
			if (tmpCtx.getParent() == null) {
				throw new AssertionError("No FuncBodyContext found in the parent hierarchy");
			}
			if (tmpCtx.getParent() instanceof LLVMIRParser.FuncBodyContext) {
				funcBodyCtx = (LLVMIRParser.FuncBodyContext) tmpCtx.getParent();
			} else {
				tmpCtx = tmpCtx.getParent();
			}
		}
		int labelIndex = -1;
		final List<LLVMIRParser.BasicBlockContext> basicBlocks = funcBodyCtx.basicBlock();
		for (final LLVMIRParser.BasicBlockContext block : basicBlocks) {
			if (block.LabelIdent() != null && unifyIdentifier(block.LabelIdent().getText()).equals(incIdentifier)) {
				labelIndex = basicBlocks.indexOf(block);
				break;
			}
		}
		if (labelIndex == -1) {
			throw new AssertionError("No label found for identifier: " + incIdentifier);
		}
		return labelIndex;
	}

	/**
	 * Retrieves the enclosing basic block context for a given parser rule context.
	 *
	 * This method traverses the parse tree upwards from the provided context until it finds a BasicBlockContext. If no
	 * such context is found, an AssertionError is thrown.
	 *
	 * @param ctx
	 *            The parser rule context from which to start the search.
	 * @return The enclosing BasicBlockContext.
	 * @throws AssertionError
	 *             if the provided context is not enclosed in a basic block.
	 */
	public static LLVMIRParser.BasicBlockContext getEnclosingBasicBlock(final ParserRuleContext ctx) {
		ParserRuleContext current = ctx;
		while (current != null && !(current instanceof LLVMIRParser.BasicBlockContext)) {
			current = current.getParent();
		}
		if (current == null) {
			throw new AssertionError("The provided context is not enclosed in a basic block.");
		}
		return (LLVMIRParser.BasicBlockContext) current;
	}
}