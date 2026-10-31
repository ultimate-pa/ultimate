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

import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.unifyIdentifier;

import java.util.ArrayList;
import java.util.Optional;

import org.antlr.v4.runtime.ParserRuleContext;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LLVMIRParser;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LlvmirLocation;

/**
 * Builders for Boogie declarations, procedures and auxiliary functions used by the translation of LLVM-IR to Boogie.
 *
 * All methods only work on their parameters and do not access any state of the translation.
 */
public final class DeclarationBuilder {

	public static final String CDIV_IDENTIFIER = "aux#cdiv";
	public static final String REM_IDENTIFIER = "aux#rem";
	private static final String X_IDENTIFIER = "aux#x";
	private static final String Y_IDENTIFIER = "aux#y";
	private static final String MAX_FROM_BIT_LENGTH_IDENTIFIER = "aux#maxFromBitLength";
	private static final String IS_SIGNED_IDENTIFIER = "aux#isSigned";

	private DeclarationBuilder() {
		// utility class, not meant to be instantiated
	}

	/**
	 * Constructs a variable declaration from a type and identifier.
	 *
	 * This method constructs a VariableDeclaration object with the specified type and identifier, using the provided
	 * location for the declaration.
	 *
	 * @param type
	 *            The type of the variable (e.g., "int", "bool").
	 * @param identifier
	 *            The identifier for the variable.
	 * @param location
	 *            The location in the source code where this variable is declared.
	 * @return A VariableDeclaration object representing the variable declaration.
	 */
	public static VariableDeclaration constructVarDecFromString(final String type, final String identifier,
			final LlvmirLocation location) {
		final PrimitiveType primType = new PrimitiveType(location, type);
		final VarList varList = new VarList(location, new String[] { unifyIdentifier(identifier) }, primType);
		return new VariableDeclaration(location, new Attribute[] {}, new VarList[] { varList });
	}

	/**
	 * Constructs a variable declaration from a type context, identifier, and location.
	 *
	 * This method constructs a VariableDeclaration object based on the provided type context and identifier.
	 *
	 * @param typeContext
	 *            The type context from which to extract the type information.
	 * @param identifier
	 *            The identifier for the variable.
	 * @param location
	 *            The location in the source code where this variable is declared.
	 * @return A VariableDeclaration object representing the variable declaration.
	 * @throws AssertionError
	 *             if the type context is not supported or does not contain an intType.
	 */
	public static VariableDeclaration constructVarDecFromTypeContext(final ParserRuleContext typeContext,
			final String identifier, final LlvmirLocation location) throws AssertionError {
		final LLVMIRParser.IntTypeContext intType;

		if (typeContext instanceof LLVMIRParser.ConcreteTypeContext) {
			intType = ((LLVMIRParser.ConcreteTypeContext) typeContext).intType();
		} else if (typeContext instanceof LLVMIRParser.TypeContext) {
			intType = ((LLVMIRParser.TypeContext) typeContext).intType();
		} else {
			throw new AssertionError("Unsupported type context for variable declaration:");
		}

		if (intType == null) {
			throw new AssertionError("Type context does not contain an intType:");
		}

		final String typeString = intType.getText();
		final String typeIdentifier = typeString.equals("i1") ? "bool" : "int";

		final PrimitiveType type = new PrimitiveType(location, typeIdentifier);
		final VarList varList = new VarList(location, new String[] { unifyIdentifier(identifier) }, type);
		return new VariableDeclaration(location, new Attribute[] {}, new VarList[] { varList });
	}

	/**
	 * Constructs a specification from a given identifier and location.
	 *
	 * This method constructs a ModifiesSpecification that indicates the specified variable is modified in the Boogie
	 * AST.
	 *
	 * @param identifier
	 *            The identifier of the variable to be modified.
	 * @param location
	 *            The location in the source code where this specification is defined.
	 * @return A ModifiesSpecification object representing the modifies specification for the given identifier.
	 */
	public static ModifiesSpecification constructSpecFromIdentifier(final String identifier,
			final LlvmirLocation location) {
		final VariableLHS varLhs = new VariableLHS(location, identifier);
		return new ModifiesSpecification(location, false, new VariableLHS[] { varLhs });
	}

	/**
	 * Constructs an initial procedure with the given parameters.
	 *
	 * This method constructs a Procedure object representing the initial procedure in the Boogie AST, including its
	 * body, variable declarations, statements, and specifications.
	 *
	 * @param location
	 *            The location in the source code where this procedure is defined.
	 * @param identifier
	 *            The identifier for the procedure.
	 * @param varDecls
	 *            The variable declarations for the procedure.
	 * @param stmts
	 *            The statements in the body of the procedure.
	 * @param specs
	 *            The specifications for the procedure.
	 * @return A Procedure object representing the initial procedure.
	 */
	public static Procedure constructInitialProcedure(final LlvmirLocation location, final String identifier,
			final VariableDeclaration[] varDecls, final Statement[] stmts, final Specification[] specs) {
		final Body body = new Body(location, varDecls, stmts);
		return new Procedure(location, new Attribute[] {}, identifier, new String[] {}, new VarList[] {},
				new VarList[] {}, specs, body);
	}

	/**
	 * Retrieves a Procedure object from the list of declarations based on the given identifier.
	 *
	 * @param identifier
	 *            The identifier of the procedure to retrieve.
	 * @param declarations
	 *            The list of declarations to search.
	 * @return The Procedure object corresponding to the identifier.
	 * @throws AssertionError
	 *             if no procedure with the given identifier is found.
	 */
	public static Procedure getProcedureFromDeclarations(final String identifier,
			final ArrayList<Declaration> declarations) throws AssertionError {
		return declarations.stream().filter(dec -> dec instanceof Procedure).map(dec -> (Procedure) dec)
				.filter(proc -> proc.getIdentifier().equals(identifier)).findFirst()
				.orElseThrow(() -> new AssertionError("Procedure with identifier '" + identifier + "' not found."));
	}

	/**
	 * Checks if a procedure with the same signature already exists in the list of declarations.
	 *
	 * This method compares the identifier, input parameters, and output parameters of the given procedure with those in
	 * the list of declarations to determine if an identical procedure is already present.
	 *
	 * @param procedure
	 *            The procedure to check for duplicates.
	 * @param declarations
	 *            The list of declarations to search.
	 * @return true if an identical procedure is found, false otherwise.
	 */
	public static boolean procedureAlreadyPresent(final Procedure procedure,
			final ArrayList<Declaration> declarations) {
		return declarations.stream().filter(dec -> dec instanceof Procedure).map(dec -> (Procedure) dec)
				.anyMatch(proc -> {
					if (!proc.getIdentifier().equals(procedure.getIdentifier())) {
						return false;
					}
					if (proc.getInParams().length != procedure.getInParams().length) {
						return false;
					}
					if (proc.getInParams().length != procedure.getInParams().length) {
						return false;
					}
					return parametersMatch(proc.getInParams(), procedure.getInParams())
							&& parametersMatch(proc.getOutParams(), procedure.getOutParams());
				});
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
	public static FunctionDeclaration contructRemainderFunction(final LlvmirLocation location) {
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
	 * This method searches the list of declarations for a TypeDeclaration with an identifier matching the format
	 * "i{bitLength}Pair".
	 *
	 * @param bitLength
	 *            The bit length to check for.
	 * @param declarations
	 *            The list of declarations to search.
	 * @return true if a matching TypeDeclaration exists, false otherwise.
	 */
	public static boolean bitLengthPairExists(final int bitLength, final ArrayList<Declaration> declarations) {
		final Optional<TypeDeclaration> typeDec =
				declarations.stream().filter(dec -> dec instanceof TypeDeclaration).map(dec -> (TypeDeclaration) dec)
						.filter(typeDecl -> typeDecl.getIdentifier().equals("i" + bitLength + "Pair")).findFirst();
		return typeDec.isPresent();
	}

	/**
	 * Constructs the declaration of the struct type that holds the result of an LLVM operation with overflow.
	 *
	 * The struct type "i{bitLength}Pair" has the field e0 of type int for the result and the field e1 of type bool for
	 * the overflow flag.
	 *
	 * @param bitLength
	 *            The bit length of the integer type of the operation.
	 * @param location
	 *            The location in the source code where this type is needed.
	 * @return A TypeDeclaration representing the struct type for the given bit length.
	 */
	public static TypeDeclaration constructBitLengthPairTypeDeclaration(final int bitLength,
			final LlvmirLocation location) {
		final ArrayList<VarList> varLists = new ArrayList<>();
		final PrimitiveType intType = new PrimitiveType(location, "int");
		final VarList varList1 = new VarList(location, new String[] { "e0" }, intType);
		varLists.add(varList1);
		final PrimitiveType boolType = new PrimitiveType(location, "bool");
		final VarList varList2 = new VarList(location, new String[] { "e1" }, boolType);
		varLists.add(varList2);
		final StructType structType = new StructType(location, varLists.toArray(VarList[]::new));
		return new TypeDeclaration(location, new Attribute[] {}, true, "i" + bitLength + "Pair", new String[] {},
				structType);
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

	/**
	 * Checks if the identifiers and types of the parameters of an existing procedure match those of another procedure.
	 *
	 * @param existing
	 *            The parameters of the procedure in the list of declarations.
	 * @param other
	 *            The parameters of the procedure to check for duplicates.
	 * @return true if all identifiers and types match, false otherwise.
	 */
	private static boolean parametersMatch(final VarList[] existing, final VarList[] other) {
		for (int i = 0; i < existing.length; i++) {
			for (int j = 0; j < existing[i].getIdentifiers().length; j++) {
				if (!existing[i].getIdentifiers()[j].equals(other[i].getIdentifiers()[j])) {
					return false;
				}
				if (!existing[i].getType().equals(other[i].getType())) {
					return false;
				}
			}
		}
		return true;
	}
}