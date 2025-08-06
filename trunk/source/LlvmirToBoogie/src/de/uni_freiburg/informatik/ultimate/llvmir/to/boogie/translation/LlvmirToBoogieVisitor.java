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
package de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.tree.ParseTree;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Spec;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LLVMIRBaseVisitor;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LLVMIRParser;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LlvmirLocation;

public class LlvmirToBoogieVisitor extends LLVMIRBaseVisitor<FunctionBody> {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private Unit mResult;
	private final String mFilename;
	private LlvmirLocation mLocation;
	private final String mLabelIdentifier = "#label";
	private final static String mUndefIdentifier = "#undef";

	private final ArrayList<Declaration> mDeclarations = new ArrayList<>();

	public LlvmirToBoogieVisitor(final IUltimateServiceProvider services, final ILogger logger, final String filename) {
		assert services != null;
		mServices = services;
		mLogger = logger;
		mFilename = filename;
		mLocation = null;
		mLogger.info("Starting translation of LLVM IR to Boogie for file: " + mFilename);
	}

	public Unit getResult() {
		return mResult;
	}

	/**
	 * Unifies the identifier by ensuring it starts with a # character.
	 *
	 * This method is used to standardize the identifiers in the Boogie AST, as they are expected to start with #.
	 *
	 * @param identifier The original identifier from the LLVM IR parse tree.
	 * @return The unified identifier starting with #, or the original identifier if it is null or empty.
	 */
	private static String unifyIdentifier(final String identifier) {
		if (identifier == null || identifier.isEmpty()) {
			return identifier;
		}
		String result = identifier;
		result = result.replace(":", "");
		final char firstChar = result.charAt(0);
		if (Character.isLetterOrDigit(firstChar)) {
			return "#" + result;
		}
		return "#" + result.substring(1);
	}

	/**
	 * Creates the initial declarations for the Boogie translation, specifically an #init procedure and a ULTIMATE.start
	 * procedure that calls #init and #main.
	 *
	 * The #init procedure is empty, while the ULTIMATE.start procedure initializes the program by calling both #init
	 * and #main.
	 */
	private void createInitialDeclarations() {
		final Body initBody = new Body(mLocation, new VariableDeclaration[] {}, new Statement[] {});
		final Procedure initProcedure = new Procedure(mLocation, new Attribute[] {}, "#init", new String[] {},
				new VarList[] {}, new VarList[] {}, new Specification[] {}, initBody);
		mDeclarations.add(initProcedure);
		final CallStatement initCall = new CallStatement(mLocation, false, new VariableLHS[] {}, "#init",
				new Expression[] {});

		final PrimitiveType intType = new PrimitiveType(mLocation, "int");
		final VarList varList = new VarList(mLocation, new String[] { "#tmp" }, intType);
		final VariableDeclaration varDecl = new VariableDeclaration(mLocation, new Attribute[] {},
				new VarList[] { varList });
		final VariableLHS varLhs = new VariableLHS(mLocation, "#tmp");
		final CallStatement mainCall = new CallStatement(mLocation, false, new VariableLHS[] { varLhs }, "#main",
				new Expression[] {});
		final Body startBody = new Body(mLocation, new VariableDeclaration[] { varDecl },
				new Statement[] { initCall, mainCall });
		final Procedure startProcedure = new Procedure(mLocation, new Attribute[] {}, "ULTIMATE.start", new String[] {},
				new VarList[] {}, new VarList[] {}, new Specification[] {}, startBody);
		mDeclarations.add(startProcedure);
	}

	/**
	 * Retrieves the #init procedure from the list of declarations.
	 *
	 * @return The #init procedure.
	 * @throws IllegalStateException if no #init procedure is found.
	 */
	private Procedure getInitProcedure() throws IllegalStateException {
		return (Procedure) mDeclarations.stream()
				.filter(decl -> decl instanceof Procedure && ((Procedure) decl).getIdentifier().equals("#init"))
				.findFirst().orElseThrow(() -> new IllegalStateException("No #init declaration found"));
	}

	/**
	 * Retrieves the ULTIMATE.start procedure from the list of declarations.
	 *
	 * @return The ULTIMATE.start procedure.
	 * @throws IllegalStateException if no ULTIMATE.start procedure is found.
	 */
	private Procedure getStartProcedure() throws IllegalStateException {
		return (Procedure) mDeclarations.stream().filter(
				decl -> decl instanceof Procedure && ((Procedure) decl).getIdentifier().equals("ULTIMATE.start"))
				.findFirst().orElseThrow(() -> new IllegalStateException("No ULTIMATE.start declaration found"));
	}

	/**
	 * Updates the #init procedure with a new statement and modifies specification.
	 *
	 * This method removes the existing procedure from the declarations, creates a new body with the provided statement
	 * and modifies specification, and then adds the updated procedure back to the declarations.
	 *
	 * @param procedure    The procedure to be updated.
	 * @param stmt         The statement to be added to the procedure body, can be null.
	 * @param modifiesSpec The modifies specification to be added, can be null.
	 * @throws IllegalArgumentException if the procedure is null.
	 */
	private void updateProcedure(final Procedure procedure, final Statement stmt, final Specification modifiesSpec)
			throws IllegalArgumentException {
		if (procedure == null) {
			throw new IllegalArgumentException("Procedure cannot be null");
		}
		mDeclarations.remove(procedure);
		final ArrayList<Statement> newBlock = new ArrayList<>(Arrays.asList(procedure.getBody().getBlock()));
		if (stmt != null) {
			newBlock.add(stmt);
		}
		final ArrayList<Specification> newSpecs = new ArrayList<>(Arrays.asList(procedure.getSpecification()));
		if (modifiesSpec != null) {
			newSpecs.add(modifiesSpec);
		}

		final Body newBody = new Body(procedure.getBody().getLocation(), procedure.getBody().getLocalVars(),
				newBlock.toArray(new Statement[0]));
		final Procedure newProcedure = new Procedure(procedure.getLocation(), procedure.getAttributes(),
				procedure.getIdentifier(), procedure.getTypeParams(), procedure.getInParams(), procedure.getOutParams(),
				newSpecs.toArray(new Specification[0]), newBody);

		mDeclarations.add(newProcedure);
	}

	/**
	 * Creates a variable declaration with a primitive type.
	 *
	 * This method is used to create variable declarations for primitive types like integers, booleans, etc.
	 *
	 * @param type       The type of the variable (e.g., "int", "bool").
	 * @param identifier The identifier for the variable.
	 * @param location   The location in the source code where this variable is declared.
	 * @return A VariableDeclaration object representing the variable declaration.
	 */
	private static VariableDeclaration createVarDecWithPrimType(final String type, final String identifier,
			final LlvmirLocation location) {
		final PrimitiveType primType = new PrimitiveType(location, type);
		final VarList varList = new VarList(location, new String[] { unifyIdentifier(identifier) }, primType);
		final VariableDeclaration varDecl = new VariableDeclaration(location, new Attribute[] {},
				new VarList[] { varList });

		return varDecl;
	}

	/**
	 * Creates a variable declaration with a primitive type based on the provided type string and identifier.
	 *
	 * This method constructs a VariableDeclaration object with the specified type and identifier, ensuring that the
	 * identifier is unified to start with a # character.
	 *
	 * @param typeString The string representation of the type (e.g., "i32").
	 * @param identifier The identifier for the variable.
	 * @param location   The location in the source code where this variable is declared.
	 * @return A VariableDeclaration object representing the variable declaration.
	 */
	private static VariableDeclaration createVarDecFromConcreteType(final LLVMIRParser.ConcreteTypeContext typeContext,
			final String identifier, final FunctionBody body, final LlvmirLocation location) throws AssertionError {
		if (typeContext.intType() != null) {
			final String typeString = typeContext.intType().getText();
			final String typeIdentifier = typeString.equals("i1") ? "bool" : "int";
			if (typeIdentifier.equals("int")) {
				final int bitLength = Integer.parseInt(typeString.substring(1));
				final VariableLHS varLhs = new VariableLHS(location, unifyIdentifier(identifier));
				final HavocStatement havocStmt = new HavocStatement(location, new VariableLHS[] { varLhs });
				body.addFuncBlock(havocStmt);

				final IntegerLiteral zeroLiteral = new IntegerLiteral(location, "0");
				final IdentifierExpression identExpr = new IdentifierExpression(location, unifyIdentifier(identifier));
				final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.COMPGEQ, identExpr,
						zeroLiteral);
				final AssumeStatement assumeStmt = new AssumeStatement(location, new NamedAttribute[] {}, binaryExpr);
				body.addFuncBlock(assumeStmt);

				final IntegerLiteral bitLengthLiteral = new IntegerLiteral(location, Integer.toString(bitLength));
				final BinaryExpression signedExpr = new BinaryExpression(location, Operator.COMPLT, identExpr,
						bitLengthLiteral);
				final AssumeStatement signedAssumeStmt = new AssumeStatement(location, new NamedAttribute[] {},
						signedExpr);
				body.addFuncBlock(signedAssumeStmt);
			}
			final PrimitiveType type = new PrimitiveType(location, typeIdentifier);
			final VarList varList = new VarList(location, new String[] { unifyIdentifier(identifier) }, type);
			return new VariableDeclaration(location, new Attribute[] {}, new VarList[] { varList });
		}
		throw new AssertionError("Unsupported concrete type for variable declaration: " + typeContext.getText());
	}

	/**
	 * Creates a variable declaration from a type context and identifier.
	 *
	 * This method constructs a VariableDeclaration object based on the provided type context and identifier, ensuring
	 * that the identifier is unified to start with a # character.
	 *
	 * @param typeContext The type context from the LLVM IR parse tree.
	 * @param identifier  The identifier for the variable.
	 * @param body        The function body to which this variable declaration will be added.
	 * @param location    The location in the source code where this variable is declared.
	 * @return A VariableDeclaration object representing the variable declaration.
	 * @throws AssertionError if the type context is not supported.
	 */
	private static VariableDeclaration createVarDecFromType(final LLVMIRParser.TypeContext typeContext,
			final String identifier, final FunctionBody body, final LlvmirLocation location) throws AssertionError {
		if (typeContext.intType() != null) {
			final String typeString = typeContext.intType().getText();
			final String typeIdentifier = typeString.equals("i1") ? "bool" : "int";
			if (typeIdentifier.equals("int")) {
				final int bitLength = Integer.parseInt(typeString.substring(1));
				final VariableLHS varLhs = new VariableLHS(location, unifyIdentifier(identifier));
				final HavocStatement havocStmt = new HavocStatement(location, new VariableLHS[] { varLhs });
				body.addFuncBlock(havocStmt);

				final IntegerLiteral zeroLiteral = new IntegerLiteral(location, "0");
				final IdentifierExpression identExpr = new IdentifierExpression(location, unifyIdentifier(identifier));
				final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.COMPGEQ, identExpr,
						zeroLiteral);
				final AssumeStatement assumeStmt = new AssumeStatement(location, new NamedAttribute[] {}, binaryExpr);
				body.addFuncBlock(assumeStmt);

				final IntegerLiteral bitLengthLiteral = new IntegerLiteral(location, Integer.toString(bitLength));
				final BinaryExpression signedExpr = new BinaryExpression(location, Operator.COMPLT, identExpr,
						bitLengthLiteral);
				final AssumeStatement signedAssumeStmt = new AssumeStatement(location, new NamedAttribute[] {},
						signedExpr);
				body.addFuncBlock(signedAssumeStmt);
			}
			final PrimitiveType type = new PrimitiveType(location, typeIdentifier);
			final VarList varList = new VarList(location, new String[] { unifyIdentifier(identifier) }, type);
			return new VariableDeclaration(location, new Attribute[] {}, new VarList[] { varList });
		}
		throw new AssertionError("Unsupported concrete type for variable declaration: " + typeContext.getText());
	}

	/**
	 * Converts a value context from the LLVM IR parse tree into a Boogie expression.
	 *
	 * This method handles both local identifiers and constant values, converting them into the appropriate Boogie
	 * expressions (IdentifierExpression or IntegerLiteral).
	 *
	 * @param valueContext The value context from the LLVM IR parse tree.
	 * @param location     The location in the source code where this value is used.
	 * @return An Expression object representing the value.
	 * @throws AssertionError if the value type is not supported.
	 */
	private static Expression getExpressionFromConcreteTypeValue(final LLVMIRParser.ValueContext valueContext,
			final LLVMIRParser.ConcreteTypeContext typeContext, final LlvmirLocation location) throws AssertionError {
		if (valueContext.LocalIdent() != null) {
			final String leftOperandName = valueContext.LocalIdent().getText();
			return new IdentifierExpression(location, unifyIdentifier(leftOperandName));
		} else if (valueContext.constant() != null) {
			if (valueContext.constant().intConst() != null) {
				final int bitLength = Integer.parseInt(typeContext.intType().getText().substring(1));
				final int constValue = Integer.parseInt(valueContext.constant().intConst().getText());
				final int modulus = 1 << bitLength;
				final int modValue = ((constValue % modulus) + modulus) % modulus;
				return new IntegerLiteral(location, Integer.toString(modValue));
			} else if (valueContext.constant().boolConst() != null) {
				return new BooleanLiteral(location, valueContext.constant().boolConst().getText().equals("true"));
			} else if (valueContext.constant().undefConst() != null) {
				return new IdentifierExpression(location, mUndefIdentifier);
			}
			// TODO: Support for other constant operand types
			throw new AssertionError(
					"The support for iCmp instructions with constant operands other than integers and booleans is not implemented yet.");
		} else {
			// TODO: Support for other left operand types
			throw new AssertionError(
					"The support for iCmp instructions with operands other than constants or local identifiers is not implemented yet.");
		}
	}

	/**
	 * Converts a value context from the LLVM IR parse tree into an expression for increment operations.
	 *
	 * This method handles both local identifiers and constant values, converting them into the appropriate Boogie
	 * expressions (IdentifierExpression or IntegerLiteral) for increment operations.
	 *
	 * @param valueContext The value context from the LLVM IR parse tree.
	 * @param typeContext  The concrete type context for the value.
	 * @param location     The location in the source code where this value is used.
	 * @return An Expression object representing the increment value.
	 * @throws AssertionError if the value type is not supported.
	 */
	private static Expression getExpressionFromTypeValue(final LLVMIRParser.ValueContext valueContext,
			final LLVMIRParser.TypeContext typeContext, final LlvmirLocation location) throws AssertionError {
		if (valueContext.LocalIdent() != null) {
			final String leftOperandName = valueContext.LocalIdent().getText();
			return new IdentifierExpression(location, unifyIdentifier(leftOperandName));
		} else if (valueContext.constant() != null) {
			if (valueContext.constant().intConst() != null) {
				final int bitLength = Integer.parseInt(typeContext.intType().getText().substring(1));
				final int constValue = Integer.parseInt(valueContext.constant().intConst().getText());
				final int modulus = 1 << bitLength;
				final int modValue = ((constValue % modulus) + modulus) % modulus;
				return new IntegerLiteral(location, Integer.toString(modValue));
			} else if (valueContext.constant().boolConst() != null) {
				return new BooleanLiteral(location, valueContext.constant().boolConst().getText().equals("true"));
			} else if (valueContext.constant().undefConst() != null) {
				return new IdentifierExpression(location, mUndefIdentifier);
			}
			// TODO: Support for other constant operand types
			throw new AssertionError(
					"The support for iCmp instructions with constant operands other than integers and booleans is not implemented yet.");
		} else {
			// TODO: Support for other left operand types
			throw new AssertionError(
					"The support for iCmp instructions with operands other than constants or local identifiers is not implemented yet.");
		}
	}

	/**
	 * Converts a constant context from the LLVM IR parse tree into a Boogie expression.
	 *
	 * This method handles integer constants, boolean constants, and undefined constants, converting them into the
	 * appropriate Boogie expressions (IntegerLiteral, BooleanLiteral, or IdentifierExpression).
	 *
	 * @param constantContext The constant context from the LLVM IR parse tree.
	 * @param typeContext     The concrete type context for the constant.
	 * @param location        The location in the source code where this constant is used.
	 * @return An Expression object representing the constant.
	 * @throws AssertionError if the constant type is not supported.
	 */
	private static Expression getExpressionFromTypeConstant(final LLVMIRParser.ConstantContext constantContext,
			final LLVMIRParser.TypeContext typeContext, final LlvmirLocation location) throws AssertionError {
		if (constantContext.intConst() != null) {
			final int bitLength = Integer.parseInt(typeContext.intType().getText().substring(1));
			final int constValue = Integer.parseInt(constantContext.intConst().getText());
			final int modulus = 1 << bitLength;
			final int modValue = ((constValue % modulus) + modulus) % modulus;
			return new IntegerLiteral(location, Integer.toString(modValue));
		} else if (constantContext.boolConst() != null) {
			return new BooleanLiteral(location, constantContext.boolConst().getText().equals("true"));
		} else if (constantContext.undefConst() != null) {
			return new IdentifierExpression(location, mUndefIdentifier);
		}
		// TODO: Support for other constant operand types
		throw new AssertionError(
				"The support for iCmp instructions with constant operands other than integers and booleans is not implemented yet.");
	}

	/**
	 * Retrieves the index of a label from the function body based on the provided identifier.
	 *
	 * This method traverses the parent hierarchy of the given context to find the function body and then searches for
	 * the label with the specified identifier within that function body.
	 *
	 * @param ctx           The context from which to start searching for the function body.
	 * @param incIdentifier The identifier of the label to find.
	 * @return The index of the label in the function body.
	 * @throws IllegalArgumentException if the context or identifier is null or empty, or if no label is found.
	 */
	private static int getLabelIndexFromFuncBody(final ParserRuleContext ctx, final String incIdentifier)
			throws IllegalArgumentException {
		if (ctx == null || incIdentifier == null || incIdentifier.isEmpty()) {
			throw new IllegalArgumentException("Context and identifier must not be null or empty");
		}
		LLVMIRParser.FuncBodyContext funcBodyCtx = null;
		ParserRuleContext tmpCtx = ctx;
		while (funcBodyCtx == null) {
			if (tmpCtx.getParent() instanceof LLVMIRParser.FuncBodyContext) {
				funcBodyCtx = (LLVMIRParser.FuncBodyContext) tmpCtx.getParent();
			} else if (tmpCtx.getParent() != null) {
				tmpCtx = tmpCtx.getParent();
			} else {
				throw new IllegalArgumentException("No FuncBodyContext found in the parent hierarchy");
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
			throw new IllegalArgumentException("No label found for identifier: " + incIdentifier);
		}
		return labelIndex;
	}

	/**
	 * Creates an assignment statement to assign a label index to the label variable.
	 *
	 * This method constructs an assignment statement that assigns the specified label index to the label variable
	 * identified by `mLabelIdentifier`.
	 *
	 * @param location   The location in the source code where this assignment occurs.
	 * @param labelIndex The index of the label to be assigned.
	 * @return An AssignmentStatement object representing the assignment.
	 */
	private AssignmentStatement createLabelAssignment(final LlvmirLocation location, final int labelIndex) {
		final IntegerLiteral labelIndexLiteral = new IntegerLiteral(location, Integer.toString(labelIndex));
		final VariableLHS labelVar = new VariableLHS(location, mLabelIdentifier);
		return new AssignmentStatement(location, new LeftHandSide[] { labelVar },
				new Expression[] { labelIndexLiteral });
	}

	/**
	 * Converts a string representation of a comparison operator to its corresponding Boogie operator.
	 *
	 * This method maps the LLVM IR comparison operators (like "eq", "ne", "sle", etc.) to their Boogie equivalents
	 * (like COMPEQ, COMPNEQ, COMPLEQ, etc.).
	 *
	 * @param operatorValue The string representation of the comparison operator.
	 * @return The corresponding Boogie Operator.
	 * @throws AssertionError if the operator is not supported.
	 */
	private static Operator getCompOperatorFromOperatorValue(final String operatorValue) {
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
	 * Creates a havoc statement for arithmetic or logic instructions.
	 *
	 * This method generates a havoc statement for arithmetic or logic instructions based on the type of the
	 * instruction. It creates a local variable with either "bool" or "int" type and adds a havoc statement to the
	 * function body.
	 *
	 * @param body       The function body to which the havoc statement will be added.
	 * @param typeValue  The type value context from the LLVM IR parse tree.
	 * @param location   The location in the source code where this instruction is defined.
	 * @param identifier The identifier for the local variable to be created.
	 */
	private static void createHavocStatementFromTypeValue(final FunctionBody body,
			final LLVMIRParser.TypeValueContext typeValue, final LlvmirLocation location, final String identifier) {
		final LLVMIRParser.ConcreteTypeContext tpyeContext = typeValue.firstClassType().concreteType();
		body.addFuncLocalVar(createVarDecFromConcreteType(tpyeContext, identifier, body, location));
		final VariableLHS varLhs = new VariableLHS(location, identifier);
		final HavocStatement havocStmt = new HavocStatement(location, new VariableLHS[] { varLhs });
		body.addFuncBlock(havocStmt);
	}

	/**
	 * Creates an expression that converts an unsigned integer to a signed integer based on the specified bit length.
	 *
	 * This method checks if the given expression is greater than or equal to the maximum value for the specified bit
	 * length. If it is, it subtracts the maximum value from the expression to convert it to a signed representation.
	 *
	 * @param expr      The expression to be converted.
	 * @param bitLength The bit length for the conversion.
	 * @param location  The location in the source code where this conversion occurs.
	 * @return An IfThenElseExpression representing the signed conversion.
	 */
	private static Expression createSignedExpression(final Expression expr, final int bitLength,
			final LlvmirLocation location) {
		final IntegerLiteral condLiteral = new IntegerLiteral(location, Integer.toString(1 << bitLength - 1));
		final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.COMPGEQ, expr, condLiteral);
		final IntegerLiteral bitLengthLiteral = new IntegerLiteral(location, Integer.toString(1 << bitLength));
		final BinaryExpression thenExpr = new BinaryExpression(location, Operator.ARITHMINUS, expr, bitLengthLiteral);
		final IfThenElseExpression ifThenElseExpr = new IfThenElseExpression(location, binaryExpr, thenExpr, expr);
		return ifThenElseExpr;
	}

	/**
	 * Handles the visit event for a compilation unit in the LLVM IR parse tree.
	 *
	 * This method initializes the location and creates the initial declarations for the Boogie translation. It then
	 * visits all children of the compilation unit context to process function definitions and global variable
	 * definitions.
	 *
	 * @param ctx The parse tree context for the compilation unit.
	 * @return null, as this method does not return any value.
	 */
	@Override
	public FunctionBody visitCompilationUnit(final LLVMIRParser.CompilationUnitContext ctx) {
		mLocation = new LlvmirLocation(mFilename, ctx.getStart().getLine(), ctx.getStop().getLine(),
				ctx.getStart().getCharPositionInLine(), ctx.getStop().getCharPositionInLine());
		createInitialDeclarations();

		visitChildren(ctx);

		mResult = new Unit(mLocation, mDeclarations.toArray(Declaration[]::new));
		return null;
	}

	/**
	 * Handles the visit event for a function definition in the LLVM IR parse tree.
	 *
	 * This method translates the parsed LLVM IR function into a Boogie procedure, including its body, parameters, and
	 * return type. Currently, only `void` and integer return types are supported.
	 *
	 * @param ctx The parse tree context for the function definition.
	 * @throws AssertionError if the return type is not supported.
	 */
	@Override
	public FunctionBody visitFuncDef(final LLVMIRParser.FuncDefContext ctx) throws AssertionError {
		final FunctionBody body = new FunctionBody();

		body.addFuncLocalVar(createVarDecWithPrimType("int", mUndefIdentifier, mLocation));
		final VariableLHS undefVar = new VariableLHS(mLocation, mUndefIdentifier);
		final HavocStatement havocStmt = new HavocStatement(mLocation, new VariableLHS[] { undefVar });
		body.addFuncBlock(havocStmt);

		for (final ParseTree child : ctx.children) {
			final FunctionBody childBody = child.accept(this);
			if (childBody != null) {
				body.merge(childBody);
			}
		}

		body.addFuncLocalVar(createVarDecWithPrimType("int", mLabelIdentifier, mLocation));
		final String funcName = unifyIdentifier(ctx.funcHeader().GlobalIdent().getText());
		final LLVMIRParser.TypeContext returnType = ctx.funcHeader().type();

		final LlvmirLocation location = new LlvmirLocation(mFilename, ctx.getStart().getLine(), ctx.getStop().getLine(),
				ctx.getStart().getCharPositionInLine(), ctx.getStop().getCharPositionInLine());

		final Body funcBody = new Body(location, body.getFuncLocalVars().toArray(VariableDeclaration[]::new),
				body.getFuncBlock().toArray(Statement[]::new));
		final ArrayList<Attribute> attributes = new ArrayList<>();
		final ArrayList<String> typeParams = new ArrayList<>();
		final ArrayList<VarList> inParams = new ArrayList<>();
		final ArrayList<VarList> outParams = new ArrayList<>();
		final ArrayList<Specification> spec = new ArrayList<>();

		for (final LLVMIRParser.ParamContext param : ctx.funcHeader().params().param()) {
			PrimitiveType paramType = null;
			if (param.type().intType().getText().equals("i1")) {
				paramType = new PrimitiveType(location, "bool");
			} else {
				paramType = new PrimitiveType(location, "int");
			}
			final VarList varList = new VarList(location,
					new String[] { unifyIdentifier(param.LocalIdent().getText()) }, paramType);
			inParams.add(varList);
		}

		if (returnType.getText().equals("void")) {
			// Nothing gets returned
		} else if (returnType.intType() != null) {
			PrimitiveType returnTypePrim = null;
			if (returnType.intType().getText().equals("i1")) {
				returnTypePrim = new PrimitiveType(location, "bool");
			} else {
				returnTypePrim = new PrimitiveType(location, "int");
			}
			final VarList retVarList = new VarList(location, new String[] { "ret" }, returnTypePrim);
			outParams.add(retVarList);
		} else {
			// TODO: Support for other types
			throw new AssertionError(
					"The support for return types other than void and integers is not implemented yet.");
		}

		final Procedure procedure = new Procedure(location, attributes.toArray(Attribute[]::new), funcName,
				typeParams.toArray(String[]::new), inParams.toArray(VarList[]::new), outParams.toArray(VarList[]::new),
				spec.toArray(Specification[]::new), funcBody);
		mDeclarations.add(procedure);

		return null;
	}

	/**
	 * Handles the visit event for a function body in the LLVM IR parse tree.
	 *
	 * This method processes the children of the function body context and merges their results into a single
	 * FunctionBody object.
	 *
	 * @param ctx The parse tree context for the function body.
	 * @return A FunctionBody object containing the merged results of the children.
	 */
	@Override
	public FunctionBody visitFuncBody(final LLVMIRParser.FuncBodyContext ctx) {
		final FunctionBody body = new FunctionBody();
		final List<LLVMIRParser.BasicBlockContext> basicBlocks = ctx.basicBlock();
		for (final LLVMIRParser.BasicBlockContext childCtx : ctx.basicBlock()) {
			final FunctionBody childBody = visit(childCtx);
			if (childBody != null) {
				body.merge(childBody);
			}
		}
		return body;
	}

	@Override
	public FunctionBody visitBasicBlock(final LLVMIRParser.BasicBlockContext ctx) {
		final LlvmirLocation location = new LlvmirLocation(mFilename, ctx.getStart().getLine(), ctx.getStop().getLine(),
				ctx.getStart().getCharPositionInLine(), ctx.getStop().getCharPositionInLine());
		final FunctionBody body = new FunctionBody();

		final LLVMIRParser.FuncBodyContext funcBodyCtx = (LLVMIRParser.FuncBodyContext) ctx.getParent();
		final List<LLVMIRParser.BasicBlockContext> blocks = funcBodyCtx.basicBlock();
		final int index = blocks.indexOf(ctx);

		body.setCurrentLabelIndex(index);

		final String labelName = unifyIdentifier(ctx.LabelIdent().getText());
		final Label label = new Label(location, labelName, new NamedAttribute[] {});
		body.addLabel(labelName);
		body.addFuncBlock(label);

		for (final ParseTree child : ctx.children) {
			if (child.getChild(0) instanceof LLVMIRParser.CondBrTermContext
					|| child.getChild(0) instanceof LLVMIRParser.BrTermContext) {
				body.addFuncBlock(createLabelAssignment(location, body.getCurrentLabelIndex()));
			}
			final FunctionBody childBody = child.accept(this);
			if (childBody != null) {
				body.merge(childBody);
			}
		}

		if (!(index == blocks.size() - 1)) {
			body.addFuncBlock(createLabelAssignment(location, body.getCurrentLabelIndex()));
		}

		return body;
	}

	/**
	 * Handles the visit event for a return terminator in the LLVM IR parse tree.
	 *
	 * Currently, it only supports integer return types.
	 *
	 * @param ctx The parse tree context for the return terminator.
	 * @throws AssertionError if the return type is not supported.
	 */
	@Override
	public FunctionBody visitRetTerm(final LLVMIRParser.RetTermContext ctx) {
		final FunctionBody body = new FunctionBody();

		final LlvmirLocation location = new LlvmirLocation(mFilename, ctx.getStart().getLine(), ctx.getStop().getLine(),
				ctx.getStart().getCharPositionInLine(), ctx.getStop().getCharPositionInLine());

		if (ctx.value() == null) {
			// If there is no value, we assume a void return type
			final ReturnStatement returnStmt = new ReturnStatement(location);
			body.addFuncBlock(returnStmt);
		} else {
			final LLVMIRParser.ConcreteTypeContext returnType = ctx.concreteType();
			if (returnType.intType() != null) {
				final VariableLHS returnVar = new VariableLHS(location, "ret");
				final AssignmentStatement assignmentStmt = new AssignmentStatement(location,
						new LeftHandSide[] { returnVar },
						new Expression[] { getExpressionFromConcreteTypeValue(ctx.value(), returnType, location) });
				final ReturnStatement returnStmt = new ReturnStatement(location);
				body.addFuncBlocks(Arrays.asList(assignmentStmt, returnStmt));
			} else {
				// TODO: Support for other types
				throw new AssertionError("The support for return types other than integers is not implemented yet.");
			}
		}
		return body;

	}

	/**
	 * Handles the visit event for a global variable definition in the LLVM IR parse tree.
	 *
	 * This method translates the global variable definition into a Boogie variable declaration and initializes it based
	 * on the type of the constant value.
	 *
	 * @param ctx The parse tree context for the global variable definition.
	 * @return A FunctionBody object containing the variable declaration and initialization statements.
	 * @throws AssertionError if the type is not supported.
	 */
	@Override
	public FunctionBody visitGlobalDef(final LLVMIRParser.GlobalDefContext ctx) throws AssertionError {
		final FunctionBody body = new FunctionBody();
		final LLVMIRParser.TypeContext type = ctx.type();
		final String identifier = unifyIdentifier(ctx.GlobalIdent().getText());
		final LlvmirLocation location = new LlvmirLocation(mFilename, ctx.getStart().getLine(), ctx.getStop().getLine(),
				ctx.getStart().getCharPositionInLine(), ctx.getStop().getCharPositionInLine());

		if (type.intType() != null) {
			mDeclarations.add(createVarDecWithPrimType("int", identifier, location));
			final String typeString = type.intType().getText() == "i1" ? "bool" : "int";
			if (typeString.equals("int")) {
				final int bitLength = Integer.parseInt(type.intType().getText().substring(1));
				final VariableLHS variableLhs = new VariableLHS(location, identifier);
				final HavocStatement havocStmt = new HavocStatement(location, new VariableLHS[] { variableLhs });
				final Specification havocSpec = new ModifiesSpecification(mLocation, false,
						new VariableLHS[] { variableLhs });
				updateProcedure(getInitProcedure(), havocStmt, havocSpec);
				updateProcedure(getStartProcedure(), null, havocSpec);

				final IntegerLiteral intLit = new IntegerLiteral(location, Integer.toString(0));
				final IdentifierExpression identifierExpr = new IdentifierExpression(location, identifier);
				final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.COMPEQ, identifierExpr,
						intLit);
				final AssumeStatement assumeStmt = new AssumeStatement(location, new NamedAttribute[] {}, binaryExpr);
				final Specification assumeSpec = new ModifiesSpecification(mLocation, false,
						new VariableLHS[] { variableLhs });
				updateProcedure(getInitProcedure(), assumeStmt, assumeSpec);
				updateProcedure(getStartProcedure(), null, assumeSpec);

				final IntegerLiteral rightValue = new IntegerLiteral(location, Integer.toString(1 << bitLength));
				final IdentifierExpression leftExpr = new IdentifierExpression(location, identifier);
				final BinaryExpression binaryExpr2 = new BinaryExpression(location, Operator.COMPLT, leftExpr,
						rightValue);
				final AssumeStatement assumeStmt2 = new AssumeStatement(location, new NamedAttribute[] {}, binaryExpr2);
				final Specification assumeSpec2 = new ModifiesSpecification(mLocation, false,
						new VariableLHS[] { variableLhs });
				updateProcedure(getInitProcedure(), assumeStmt2, assumeSpec2);
				updateProcedure(getStartProcedure(), null, assumeSpec2);
			}
			final VariableLHS varLhs = new VariableLHS(location, identifier);
			final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
					new Expression[] { getExpressionFromTypeConstant(ctx.constant(), type, location) });
			final Specification modifiesSpec = new ModifiesSpecification(mLocation, false,
					new VariableLHS[] { varLhs });
			updateProcedure(getInitProcedure(), assignment, modifiesSpec);
			updateProcedure(getStartProcedure(), null, modifiesSpec);

			body.addFuncLocalVar(createVarDecWithPrimType(typeString, identifier, location));
		} else {
			// TODO: Support for other types
			throw new AssertionError("The support for types other than integers is not implemented yet.");
		}

		return body;
	}

	/**
	 * Handles the visit event for a local variable definition in the LLVM IR parse tree.
	 *
	 * This method translates the local variable definition into a Boogie variable declaration and initializes it based
	 * on the type of instruction.
	 *
	 * @param ctx The parse tree context for the local variable definition.
	 * @throws AssertionError if the instruction type is not supported.
	 */
	@Override
	public FunctionBody visitLocalDefInst(final LLVMIRParser.LocalDefInstContext ctx) {
		final FunctionBody body = new FunctionBody();
		final String identifier = unifyIdentifier(ctx.LocalIdent().getText());
		final LLVMIRParser.ValueInstructionContext instructionType = ctx.valueInstruction();
		final LlvmirLocation location = new LlvmirLocation(mFilename, ctx.getStart().getLine(), ctx.getStop().getLine(),
				ctx.getStart().getCharPositionInLine(), ctx.getStop().getCharPositionInLine());

		if (instructionType.loadInst() != null) {
			final LLVMIRParser.TypeContext variableType = instructionType.loadInst().type();
			if (variableType.intType() != null) {
				body.addFuncLocalVar(createVarDecFromType(variableType, identifier, body, location));
				final VariableLHS varLhs = new VariableLHS(location, identifier);

				String loadVarIdentifier = null;
				if (instructionType.loadInst().typeValue().value().LocalIdent() != null) {
					loadVarIdentifier = unifyIdentifier(
							instructionType.loadInst().typeValue().value().LocalIdent().getText());
				} else if (instructionType.loadInst().typeValue().value().constant() != null) {
					loadVarIdentifier = instructionType.loadInst().typeValue().value().constant().GlobalIdent()
							.getText();
				} else {
					throw new AssertionError("Something went wrong while parsing the load instruction:");
				}

				final IdentifierExpression loadVarExpr = new IdentifierExpression(location,
						unifyIdentifier(loadVarIdentifier));
				final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
						new Expression[] { loadVarExpr });
				body.addFuncBlock(assignment);
				// TODO
			} else {
				// TODO: Support for other types
				throw new AssertionError(
						"The support for types other than integers in load instructions is not implemented yet.");
			}
		} else if (instructionType.iCmpInst() != null) {
			body.addFuncLocalVar(createVarDecWithPrimType("bool", identifier, location));
			final LLVMIRParser.ConcreteTypeContext typeContext = instructionType.iCmpInst().typeValue().firstClassType()
					.concreteType();

			Expression leftExpr = null;
			Expression rightExpr = null;
			final Operator operator = getCompOperatorFromOperatorValue(instructionType.iCmpInst().iPred().getText());

			final LLVMIRParser.ValueContext leftValue = instructionType.iCmpInst().typeValue().value();
			leftExpr = getExpressionFromConcreteTypeValue(leftValue, typeContext, location);

			final LLVMIRParser.ValueContext rightValue = instructionType.iCmpInst().value();
			rightExpr = getExpressionFromConcreteTypeValue(rightValue, typeContext, location);

			if (typeContext.intType() != null && !typeContext.intType().getText().equals("i1")) {
				final int bitLength = Integer.parseInt(typeContext.intType().getText().substring(1));
				if (operator == Operator.COMPLEQ || operator == Operator.COMPLT || operator == Operator.COMPGEQ
						|| operator == Operator.COMPGT) {
					leftExpr = createSignedExpression(leftExpr, bitLength, location);
					rightExpr = createSignedExpression(rightExpr, bitLength, location);
				}
			}

			final VariableLHS varLhs = new VariableLHS(null, identifier);
			final BinaryExpression binaryExpr = new BinaryExpression(location, operator, leftExpr, rightExpr);
			final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
					new Expression[] { binaryExpr });
			body.addFuncBlock(assignment);
		} else if (instructionType.phiInst() != null) {
			final LLVMIRParser.TypeContext typeContext = instructionType.phiInst().type();
			body.addFuncLocalVar(createVarDecFromType(typeContext, identifier, body, location));
			for (final LLVMIRParser.IncContext inc : instructionType.phiInst().inc()) {
				final String incIdentifier = unifyIdentifier(inc.LocalIdent().getText());
				final int labelIndex = getLabelIndexFromFuncBody(ctx, incIdentifier);
				final IdentifierExpression incExpr = new IdentifierExpression(location, mLabelIdentifier);
				final IntegerLiteral labelIndexLiteral = new IntegerLiteral(location, Integer.toString(labelIndex));
				final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.COMPEQ, incExpr,
						labelIndexLiteral);
				final VariableLHS varLhs = new VariableLHS(location, identifier);
				final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
						new Expression[] { getExpressionFromTypeValue(inc.value(), typeContext, location) });
				final IfStatement ifStmt = new IfStatement(location, binaryExpr, new Statement[] { assignment },
						new Statement[] {});
				body.addFuncBlock(ifStmt);
			}
		} else if (instructionType.zExtInst() != null) {
			body.addFuncLocalVar(createVarDecWithPrimType("int", identifier, location));
			final LLVMIRParser.ConcreteTypeContext typeContext = instructionType.zExtInst().typeValue().firstClassType()
					.concreteType();
			if (typeContext.intType().getText().equals("i1")) {
				final IntegerLiteral zeroLiteral = new IntegerLiteral(location, "0");
				final IntegerLiteral oneLiteral = new IntegerLiteral(location, "1");
				final VariableLHS zeroVarLhs = new VariableLHS(location, identifier);
				final VariableLHS oneVarLhs = new VariableLHS(location, identifier);
				final AssignmentStatement elseAssignment = new AssignmentStatement(location,
						new LeftHandSide[] { zeroVarLhs }, new Expression[] { zeroLiteral });
				final AssignmentStatement thenAssignment = new AssignmentStatement(location,
						new LeftHandSide[] { oneVarLhs }, new Expression[] { oneLiteral });
				final IfStatement ifStmt = new IfStatement(
						location, getExpressionFromConcreteTypeValue(instructionType.zExtInst().typeValue().value(),
								typeContext, location),
						new Statement[] { thenAssignment }, new Statement[] { elseAssignment });
				body.addFuncBlock(ifStmt);
			} else {
				final VariableLHS varLhs = new VariableLHS(location, identifier);
				final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
						new Expression[] { getExpressionFromConcreteTypeValue(
								instructionType.zExtInst().typeValue().value(), typeContext, location) });
				body.addFuncBlock(assignment);
			}
		} else if (instructionType.sExtInst() != null) {
			final LLVMIRParser.TypeContext newTypeContext = instructionType.sExtInst().type();
			final LLVMIRParser.ConcreteTypeContext oldTypeContext = instructionType.sExtInst().typeValue()
					.firstClassType().concreteType();
			final String newTypeString = newTypeContext.intType().getText();
			final String oldTypeString = oldTypeContext.intType().getText();
			body.addFuncLocalVar(createVarDecFromType(newTypeContext, identifier, body, location));
			if (oldTypeContext.intType() != null && oldTypeString.equals("i1")) {
				final IntegerLiteral zeroLiteral = new IntegerLiteral(location, "0");
				final IntegerLiteral oneLiteral = new IntegerLiteral(location, "1");
				final VariableLHS zeroVarLhs = new VariableLHS(location, identifier);
				final VariableLHS oneVarLhs = new VariableLHS(location, identifier);
				final AssignmentStatement elseAssignment = new AssignmentStatement(location,
						new LeftHandSide[] { zeroVarLhs }, new Expression[] { zeroLiteral });
				final AssignmentStatement thenAssignment = new AssignmentStatement(location,
						new LeftHandSide[] { oneVarLhs }, new Expression[] { oneLiteral });
				final IfStatement ifStmt = new IfStatement(location,
						getExpressionFromConcreteTypeValue(instructionType.sExtInst().typeValue().value(),
								oldTypeContext, location),
						new Statement[] { thenAssignment }, new Statement[] { elseAssignment });
				body.addFuncBlock(ifStmt);
			} else {
				final VariableLHS varLhs = new VariableLHS(location, identifier);
				final int oldBitLength = Integer.parseInt(oldTypeString.substring(1));
				final int newBitLength = Integer.parseInt(newTypeString.substring(1));
				final IntegerLiteral bitLengthLiteral = new IntegerLiteral(location,
						Integer.toString(1 << newBitLength));
				final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.ARITHMOD,
						createSignedExpression(
								getExpressionFromConcreteTypeValue(instructionType.sExtInst().typeValue().value(),
										oldTypeContext, location),
								oldBitLength, location),
						bitLengthLiteral);
				final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
						new Expression[] { binaryExpr });
				body.addFuncBlock(assignment);
			}
		} else if (instructionType.addInst() != null) {
			final LLVMIRParser.ConcreteTypeContext typeContext = instructionType.addInst().typeValue().firstClassType()
					.concreteType();
			final String typeString = typeContext.intType().getText();
			body.addFuncLocalVar(createVarDecFromConcreteType(typeContext, identifier, body, location));
			final int bitLength = Integer.parseInt(typeString.substring(1));
			final VariableLHS varLhs = new VariableLHS(location, identifier);
			final Expression leftExpr = getExpressionFromConcreteTypeValue(
					instructionType.addInst().typeValue().value(), typeContext, location);
			final Expression rightExpr = getExpressionFromConcreteTypeValue(instructionType.addInst().value(),
					typeContext, location);
			final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.ARITHPLUS, leftExpr, rightExpr);
			final IntegerLiteral bitLengthLiteral = new IntegerLiteral(location, Integer.toString(1 << bitLength));
			final BinaryExpression signedExpr = new BinaryExpression(location, Operator.ARITHMOD, binaryExpr,
					bitLengthLiteral);
			final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
					new Expression[] { signedExpr });
			body.addFuncBlock(assignment);
		} else if (instructionType.sDivInst() != null) {
			final LLVMIRParser.ConcreteTypeContext typeContext = instructionType.sDivInst().typeValue().firstClassType()
					.concreteType();
			final String typeString = typeContext.intType().getText();
			body.addFuncLocalVar(createVarDecFromConcreteType(typeContext, identifier, body, location));
			final int bitLength = Integer.parseInt(typeString.substring(1));
			final VariableLHS varLhs = new VariableLHS(location, identifier);
			final Expression leftExpr = getExpressionFromConcreteTypeValue(
					instructionType.sDivInst().typeValue().value(), typeContext, location);
			final Expression rightExpr = getExpressionFromConcreteTypeValue(instructionType.sDivInst().value(),
					typeContext, location);
			final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.ARITHDIV,
					createSignedExpression(leftExpr, bitLength, location),
					createSignedExpression(rightExpr, bitLength, location));
			final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
					new Expression[] { binaryExpr });
			body.addFuncBlock(assignment);

			final BinaryExpression signedExpr = new BinaryExpression(location, Operator.ARITHMOD,
					createSignedExpression(leftExpr, bitLength, location),
					createSignedExpression(rightExpr, bitLength, location));
			final IntegerLiteral zeroLiteral = new IntegerLiteral(location, "0");
			final BinaryExpression leftBinaryExpr = new BinaryExpression(location, Operator.COMPNEQ, signedExpr,
					zeroLiteral);
			final IdentifierExpression identifierExpr = new IdentifierExpression(location, identifier);
			final BinaryExpression rightBinaryExpr = new BinaryExpression(location, Operator.COMPLT, identifierExpr,
					zeroLiteral);
			final BinaryExpression condBinaryExpr = new BinaryExpression(location, Operator.LOGICAND, leftBinaryExpr,
					rightBinaryExpr);
			final IntegerLiteral oneLiteral = new IntegerLiteral(location, "1");
			final BinaryExpression thenBinaryExpr = new BinaryExpression(location, Operator.ARITHPLUS, identifierExpr,
					oneLiteral);
			final IfThenElseExpression ifThenElseExpr = new IfThenElseExpression(location, condBinaryExpr,
					thenBinaryExpr, identifierExpr);
			final VariableLHS varLhs2 = new VariableLHS(location, identifier);
			final AssignmentStatement assignment2 = new AssignmentStatement(location, new LeftHandSide[] { varLhs2 },
					new Expression[] { ifThenElseExpr });
			body.addFuncBlock(assignment2);

			final IntegerLiteral bitLengthLiteral = new IntegerLiteral(location, Integer.toString(1 << bitLength));
			final BinaryExpression binaryExpr3 = new BinaryExpression(location, Operator.ARITHMOD, identifierExpr,
					bitLengthLiteral);
			final VariableLHS varLhs3 = new VariableLHS(location, identifier);
			final AssignmentStatement assignment3 = new AssignmentStatement(location, new LeftHandSide[] { varLhs3 },
					new Expression[] { binaryExpr3 });
			body.addFuncBlock(assignment3);
		} else if (instructionType.uDivInst() != null) {
			final LLVMIRParser.ConcreteTypeContext typeContext = instructionType.uDivInst().typeValue().firstClassType()
					.concreteType();
			final String typeString = typeContext.intType().getText();
			body.addFuncLocalVar(createVarDecFromConcreteType(typeContext, identifier, body, location));
			final int bitLength = Integer.parseInt(typeString.substring(1));
			final VariableLHS varLhs = new VariableLHS(location, identifier);
			final Expression leftExpr = getExpressionFromConcreteTypeValue(
					instructionType.uDivInst().typeValue().value(), typeContext, location);
			final Expression rightExpr = getExpressionFromConcreteTypeValue(instructionType.uDivInst().value(),
					typeContext, location);
			final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.ARITHDIV, leftExpr, rightExpr);
			final IntegerLiteral bitLengthLiteral = new IntegerLiteral(location, Integer.toString(1 << bitLength));
			final BinaryExpression signedExpr = new BinaryExpression(location, Operator.ARITHMOD, binaryExpr,
					bitLengthLiteral);
			final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
					new Expression[] { signedExpr });
			body.addFuncBlock(assignment);
		} else if (instructionType.uRemInst() != null) {
			final LLVMIRParser.ConcreteTypeContext typeContext = instructionType.uRemInst().typeValue().firstClassType()
					.concreteType();
			final String typeString = typeContext.intType().getText();
			body.addFuncLocalVar(createVarDecFromConcreteType(typeContext, identifier, body, location));
			final int bitLength = Integer.parseInt(typeString.substring(1));
			final VariableLHS varLhs = new VariableLHS(location, identifier);
			final Expression leftExpr = getExpressionFromConcreteTypeValue(
					instructionType.uRemInst().typeValue().value(), typeContext, location);
			final Expression rightExpr = getExpressionFromConcreteTypeValue(instructionType.uRemInst().value(),
					typeContext, location);
			final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.ARITHMOD, leftExpr, rightExpr);
			final IntegerLiteral bitLengthLiteral = new IntegerLiteral(location, Integer.toString(1 << bitLength));
			final BinaryExpression signedExpr = new BinaryExpression(location, Operator.ARITHMOD, binaryExpr,
					bitLengthLiteral);
			final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
					new Expression[] { signedExpr });
			body.addFuncBlock(assignment);
		} else if (instructionType.sRemInst() != null) {
			final LLVMIRParser.ConcreteTypeContext typeContext = instructionType.sRemInst().typeValue().firstClassType()
					.concreteType();
			final String typeString = typeContext.intType().getText();
			body.addFuncLocalVar(createVarDecFromConcreteType(typeContext, identifier, body, location));
			final int bitLength = Integer.parseInt(typeString.substring(1));
			final VariableLHS varLhs = new VariableLHS(location, identifier);
			final Expression leftExpr = getExpressionFromConcreteTypeValue(
					instructionType.sRemInst().typeValue().value(), typeContext, location);
			final Expression rightExpr = getExpressionFromConcreteTypeValue(instructionType.sRemInst().value(),
					typeContext, location);
			final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.ARITHMOD,
					createSignedExpression(leftExpr, bitLength, location),
					createSignedExpression(rightExpr, bitLength, location));
			final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
					new Expression[] { binaryExpr });
			body.addFuncBlock(assignment);

			final IntegerLiteral zeroLiteral = new IntegerLiteral(location, "0");
			final BinaryExpression leftBinaryExpr = new BinaryExpression(location, Operator.COMPLT, binaryExpr,
					zeroLiteral);
			final BinaryExpression rightBinaryExpr = new BinaryExpression(location, Operator.COMPGT,
					new IdentifierExpression(location, identifier), zeroLiteral);
			final BinaryExpression condBinaryExpr = new BinaryExpression(location, Operator.LOGICAND, leftBinaryExpr,
					rightBinaryExpr);
			final IdentifierExpression identifierExpr = new IdentifierExpression(location, identifier);
			final BinaryExpression binaryExpr2 = new BinaryExpression(location, Operator.ARITHMINUS, identifierExpr,
					createSignedExpression(rightBinaryExpr, bitLength, location));
			final VariableLHS varLhs2 = new VariableLHS(location, identifier);
			final AssignmentStatement thenAssignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs2 },
					new Expression[] { binaryExpr2 });
			final IfStatement ifStmt = new IfStatement(location, condBinaryExpr, new Statement[] { thenAssignment },
					new Statement[] {});
			body.addFuncBlock(ifStmt);

			final BinaryExpression leftBinaryExpr2 = new BinaryExpression(location, Operator.COMPGT,
					createSignedExpression(leftExpr, bitLength, location), zeroLiteral);
			final BinaryExpression rightBinaryExpr2 = new BinaryExpression(location, Operator.COMPLT,
					createSignedExpression(rightExpr, bitLength, location), zeroLiteral);
			final BinaryExpression condBinaryExpr2 = new BinaryExpression(location, Operator.LOGICAND, leftBinaryExpr2,
					rightBinaryExpr2);
			final BinaryExpression binaryExpr3 = new BinaryExpression(location, Operator.ARITHMINUS, identifierExpr,
					createSignedExpression(rightBinaryExpr2, bitLength, location));
			final AssignmentStatement thenAssignment2 = new AssignmentStatement(location,
					new LeftHandSide[] { varLhs2 }, new Expression[] { binaryExpr3 });
			final IfStatement ifStmt2 = new IfStatement(location, condBinaryExpr2, new Statement[] { thenAssignment2 },
					new Statement[] {});
			body.addFuncBlock(ifStmt2);

			final IntegerLiteral bitLengthLiteral = new IntegerLiteral(location, Integer.toString(1 << bitLength));
			final BinaryExpression binaryExpr4 = new BinaryExpression(location, Operator.ARITHMOD, identifierExpr,
					bitLengthLiteral);
			final AssignmentStatement assignment2 = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
					new Expression[] { binaryExpr4 });
			body.addFuncBlock(assignment2);
		} else if (instructionType.subInst() != null) {
			final LLVMIRParser.ConcreteTypeContext typeContext = instructionType.subInst().typeValue().firstClassType()
					.concreteType();
			final String typeString = typeContext.intType().getText();
			body.addFuncLocalVar(createVarDecFromConcreteType(typeContext, identifier, body, location));
			final int bitLength = Integer.parseInt(typeString.substring(1));
			final VariableLHS varLhs = new VariableLHS(location, identifier);
			final Expression leftExpr = getExpressionFromConcreteTypeValue(
					instructionType.subInst().typeValue().value(), typeContext, location);
			final Expression rightExpr = getExpressionFromConcreteTypeValue(instructionType.subInst().value(),
					typeContext, location);
			final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.ARITHMINUS, leftExpr,
					rightExpr);
			final IntegerLiteral bitLengthLiteral = new IntegerLiteral(location, Integer.toString(1 << bitLength));
			final BinaryExpression signedExpr = new BinaryExpression(location, Operator.ARITHMOD, binaryExpr,
					bitLengthLiteral);
			final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
					new Expression[] { signedExpr });
			body.addFuncBlock(assignment);
		} else if (instructionType.mulInst() != null) {
			final LLVMIRParser.ConcreteTypeContext typeContext = instructionType.mulInst().typeValue().firstClassType()
					.concreteType();
			final String typeString = typeContext.intType().getText();
			body.addFuncLocalVar(createVarDecFromConcreteType(typeContext, identifier, body, location));
			final int bitLength = Integer.parseInt(typeString.substring(1));
			final VariableLHS varLhs = new VariableLHS(location, identifier);
			final Expression leftExpr = getExpressionFromConcreteTypeValue(
					instructionType.mulInst().typeValue().value(), typeContext, location);
			final Expression rightExpr = getExpressionFromConcreteTypeValue(instructionType.mulInst().value(),
					typeContext, location);
			final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.ARITHMUL, leftExpr, rightExpr);
			final IntegerLiteral bitLengthLiteral = new IntegerLiteral(location, Integer.toString(1 << bitLength));
			final BinaryExpression signedExpr = new BinaryExpression(location, Operator.ARITHMOD, binaryExpr,
					bitLengthLiteral);
			final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
					new Expression[] { signedExpr });
			body.addFuncBlock(assignment);
		} else if (instructionType.allocaInst() != null) {
			final LLVMIRParser.ConcreteTypeContext typeContext = instructionType.allocaInst().typeValue()
					.firstClassType().concreteType();
			body.addFuncLocalVar(createVarDecFromConcreteType(typeContext, identifier, body, location));
		} else if (instructionType.callInst() != null) {
			final LLVMIRParser.TypeContext typeContext = instructionType.callInst().type();
			final String typeString = typeContext.intType().getText();
			body.addFuncLocalVar(createVarDecFromType(typeContext, identifier, body, location));
			final String callIdentifier = instructionType.callInst().value().constant().getText();
			if (callIdentifier.equals("@__VERIFIER_nondet_int") || callIdentifier.equals("@__VERIFIER_nondet_short")
					|| callIdentifier.equals("@__VERIFIER_nondet_ushort")
					|| callIdentifier.equals("@__VERIFIER_nondet_bool")
					|| callIdentifier.equals("@__VERIFIER_nondet_ulong")
					|| callIdentifier.equals("@__VERIFIER_nondet_uint128")
					|| callIdentifier.equals("@__VERIFIER_nondet_uint")
					|| callIdentifier.equals("@__VERIFIER_nondet_ulonglong")
					|| callIdentifier.equals("@__VERIFIER_nondet_char")
					|| callIdentifier.equals("@__VERIFIER_nondet_uchar") || callIdentifier.equals("@printf")) {
				final VariableLHS varLhs = new VariableLHS(location, identifier);
				final HavocStatement havocStmt = new HavocStatement(location, new VariableLHS[] { varLhs });
				body.addFuncBlock(havocStmt);
			} else {
				final ArrayList<Expression> args = new ArrayList<>();
				for (final LLVMIRParser.ArgContext arg : instructionType.callInst().args().arg()) {
					args.add(getExpressionFromTypeValue(arg.value(), typeContext, location));
				}
				final VariableLHS varLhs = new VariableLHS(location, identifier);
				final CallStatement callStmt = new CallStatement(location, false, new VariableLHS[] {},
						unifyIdentifier(callIdentifier), args.toArray(Expression[]::new));
				body.addFuncBlock(callStmt);
			}
		} else if (instructionType.selectInst() != null) {
			final LLVMIRParser.ConcreteTypeContext typeContext0 = instructionType.selectInst().typeValue(0)
					.firstClassType().concreteType();
			final LLVMIRParser.ConcreteTypeContext typeContext1 = instructionType.selectInst().typeValue(1)
					.firstClassType().concreteType();

			final Expression ifExpr = getExpressionFromConcreteTypeValue(
					instructionType.selectInst().typeValue(0).value(), typeContext0, location);
			final Expression thenExpr = getExpressionFromConcreteTypeValue(
					instructionType.selectInst().typeValue(1).value(), typeContext1, location);
			final Expression elseExpr = getExpressionFromConcreteTypeValue(
					instructionType.selectInst().typeValue(2).value(), typeContext1, location);
			body.addFuncLocalVar(createVarDecFromConcreteType(typeContext1, identifier, body, location));
			final VariableLHS thenVarLhs = new VariableLHS(location, identifier);
			final VariableLHS elseVarLhs = new VariableLHS(location, identifier);
			final AssignmentStatement thenAssignment = new AssignmentStatement(location,
					new LeftHandSide[] { thenVarLhs }, new Expression[] { thenExpr });
			final AssignmentStatement elseAssignment = new AssignmentStatement(location,
					new LeftHandSide[] { elseVarLhs }, new Expression[] { elseExpr });
			final IfStatement ifStmt = new IfStatement(location, ifExpr, new Statement[] { thenAssignment },
					new Statement[] { elseAssignment });
			body.addFuncBlock(ifStmt);
		} else if (instructionType.andInst() != null) {
			createHavocStatementFromTypeValue(body, instructionType.addInst().typeValue(), location, identifier);
		} else if (instructionType.orInst() != null) {
			createHavocStatementFromTypeValue(body, instructionType.orInst().typeValue(), location, identifier);
		} else if (instructionType.xorInst() != null) {
			createHavocStatementFromTypeValue(body, instructionType.xorInst().typeValue(), location, identifier);
		} else if (instructionType.shlInst() != null) {
			createHavocStatementFromTypeValue(body, instructionType.shlInst().typeValue(), location, identifier);
		} else if (instructionType.aShrInst() != null) {
			createHavocStatementFromTypeValue(body, instructionType.aShrInst().typeValue(), location, identifier);
		} else if (instructionType.lShrInst() != null) {
			createHavocStatementFromTypeValue(body, instructionType.lShrInst().typeValue(), location, identifier);
		}

		else {
			// TODO: Support for other instructions
			throw new AssertionError("The support for the given instruction is not implemented yet.");
		}
		return body;
	}

	/**
	 * Handles the visit event for a branch terminator in the LLVM IR parse tree.
	 *
	 * This method processes the branch terminator and creates a GotoStatement to jump to the specified label.
	 *
	 * @param ctx The parse tree context for the branch terminator.
	 * @return A FunctionBody object containing the GotoStatement.
	 */
	@Override
	public FunctionBody visitBrTerm(final LLVMIRParser.BrTermContext ctx) {
		final LlvmirLocation location = new LlvmirLocation(mFilename, ctx.getStart().getLine(), ctx.getStop().getLine(),
				ctx.getStart().getCharPositionInLine(), ctx.getStop().getCharPositionInLine());
		final FunctionBody body = new FunctionBody();
		final String labelIdentifier = unifyIdentifier(ctx.label().LocalIdent().getText());
		final GotoStatement gotoStmt = new GotoStatement(location, new String[] { labelIdentifier });
		body.addFuncBlock(gotoStmt);

		return body;
	}

	/**
	 * Handles the visit event for a conditional branch terminator in the LLVM IR parse tree.
	 *
	 * This method processes the conditional branch terminator and creates an IfStatement to handle the condition, along
	 * with GotoStatements for the true and false branches.
	 *
	 * @param ctx The parse tree context for the conditional branch terminator.
	 * @return A FunctionBody object containing the IfStatement and GotoStatements.
	 */
	@Override
	public FunctionBody visitCondBrTerm(final LLVMIRParser.CondBrTermContext ctx) {
		final LlvmirLocation location = new LlvmirLocation(mFilename, ctx.getStart().getLine(), ctx.getStop().getLine(),
				ctx.getStart().getCharPositionInLine(), ctx.getStop().getCharPositionInLine());
		final FunctionBody body = new FunctionBody();

		final String variableIdentifier = unifyIdentifier(ctx.value().LocalIdent().getText());
		final String thenLabelIdentifier = unifyIdentifier(ctx.label(0).LocalIdent().getText());
		final String elseLabelIdentifier = unifyIdentifier(ctx.label(1).LocalIdent().getText());
		final GotoStatement thenGoto = new GotoStatement(location, new String[] { thenLabelIdentifier });
		final GotoStatement elseGoto = new GotoStatement(location, new String[] { elseLabelIdentifier });
		final IdentifierExpression variableExpr = new IdentifierExpression(location, variableIdentifier);
		final IfStatement ifStmt = new IfStatement(location, variableExpr, new Statement[] { thenGoto },
				new Statement[] { elseGoto });
		body.addFuncBlock(ifStmt);

		return body;
	}

	/**
	 * Handles the visit event for a store instruction in the LLVM IR parse tree.
	 *
	 * This method processes the store instruction and creates an AssignmentStatement to assign a value to a variable.
	 *
	 * @param ctx The parse tree context for the store instruction.
	 * @return A FunctionBody object containing the AssignmentStatement.
	 */
	@Override
	public FunctionBody visitStoreInst(final LLVMIRParser.StoreInstContext ctx) {
		final FunctionBody body = new FunctionBody();
		final LlvmirLocation location = new LlvmirLocation(mFilename, ctx.getStart().getLine(), ctx.getStop().getLine(),
				ctx.getStart().getCharPositionInLine(), ctx.getStop().getCharPositionInLine());

		final String identifier = unifyIdentifier(ctx.typeValue(1).value().LocalIdent().getText());
		final VariableLHS varLhs = new VariableLHS(location, identifier);
		final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
				new Expression[] { getExpressionFromConcreteTypeValue(ctx.typeValue(0).value(),
						ctx.typeValue(0).firstClassType().concreteType(), location) });
		body.addFuncBlock(assignment);

		return body;
	}

	@Override
	public FunctionBody visitCallInst(final LLVMIRParser.CallInstContext ctx) {
		final FunctionBody body = new FunctionBody();
		final LlvmirLocation location = new LlvmirLocation(mFilename, ctx.getStart().getLine(), ctx.getStop().getLine(),
				ctx.getStart().getCharPositionInLine(), ctx.getStop().getCharPositionInLine());

		final String callIdentifier = ctx.value().constant().getText();
		if (callIdentifier.equals("@__assert_fail") || callIdentifier.equals("@__VERIFIER_error")) {
			final BooleanLiteral boolLit = new BooleanLiteral(location, false);
			final AssertStatement assertStmt = new AssertStatement(location, new NamedAttribute[] {}, boolLit);
			final Check chk = new Check(Spec.ASSERT);
			chk.annotate(assertStmt);
			body.addFuncBlock(assertStmt);
		} else if (callIdentifier.equals("@printf")) {
			// This call can be ignored as it is not relevant for the Boogie translation
		} else {
			final ArrayList<Expression> args = new ArrayList<>();
			for (final LLVMIRParser.ArgContext arg : ctx.args().arg()) {
				args.add(getExpressionFromConcreteTypeValue(arg.value(), arg.concreteType(), location));
			}
			final CallStatement callStmt = new CallStatement(location, false, new VariableLHS[] {},
					unifyIdentifier(callIdentifier), args.toArray(Expression[]::new));
			body.addFuncBlock(callStmt);
		}

		return body;
	}
}
