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
import java.util.HashMap;
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
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class LlvmirToBoogieVisitor extends LLVMIRBaseVisitor<Result> {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private Unit mResult;
	private final String mFilename;
	private LlvmirLocation mLocation;
	private final static String mLabelIdentifier = "#label";
	private final static String mUndefIdentifier = "#undef";

	private final ArrayList<Declaration> mDeclarations = new ArrayList<>();
	private final HashMap<String, Pair<Declaration, Statement>> mGlobalVars = new HashMap<>();

	public LlvmirToBoogieVisitor(final IUltimateServiceProvider services, final ILogger logger, final String filename) {
		assert services != null;
		mServices = services;
		mLogger = logger;
		mResult = null;
		mFilename = filename;
		mLocation = null;
		mLogger.info("Starting translation of LLVM IR to Boogie for file: " + mFilename);
	}

	public Unit getResult() {
		if (mResult == null) {
			mLogger.error("Translation result is null. Ensure that visitCompilationUnit was called successfully.");
			throw new IllegalStateException("Translation result is null");
		}
		return mResult;
	}

	/**
	 * Unifies the identifier by removing colons and ensuring it starts with a valid character.
	 *
	 * This method is used to ensure that identifiers in the Boogie AST conform to the expected format.
	 *
	 * @param identifier The identifier to be unified.
	 * @return A unified identifier string.
	 */
	private static String unifyIdentifier(final String identifier) {
		if (identifier == null || identifier.isEmpty()) {
			return identifier;
		}
		String result = identifier;
		result = result.replace(":", "");
		final char firstChar = result.charAt(0);
		if (Character.isLetterOrDigit(firstChar) || firstChar == '#') {
			return result;
		}
		return result.substring(1);
	}

	/**
	 * Constructs a specification from a given identifier and location.
	 *
	 * This method creates a ModifiesSpecification that indicates the specified variable is modified in the Boogie AST.
	 *
	 * @param identifier The identifier of the variable to be modified.
	 * @param location   The location in the source code where this specification is defined.
	 * @return A Specification object representing the modifies specification for the given identifier.
	 */
	private static Specification constructSpecFromIdentifier(final String identifier, final LlvmirLocation location) {
		final VariableLHS varLhs = new VariableLHS(location, identifier);
		return new ModifiesSpecification(location, false, new VariableLHS[] { varLhs });
	}

	/**
	 * Constructs an initial procedure with the given parameters.
	 *
	 * This method creates a Procedure object representing the initial procedure in the Boogie AST, including its body,
	 * variable declarations, statements, and specifications.
	 *
	 * @param location   The location in the source code where this procedure is defined.
	 * @param identifier The identifier for the procedure.
	 * @param varDecls   The variable declarations for the procedure.
	 * @param stmts      The statements in the body of the procedure.
	 * @param specs      The specifications for the procedure.
	 * @return A Procedure object representing the initial procedure.
	 */
	private static Procedure constructInitialProcedure(final LlvmirLocation location, final String identifier,
			final VariableDeclaration[] varDecls, final Statement[] stmts, final Specification[] specs) {
		final Body body = new Body(location, varDecls, stmts);
		return new Procedure(location, new Attribute[] {}, identifier, new String[] {}, new VarList[] {},
				new VarList[] {}, specs, body);
	}

	/**
	 * Creates initial declarations for global variables and the ULTIMATE.start procedure.
	 *
	 * This method initializes the global variables and constructs the ULTIMATE.start procedure that will be executed at
	 * the start of the program. It also creates an #init procedure for global variable initialization.
	 *
	 * Using addFirst ensures that the initial declarations are at the beginning of the Boogie AST unit.
	 */
	private void createInitialDeclarations() {
		final ArrayList<Statement> stmts = new ArrayList<>();
		final ArrayList<Specification> specs = new ArrayList<>();
		final ArrayList<Declaration> decls = new ArrayList<>();
		for (final String key : mGlobalVars.keySet()) {
			final Pair<Declaration, Statement> pair = mGlobalVars.get(key);
			if (pair == null) {
				mLogger.error("No pair found for global variable: " + key);
				continue;
			}
			decls.add(pair.getFirst());
			stmts.add(pair.getSecond());
			specs.add(constructSpecFromIdentifier(unifyIdentifier(key), (LlvmirLocation) pair.getSecond().getLoc()));
		}

		mDeclarations.addFirst(constructInitialProcedure(mLocation, "#init", new VariableDeclaration[] {},
				stmts.toArray(Statement[]::new), specs.toArray(Specification[]::new)));

		final VariableLHS varLhs = new VariableLHS(mLocation, "#tmp");
		final CallStatement mainCall = new CallStatement(mLocation, false, new VariableLHS[] { varLhs }, "main",
				new Expression[] {});
		final VariableDeclaration varDecl = constructVarDecFromString("int", "#tmp", mLocation);
		final CallStatement initCall = new CallStatement(mLocation, false, new VariableLHS[] {}, "#init",
				new Expression[] {});

		mDeclarations
				.addFirst(constructInitialProcedure(mLocation, "ULTIMATE.start", new VariableDeclaration[] { varDecl },
						new Statement[] { initCall, mainCall }, specs.toArray(Specification[]::new)));

		mDeclarations.addAll(0, decls);
	}

	/**
	 * Constructs a variable declaration from a type and identifier.
	 *
	 * This method creates a VariableDeclaration object with the specified type and identifier, using the provided
	 * location for the declaration.
	 *
	 * @param type       The type of the variable (e.g., "int", "bool").
	 * @param identifier The identifier for the variable.
	 * @param location   The location in the source code where this variable is declared.
	 * @return A VariableDeclaration object representing the variable declaration.
	 */
	private static VariableDeclaration constructVarDecFromString(final String type, final String identifier,
			final LlvmirLocation location) {
		final PrimitiveType primType = new PrimitiveType(location, type);
		final VarList varList = new VarList(location, new String[] { unifyIdentifier(identifier) }, primType);
		return new VariableDeclaration(location, new Attribute[] {}, new VarList[] { varList });
	}

	// TODO: Javadoc
	private static VariableDeclaration constructVarDecFromTypeContext(final ParserRuleContext typeContext,
			final String identifier, final Result result, final LlvmirLocation location) throws AssertionError {
		final LLVMIRParser.IntTypeContext intType;

		if (typeContext instanceof LLVMIRParser.ConcreteTypeContext) {
			intType = ((LLVMIRParser.ConcreteTypeContext) typeContext).intType();
		} else if (typeContext instanceof LLVMIRParser.TypeContext) {
			intType = ((LLVMIRParser.TypeContext) typeContext).intType();
		} else {
			throw new AssertionError("Unsupported type context for variable declaration: " + typeContext.getText());
		}

		if (intType == null) {
			throw new AssertionError("Type context does not contain an intType: " + typeContext.getText());
		}

		final String typeString = intType.getText();
		final String typeIdentifier = typeString.equals("i1") ? "bool" : "int";

		if (typeIdentifier.equals("int")) {
			final int bitLength = getBitLengthFromType(typeContext);
			final VariableLHS varLhs = new VariableLHS(location, unifyIdentifier(identifier));
			final HavocStatement havocStmt = new HavocStatement(location, new VariableLHS[] { varLhs });
			result.addFuncBlock(havocStmt);

			final IdentifierExpression identExpr = new IdentifierExpression(location, unifyIdentifier(identifier));
			final IntegerLiteral zeroLiteral = new IntegerLiteral(location, "0");
			final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.COMPGEQ, identExpr,
					zeroLiteral);
			result.addFuncBlock(new AssumeStatement(location, new NamedAttribute[] {}, binaryExpr));

			final IntegerLiteral bitLengthLiteral = new IntegerLiteral(location, Integer.toString(bitLength));
			final BinaryExpression signedExpr = new BinaryExpression(location, Operator.COMPLT, identExpr,
					bitLengthLiteral);
			result.addFuncBlock(new AssumeStatement(location, new NamedAttribute[] {}, signedExpr));
		}

		final PrimitiveType type = new PrimitiveType(location, typeIdentifier);
		final VarList varList = new VarList(location, new String[] { unifyIdentifier(identifier) }, type);
		return new VariableDeclaration(location, new Attribute[] {}, new VarList[] { varList });

	}

	// TODO: Javadoc
	private static Expression constructExpressionFromValue(final LLVMIRParser.ValueContext valueContext,
			final ParserRuleContext typeContext, final LlvmirLocation location) throws AssertionError {
		if (valueContext.LocalIdent() != null) {
			final String operandName = valueContext.LocalIdent().getText();
			return new IdentifierExpression(location, unifyIdentifier(operandName));
		} else if (valueContext.constant() != null) {
			return constructExpressionFromConstant(valueContext.constant(), typeContext, location);
		} else {
			throw new AssertionError(
					"The support for iCmp instructions with operands other than constants or local identifiers is not implemented yet.");
		}
	}

	// TODO: Javadoc
	private static Expression constructExpressionFromConstant(final LLVMIRParser.ConstantContext constantContext,
			final ParserRuleContext typeContext, final LlvmirLocation location) throws AssertionError {
		if (constantContext.intConst() != null) {
			final int bitLength = getBitLengthFromType(typeContext);
			final int constValue = Integer.parseInt(constantContext.intConst().getText());
			final int modValue = euclideanMod(constValue, bitLength);
			return new IntegerLiteral(location, Integer.toString(modValue));
		} else if (constantContext.boolConst() != null) {
			return new BooleanLiteral(location, constantContext.boolConst().getText().equals("true"));
		} else if (constantContext.undefConst() != null) {
			return new IdentifierExpression(location, mUndefIdentifier);
		}
		throw new AssertionError(
				"The support for iCmp instructions with constant operands other than integers and booleans is not implemented yet.");
	}

	/**
	 * Computes the Euclidean modulus of a value with respect to a specified bit length.
	 *
	 * This method calculates the modulus of the given value with respect to 2 raised to the power of the specified bit
	 * length, ensuring that the result is always non-negative.
	 *
	 * @param value     The value for which to compute the modulus.
	 * @param bitLength The bit length for the modulus operation.
	 * @return The non-negative modulus of the value with respect to 2^bitLength.
	 */
	public static int euclideanMod(final int value, final int bitLength) {
		final int modulus = 1 << bitLength;
		return ((value % modulus) + modulus) % modulus;
	}

	/**
	 * Retrieves the bit length from a type context.
	 *
	 * This method extracts the bit length from a type context, which can be either a ConcreteTypeContext or a
	 * TypeContext. It assumes that the type is an integer type (e.g., "i32") and returns the bit length as an integer.
	 *
	 * @param typeContext The type context from which to extract the bit length.
	 * @return The bit length of the integer type.
	 * @throws AssertionError if the type context is not supported.
	 */
	private static int getBitLengthFromType(final ParserRuleContext typeContext) throws AssertionError {
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
	private static AssignmentStatement createLabelAssignment(final LlvmirLocation location, final int labelIndex) {
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
	 * result.
	 *
	 * @param result     The result to which the havoc statement will be added.
	 * @param typeValue  The type value context from the LLVM IR parse tree.
	 * @param location   The location in the source code where this instruction is defined.
	 * @param identifier The identifier for the local variable to be created.
	 */
	private static void createHavocStatementFromTypeValue(final Result result,
			final LLVMIRParser.TypeValueContext typeValue, final LlvmirLocation location, final String identifier) {
		final LLVMIRParser.ConcreteTypeContext tpyeContext = typeValue.firstClassType().concreteType();
		result.addFuncLocalVar(constructVarDecFromTypeContext(tpyeContext, identifier, result, location));
		final VariableLHS varLhs = new VariableLHS(location, identifier);
		final HavocStatement havocStmt = new HavocStatement(location, new VariableLHS[] { varLhs });
		result.addFuncBlock(havocStmt);
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
	 * Handles the visit event for the compilation unit in the LLVM IR parse tree.
	 *
	 * This method initializes the location and processes the children of the compilation unit context to create
	 * declarations and the final Boogie AST unit.
	 *
	 * @param ctx The parse tree context for the compilation unit.
	 * @return A Result object containing the final Boogie AST unit.
	 */
	@Override
	public Result visitCompilationUnit(final LLVMIRParser.CompilationUnitContext ctx) {
		mLocation = new LlvmirLocation(mFilename, ctx.getStart().getLine(), ctx.getStop().getLine(),
				ctx.getStart().getCharPositionInLine(), ctx.getStop().getCharPositionInLine());

		visitChildren(ctx);

		createInitialDeclarations();
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
	public Result visitFuncDef(final LLVMIRParser.FuncDefContext ctx) throws AssertionError {
		final Result result = new Result();

		result.addFuncLocalVar(constructVarDecFromString("int", mUndefIdentifier, mLocation));
		final VariableLHS undefVar = new VariableLHS(mLocation, mUndefIdentifier);
		final HavocStatement havocStmt = new HavocStatement(mLocation, new VariableLHS[] { undefVar });
		result.addFuncBlock(havocStmt);

		for (final ParseTree child : ctx.children) {
			final Result childResult = child.accept(this);
			if (childResult != null) {
				result.merge(childResult);
			}
		}

		result.addFuncLocalVar(constructVarDecFromString("int", mLabelIdentifier, mLocation));
		final String funcName = unifyIdentifier(ctx.funcHeader().GlobalIdent().getText());
		final LLVMIRParser.TypeContext returnType = ctx.funcHeader().type();

		final LlvmirLocation location = new LlvmirLocation(mFilename, ctx.getStart().getLine(), ctx.getStop().getLine(),
				ctx.getStart().getCharPositionInLine(), ctx.getStop().getCharPositionInLine());

		final Body body = new Body(location, result.getFuncLocalVars().toArray(VariableDeclaration[]::new),
				result.getFuncBlock().toArray(Statement[]::new));
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
			throw new AssertionError(
					"The support for return types other than void and integers is not implemented yet.");
		}

		final Procedure procedure = new Procedure(location, attributes.toArray(Attribute[]::new), funcName,
				typeParams.toArray(String[]::new), inParams.toArray(VarList[]::new), outParams.toArray(VarList[]::new),
				spec.toArray(Specification[]::new), body);
		mDeclarations.add(procedure);

		return null;
	}

	/**
	 * Handles the visit event for a function body in the LLVM IR parse tree.
	 *
	 * This method processes the children of the function body context and merges their results into a single Result
	 * object.
	 *
	 * @param ctx The parse tree context for the function body.
	 * @return A Result object containing the merged results of the children.
	 */
	@Override
	public Result visitFuncBody(final LLVMIRParser.FuncBodyContext ctx) {
		final Result result = new Result();
		for (final LLVMIRParser.BasicBlockContext childCtx : ctx.basicBlock()) {
			final Result childResult = visit(childCtx);
			if (childResult != null) {
				result.merge(childResult);
			}
		}
		return result;
	}

	/**
	 * Handles the visit event for a basic block in the LLVM IR parse tree.
	 *
	 * This method processes the basic block context, creates a label for it, and processes its children to generate
	 * statements for the Boogie AST. It also handles terminators like conditional and unconditional branches.
	 *
	 * @param ctx The parse tree context for the basic block.
	 * @return A Result object containing the generated statements for the basic block.
	 */
	@Override
	public Result visitBasicBlock(final LLVMIRParser.BasicBlockContext ctx) {
		final LlvmirLocation location = new LlvmirLocation(mFilename, ctx.getStart().getLine(), ctx.getStop().getLine(),
				ctx.getStart().getCharPositionInLine(), ctx.getStop().getCharPositionInLine());
		final Result result = new Result();

		final LLVMIRParser.FuncBodyContext funcBodyCtx = (LLVMIRParser.FuncBodyContext) ctx.getParent();
		final List<LLVMIRParser.BasicBlockContext> blocks = funcBodyCtx.basicBlock();
		final int index = blocks.indexOf(ctx);

		final String labelName = unifyIdentifier(ctx.LabelIdent().getText());
		final Label label = new Label(location, labelName, new NamedAttribute[] {});
		result.addFuncBlock(label);

		for (final ParseTree child : ctx.children) {
			if (child.getChild(0) instanceof LLVMIRParser.CondBrTermContext
					|| child.getChild(0) instanceof LLVMIRParser.BrTermContext) {
				result.addFuncBlock(createLabelAssignment(location, index));
			}
			final Result childResult = child.accept(this);
			if (childResult != null) {
				result.merge(childResult);
			}
		}

		// TODO: Add comment that explains why we add a label assignment here
		if (!(index == blocks.size() - 1)) {
			result.addFuncBlock(createLabelAssignment(location, index));
		}

		return result;
	}

	/**
	 * Handles the visit event for a return term in the LLVM IR parse tree.
	 *
	 * This method processes the return statement, handling both void returns and returns with values. It creates
	 * appropriate Boogie statements based on the return type.
	 *
	 * @param ctx The parse tree context for the return term.
	 * @return A Result object containing the generated statements for the return term.
	 * @throws AssertionError if the return type is not supported.
	 */
	@Override
	public Result visitRetTerm(final LLVMIRParser.RetTermContext ctx) throws AssertionError {
		final Result result = new Result();

		final LlvmirLocation location = new LlvmirLocation(mFilename, ctx.getStart().getLine(), ctx.getStop().getLine(),
				ctx.getStart().getCharPositionInLine(), ctx.getStop().getCharPositionInLine());

		if (ctx.value() == null) {
			// If there is no value, we assume a void return type
			final ReturnStatement returnStmt = new ReturnStatement(location);
			result.addFuncBlock(returnStmt);
		} else {
			final LLVMIRParser.ConcreteTypeContext returnType = ctx.concreteType();
			if (returnType.intType() != null) {
				final VariableLHS returnVar = new VariableLHS(location, "ret");
				final AssignmentStatement assignmentStmt = new AssignmentStatement(location,
						new LeftHandSide[] { returnVar },
						new Expression[] { constructExpressionFromValue(ctx.value(), returnType, location) });
				final ReturnStatement returnStmt = new ReturnStatement(location);
				result.addFuncBlocks(Arrays.asList(assignmentStmt, returnStmt));
			} else {
				throw new AssertionError("The support for return types other than integers is not implemented yet.");
			}
		}
		return result;

	}

	/**
	 * Handles the visit event for a global variable definition in the LLVM IR parse tree.
	 *
	 * This method translates the global variable definition into a Boogie variable declaration and initializes it based
	 * on the type of the constant value.
	 *
	 * @param ctx The parse tree context for the global variable definition.
	 * @return A Result object containing the variable declaration and initialization statements.
	 * @throws AssertionError if the type is not supported.
	 */
	@Override
	public Result visitGlobalDef(final LLVMIRParser.GlobalDefContext ctx) throws AssertionError {
		final LLVMIRParser.TypeContext type = ctx.type();
		final String identifier = unifyIdentifier(ctx.GlobalIdent().getText());
		final LlvmirLocation location = new LlvmirLocation(mFilename, ctx.getStart().getLine(), ctx.getStop().getLine(),
				ctx.getStart().getCharPositionInLine(), ctx.getStop().getCharPositionInLine());

		if (type.intType() == null) {
			throw new AssertionError("The support for types other than integers is not implemented yet.");
		}

		final String typeString = type.intType().getText().equals("i1") ? "bool" : "int";
		final VariableDeclaration varDecl = constructVarDecFromString(typeString, identifier, location);

		final VariableLHS varLhs = new VariableLHS(location, identifier);
		final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
				new Expression[] { constructExpressionFromConstant(ctx.constant(), type, location) });

		mGlobalVars.put(identifier, new Pair<>(varDecl, assignment));

		return null;
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
	public Result visitLocalDefInst(final LLVMIRParser.LocalDefInstContext ctx) {
		final Result result = new Result();
		final String identifier = unifyIdentifier(ctx.LocalIdent().getText());
		final LLVMIRParser.ValueInstructionContext instructionType = ctx.valueInstruction();
		final LlvmirLocation location = new LlvmirLocation(mFilename, ctx.getStart().getLine(), ctx.getStop().getLine(),
				ctx.getStart().getCharPositionInLine(), ctx.getStop().getCharPositionInLine());

		if (instructionType.loadInst() != null) {
			final LLVMIRParser.TypeContext variableType = instructionType.loadInst().type();
			if (variableType.intType() != null) {
				result.addFuncLocalVar(constructVarDecFromTypeContext(variableType, identifier, result, location));
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
				result.addFuncBlock(assignment);
			} else {
				throw new AssertionError(
						"The support for types other than integers in load instructions is not implemented yet.");
			}
		} else if (instructionType.iCmpInst() != null) {
			result.addFuncLocalVar(constructVarDecFromString("bool", identifier, location));
			final LLVMIRParser.ConcreteTypeContext typeContext = instructionType.iCmpInst().typeValue().firstClassType()
					.concreteType();

			Expression leftExpr = null;
			Expression rightExpr = null;
			final Operator operator = getCompOperatorFromOperatorValue(instructionType.iCmpInst().iPred().getText());

			final LLVMIRParser.ValueContext leftValue = instructionType.iCmpInst().typeValue().value();
			leftExpr = constructExpressionFromValue(leftValue, typeContext, location);

			final LLVMIRParser.ValueContext rightValue = instructionType.iCmpInst().value();
			rightExpr = constructExpressionFromValue(rightValue, typeContext, location);

			if (typeContext.intType() != null && !typeContext.intType().getText().equals("i1")) {
				final int bitLength = getBitLengthFromType(typeContext);
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
			result.addFuncBlock(assignment);
		} else if (instructionType.phiInst() != null) {
			final LLVMIRParser.TypeContext typeContext = instructionType.phiInst().type();
			result.addFuncLocalVar(constructVarDecFromTypeContext(typeContext, identifier, result, location));
			for (final LLVMIRParser.IncContext inc : instructionType.phiInst().inc()) {
				final String incIdentifier = unifyIdentifier(inc.LocalIdent().getText());
				final int labelIndex = getLabelIndexFromFuncBody(ctx, incIdentifier);
				final IdentifierExpression incExpr = new IdentifierExpression(location, mLabelIdentifier);
				final IntegerLiteral labelIndexLiteral = new IntegerLiteral(location, Integer.toString(labelIndex));
				final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.COMPEQ, incExpr,
						labelIndexLiteral);
				final VariableLHS varLhs = new VariableLHS(location, identifier);
				final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
						new Expression[] { constructExpressionFromValue(inc.value(), typeContext, location) });
				final IfStatement ifStmt = new IfStatement(location, binaryExpr, new Statement[] { assignment },
						new Statement[] {});
				result.addFuncBlock(ifStmt);
			}
		} else if (instructionType.zExtInst() != null) {
			result.addFuncLocalVar(constructVarDecFromString("int", identifier, location));
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
						location, constructExpressionFromValue(instructionType.zExtInst().typeValue().value(),
								typeContext, location),
						new Statement[] { thenAssignment }, new Statement[] { elseAssignment });
				result.addFuncBlock(ifStmt);
			} else {
				final VariableLHS varLhs = new VariableLHS(location, identifier);
				final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
						new Expression[] { constructExpressionFromValue(instructionType.zExtInst().typeValue().value(),
								typeContext, location) });
				result.addFuncBlock(assignment);
			}
		} else if (instructionType.sExtInst() != null) {
			final LLVMIRParser.TypeContext newTypeContext = instructionType.sExtInst().type();
			final LLVMIRParser.ConcreteTypeContext oldTypeContext = instructionType.sExtInst().typeValue()
					.firstClassType().concreteType();
			final String oldTypeString = oldTypeContext.intType().getText();
			result.addFuncLocalVar(constructVarDecFromTypeContext(newTypeContext, identifier, result, location));
			if (oldTypeContext.intType() != null && oldTypeString.equals("i1")) {
				final IntegerLiteral zeroLiteral = new IntegerLiteral(location, "0");
				final IntegerLiteral oneLiteral = new IntegerLiteral(location, "1");
				final VariableLHS zeroVarLhs = new VariableLHS(location, identifier);
				final VariableLHS oneVarLhs = new VariableLHS(location, identifier);
				final AssignmentStatement elseAssignment = new AssignmentStatement(location,
						new LeftHandSide[] { zeroVarLhs }, new Expression[] { zeroLiteral });
				final AssignmentStatement thenAssignment = new AssignmentStatement(location,
						new LeftHandSide[] { oneVarLhs }, new Expression[] { oneLiteral });
				final IfStatement ifStmt = new IfStatement(
						location, constructExpressionFromValue(instructionType.sExtInst().typeValue().value(),
								oldTypeContext, location),
						new Statement[] { thenAssignment }, new Statement[] { elseAssignment });
				result.addFuncBlock(ifStmt);
			} else {
				final VariableLHS varLhs = new VariableLHS(location, identifier);
				final int oldBitLength = getBitLengthFromType(oldTypeContext);
				final int newBitLength = getBitLengthFromType(newTypeContext);
				final IntegerLiteral bitLengthLiteral = new IntegerLiteral(location,
						Integer.toString(1 << newBitLength));
				final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.ARITHMOD,
						createSignedExpression(
								constructExpressionFromValue(instructionType.sExtInst().typeValue().value(),
										oldTypeContext, location),
								oldBitLength, location),
						bitLengthLiteral);
				final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
						new Expression[] { binaryExpr });
				result.addFuncBlock(assignment);
			}
		} else if (instructionType.addInst() != null) {
			final LLVMIRParser.ConcreteTypeContext typeContext = instructionType.addInst().typeValue().firstClassType()
					.concreteType();
			result.addFuncLocalVar(constructVarDecFromTypeContext(typeContext, identifier, result, location));
			final int bitLength = getBitLengthFromType(typeContext);
			final VariableLHS varLhs = new VariableLHS(location, identifier);
			final Expression leftExpr = constructExpressionFromValue(instructionType.addInst().typeValue().value(),
					typeContext, location);
			final Expression rightExpr = constructExpressionFromValue(instructionType.addInst().value(), typeContext,
					location);
			final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.ARITHPLUS, leftExpr, rightExpr);
			final IntegerLiteral bitLengthLiteral = new IntegerLiteral(location, Integer.toString(1 << bitLength));
			final BinaryExpression signedExpr = new BinaryExpression(location, Operator.ARITHMOD, binaryExpr,
					bitLengthLiteral);
			final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
					new Expression[] { signedExpr });
			result.addFuncBlock(assignment);
		} else if (instructionType.sDivInst() != null) {
			final LLVMIRParser.ConcreteTypeContext typeContext = instructionType.sDivInst().typeValue().firstClassType()
					.concreteType();
			result.addFuncLocalVar(constructVarDecFromTypeContext(typeContext, identifier, result, location));
			final int bitLength = getBitLengthFromType(typeContext);
			final VariableLHS varLhs = new VariableLHS(location, identifier);
			final Expression leftExpr = constructExpressionFromValue(instructionType.sDivInst().typeValue().value(),
					typeContext, location);
			final Expression rightExpr = constructExpressionFromValue(instructionType.sDivInst().value(), typeContext,
					location);
			final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.ARITHDIV,
					createSignedExpression(leftExpr, bitLength, location),
					createSignedExpression(rightExpr, bitLength, location));
			final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
					new Expression[] { binaryExpr });
			result.addFuncBlock(assignment);

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
			result.addFuncBlock(assignment2);

			final IntegerLiteral bitLengthLiteral = new IntegerLiteral(location, Integer.toString(1 << bitLength));
			final BinaryExpression binaryExpr3 = new BinaryExpression(location, Operator.ARITHMOD, identifierExpr,
					bitLengthLiteral);
			final VariableLHS varLhs3 = new VariableLHS(location, identifier);
			final AssignmentStatement assignment3 = new AssignmentStatement(location, new LeftHandSide[] { varLhs3 },
					new Expression[] { binaryExpr3 });
			result.addFuncBlock(assignment3);
		} else if (instructionType.uDivInst() != null) {
			final LLVMIRParser.ConcreteTypeContext typeContext = instructionType.uDivInst().typeValue().firstClassType()
					.concreteType();
			result.addFuncLocalVar(constructVarDecFromTypeContext(typeContext, identifier, result, location));
			final int bitLength = getBitLengthFromType(typeContext);
			final VariableLHS varLhs = new VariableLHS(location, identifier);
			final Expression leftExpr = constructExpressionFromValue(instructionType.uDivInst().typeValue().value(),
					typeContext, location);
			final Expression rightExpr = constructExpressionFromValue(instructionType.uDivInst().value(), typeContext,
					location);
			final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.ARITHDIV, leftExpr, rightExpr);
			final IntegerLiteral bitLengthLiteral = new IntegerLiteral(location, Integer.toString(1 << bitLength));
			final BinaryExpression signedExpr = new BinaryExpression(location, Operator.ARITHMOD, binaryExpr,
					bitLengthLiteral);
			final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
					new Expression[] { signedExpr });
			result.addFuncBlock(assignment);
		} else if (instructionType.uRemInst() != null) {
			final LLVMIRParser.ConcreteTypeContext typeContext = instructionType.uRemInst().typeValue().firstClassType()
					.concreteType();
			result.addFuncLocalVar(constructVarDecFromTypeContext(typeContext, identifier, result, location));
			final int bitLength = getBitLengthFromType(typeContext);
			final VariableLHS varLhs = new VariableLHS(location, identifier);
			final Expression leftExpr = constructExpressionFromValue(instructionType.uRemInst().typeValue().value(),
					typeContext, location);
			final Expression rightExpr = constructExpressionFromValue(instructionType.uRemInst().value(), typeContext,
					location);
			final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.ARITHMOD, leftExpr, rightExpr);
			final IntegerLiteral bitLengthLiteral = new IntegerLiteral(location, Integer.toString(1 << bitLength));
			final BinaryExpression signedExpr = new BinaryExpression(location, Operator.ARITHMOD, binaryExpr,
					bitLengthLiteral);
			final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
					new Expression[] { signedExpr });
			result.addFuncBlock(assignment);
		} else if (instructionType.sRemInst() != null) {
			final LLVMIRParser.ConcreteTypeContext typeContext = instructionType.sRemInst().typeValue().firstClassType()
					.concreteType();
			result.addFuncLocalVar(constructVarDecFromTypeContext(typeContext, identifier, result, location));
			final int bitLength = getBitLengthFromType(typeContext);
			final VariableLHS varLhs = new VariableLHS(location, identifier);
			final Expression leftExpr = constructExpressionFromValue(instructionType.sRemInst().typeValue().value(),
					typeContext, location);
			final Expression rightExpr = constructExpressionFromValue(instructionType.sRemInst().value(), typeContext,
					location);
			final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.ARITHMOD,
					createSignedExpression(leftExpr, bitLength, location),
					createSignedExpression(rightExpr, bitLength, location));
			final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
					new Expression[] { binaryExpr });
			result.addFuncBlock(assignment);

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
			result.addFuncBlock(ifStmt);

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
			result.addFuncBlock(ifStmt2);

			final IntegerLiteral bitLengthLiteral = new IntegerLiteral(location, Integer.toString(1 << bitLength));
			final BinaryExpression binaryExpr4 = new BinaryExpression(location, Operator.ARITHMOD, identifierExpr,
					bitLengthLiteral);
			final AssignmentStatement assignment2 = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
					new Expression[] { binaryExpr4 });
			result.addFuncBlock(assignment2);
		} else if (instructionType.subInst() != null) {
			final LLVMIRParser.ConcreteTypeContext typeContext = instructionType.subInst().typeValue().firstClassType()
					.concreteType();
			result.addFuncLocalVar(constructVarDecFromTypeContext(typeContext, identifier, result, location));
			final int bitLength = getBitLengthFromType(typeContext);
			final VariableLHS varLhs = new VariableLHS(location, identifier);
			final Expression leftExpr = constructExpressionFromValue(instructionType.subInst().typeValue().value(),
					typeContext, location);
			final Expression rightExpr = constructExpressionFromValue(instructionType.subInst().value(), typeContext,
					location);
			final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.ARITHMINUS, leftExpr,
					rightExpr);
			final IntegerLiteral bitLengthLiteral = new IntegerLiteral(location, Integer.toString(1 << bitLength));
			final BinaryExpression signedExpr = new BinaryExpression(location, Operator.ARITHMOD, binaryExpr,
					bitLengthLiteral);
			final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
					new Expression[] { signedExpr });
			result.addFuncBlock(assignment);
		} else if (instructionType.mulInst() != null) {
			final LLVMIRParser.ConcreteTypeContext typeContext = instructionType.mulInst().typeValue().firstClassType()
					.concreteType();
			result.addFuncLocalVar(constructVarDecFromTypeContext(typeContext, identifier, result, location));
			final int bitLength = getBitLengthFromType(typeContext);
			final VariableLHS varLhs = new VariableLHS(location, identifier);
			final Expression leftExpr = constructExpressionFromValue(instructionType.mulInst().typeValue().value(),
					typeContext, location);
			final Expression rightExpr = constructExpressionFromValue(instructionType.mulInst().value(), typeContext,
					location);
			final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.ARITHMUL, leftExpr, rightExpr);
			final IntegerLiteral bitLengthLiteral = new IntegerLiteral(location, Integer.toString(1 << bitLength));
			final BinaryExpression signedExpr = new BinaryExpression(location, Operator.ARITHMOD, binaryExpr,
					bitLengthLiteral);
			final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
					new Expression[] { signedExpr });
			result.addFuncBlock(assignment);
		} else if (instructionType.allocaInst() != null) {
			final LLVMIRParser.ConcreteTypeContext typeContext = instructionType.allocaInst().typeValue()
					.firstClassType().concreteType();
			result.addFuncLocalVar(constructVarDecFromTypeContext(typeContext, identifier, result, location));
		} else if (instructionType.callInst() != null) {
			final LLVMIRParser.TypeContext typeContext = instructionType.callInst().type();
			result.addFuncLocalVar(constructVarDecFromTypeContext(typeContext, identifier, result, location));
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
				result.addFuncBlock(havocStmt);
			} else {
				final ArrayList<Expression> args = new ArrayList<>();
				for (final LLVMIRParser.ArgContext arg : instructionType.callInst().args().arg()) {
					args.add(constructExpressionFromValue(arg.value(), typeContext, location));
				}
				final VariableLHS varLhs = new VariableLHS(location, identifier);
				final CallStatement callStmt = new CallStatement(location, false, new VariableLHS[] { varLhs },
						unifyIdentifier(callIdentifier), args.toArray(Expression[]::new));
				result.addFuncBlock(callStmt);
			}
		} else if (instructionType.selectInst() != null) {
			final LLVMIRParser.ConcreteTypeContext typeContext0 = instructionType.selectInst().typeValue(0)
					.firstClassType().concreteType();
			final LLVMIRParser.ConcreteTypeContext typeContext1 = instructionType.selectInst().typeValue(1)
					.firstClassType().concreteType();

			final Expression ifExpr = constructExpressionFromValue(instructionType.selectInst().typeValue(0).value(),
					typeContext0, location);
			final Expression thenExpr = constructExpressionFromValue(instructionType.selectInst().typeValue(1).value(),
					typeContext1, location);
			final Expression elseExpr = constructExpressionFromValue(instructionType.selectInst().typeValue(2).value(),
					typeContext1, location);
			result.addFuncLocalVar(constructVarDecFromTypeContext(typeContext1, identifier, result, location));
			final VariableLHS thenVarLhs = new VariableLHS(location, identifier);
			final VariableLHS elseVarLhs = new VariableLHS(location, identifier);
			final AssignmentStatement thenAssignment = new AssignmentStatement(location,
					new LeftHandSide[] { thenVarLhs }, new Expression[] { thenExpr });
			final AssignmentStatement elseAssignment = new AssignmentStatement(location,
					new LeftHandSide[] { elseVarLhs }, new Expression[] { elseExpr });
			final IfStatement ifStmt = new IfStatement(location, ifExpr, new Statement[] { thenAssignment },
					new Statement[] { elseAssignment });
			result.addFuncBlock(ifStmt);
		} else if (instructionType.andInst() != null) {
			createHavocStatementFromTypeValue(result, instructionType.addInst().typeValue(), location, identifier);
		} else if (instructionType.orInst() != null) {
			createHavocStatementFromTypeValue(result, instructionType.orInst().typeValue(), location, identifier);
		} else if (instructionType.xorInst() != null) {
			createHavocStatementFromTypeValue(result, instructionType.xorInst().typeValue(), location, identifier);
		} else if (instructionType.shlInst() != null) {
			createHavocStatementFromTypeValue(result, instructionType.shlInst().typeValue(), location, identifier);
		} else if (instructionType.aShrInst() != null) {
			createHavocStatementFromTypeValue(result, instructionType.aShrInst().typeValue(), location, identifier);
		} else if (instructionType.lShrInst() != null) {
			createHavocStatementFromTypeValue(result, instructionType.lShrInst().typeValue(), location, identifier);
		} else {
			throw new AssertionError("The support for the given instruction is not implemented yet.");
		}
		return result;
	}

	/**
	 * Handles the visit event for a branch terminator in the LLVM IR parse tree.
	 *
	 * This method processes the branch terminator and creates a GotoStatement to jump to the specified label.
	 *
	 * @param ctx The parse tree context for the branch terminator.
	 * @return A Result object containing the GotoStatement.
	 */
	@Override
	public Result visitBrTerm(final LLVMIRParser.BrTermContext ctx) {
		final LlvmirLocation location = new LlvmirLocation(mFilename, ctx.getStart().getLine(), ctx.getStop().getLine(),
				ctx.getStart().getCharPositionInLine(), ctx.getStop().getCharPositionInLine());
		final Result result = new Result();
		final String labelIdentifier = unifyIdentifier(ctx.label().LocalIdent().getText());
		final GotoStatement gotoStmt = new GotoStatement(location, new String[] { labelIdentifier });
		result.addFuncBlock(gotoStmt);

		return result;
	}

	/**
	 * Handles the visit event for a conditional branch terminator in the LLVM IR parse tree.
	 *
	 * This method processes the conditional branch terminator and creates an IfStatement to handle the condition, along
	 * with GotoStatements for the true and false branches.
	 *
	 * @param ctx The parse tree context for the conditional branch terminator.
	 * @return A Result object containing the IfStatement and GotoStatements.
	 */
	@Override
	public Result visitCondBrTerm(final LLVMIRParser.CondBrTermContext ctx) {
		final LlvmirLocation location = new LlvmirLocation(mFilename, ctx.getStart().getLine(), ctx.getStop().getLine(),
				ctx.getStart().getCharPositionInLine(), ctx.getStop().getCharPositionInLine());
		final Result result = new Result();

		final String variableIdentifier = unifyIdentifier(ctx.value().LocalIdent().getText());
		final String thenLabelIdentifier = unifyIdentifier(ctx.label(0).LocalIdent().getText());
		final String elseLabelIdentifier = unifyIdentifier(ctx.label(1).LocalIdent().getText());
		final GotoStatement thenGoto = new GotoStatement(location, new String[] { thenLabelIdentifier });
		final GotoStatement elseGoto = new GotoStatement(location, new String[] { elseLabelIdentifier });
		final IdentifierExpression variableExpr = new IdentifierExpression(location, variableIdentifier);
		final IfStatement ifStmt = new IfStatement(location, variableExpr, new Statement[] { thenGoto },
				new Statement[] { elseGoto });
		result.addFuncBlock(ifStmt);

		return result;
	}

	/**
	 * Handles the visit event for a store instruction in the LLVM IR parse tree.
	 *
	 * This method processes the store instruction and creates an AssignmentStatement to assign a value to a variable.
	 *
	 * @param ctx The parse tree context for the store instruction.
	 * @return A Result object containing the AssignmentStatement.
	 */
	@Override
	public Result visitStoreInst(final LLVMIRParser.StoreInstContext ctx) {
		final Result result = new Result();
		final LlvmirLocation location = new LlvmirLocation(mFilename, ctx.getStart().getLine(), ctx.getStop().getLine(),
				ctx.getStart().getCharPositionInLine(), ctx.getStop().getCharPositionInLine());

		final String identifier = unifyIdentifier(ctx.typeValue(1).value().LocalIdent().getText());
		final VariableLHS varLhs = new VariableLHS(location, identifier);
		final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
				new Expression[] { constructExpressionFromValue(ctx.typeValue(0).value(),
						ctx.typeValue(0).firstClassType().concreteType(), location) });
		result.addFuncBlock(assignment);

		return result;
	}

	/**
	 * Handles the visit event for a call instruction in the LLVM IR parse tree.
	 *
	 * This method processes the call instruction and creates a CallStatement or an AssertStatement based on the called
	 * function.
	 *
	 * @param ctx The parse tree context for the call instruction.
	 * @return A Result object containing the CallStatement or AssertStatement.
	 */
	@Override
	public Result visitCallInst(final LLVMIRParser.CallInstContext ctx) {
		final Result result = new Result();
		final LlvmirLocation location = new LlvmirLocation(mFilename, ctx.getStart().getLine(), ctx.getStop().getLine(),
				ctx.getStart().getCharPositionInLine(), ctx.getStop().getCharPositionInLine());

		final String callIdentifier = ctx.value().constant().getText();
		if (callIdentifier.equals("@__assert_fail") || callIdentifier.equals("@__VERIFIER_error")) {
			final BooleanLiteral boolLit = new BooleanLiteral(location, false);
			final AssertStatement assertStmt = new AssertStatement(location, new NamedAttribute[] {}, boolLit);
			final Check chk = new Check(Spec.ASSERT);
			chk.annotate(assertStmt);
			result.addFuncBlock(assertStmt);
		} else if (callIdentifier.equals("@printf")) {
			// This call can be ignored as it is not relevant for the Boogie translation
		} else {
			final ArrayList<Expression> args = new ArrayList<>();
			for (final LLVMIRParser.ArgContext arg : ctx.args().arg()) {
				args.add(constructExpressionFromValue(arg.value(), arg.concreteType(), location));
			}
			final CallStatement callStmt = new CallStatement(location, false, new VariableLHS[] {},
					unifyIdentifier(callIdentifier), args.toArray(Expression[]::new));
			result.addFuncBlock(callStmt);
		}

		return result;
	}
}
