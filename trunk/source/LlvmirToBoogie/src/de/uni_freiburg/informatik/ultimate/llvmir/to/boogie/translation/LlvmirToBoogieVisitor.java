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

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Optional;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.tree.ParseTree;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
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
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionDeclaration;
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
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogiePrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
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
	private final static String mLabelIdentifier = "aux#label";
	private final static String mUndefIdentifier = "aux#undef";
	private final static String mCDivIdentifier = "aux#cdiv";
	private final static String mRemIdentifier = "aux#rem";

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
		if (result.startsWith("aux#")) {
			return result;
		} else if (Character.isLetterOrDigit(firstChar)) {
			return '#' + result;
		}
		return '#' + result.substring(1);
	}

	/**
	 * Constructs a location object from the given context.
	 *
	 * This method creates a LlvmirLocation object that represents the location of a specific context in the source
	 * code. It uses the filename, line numbers, and character positions from the context to create the location.
	 *
	 * @param ctx The ParserRuleContext from which to extract the location information.
	 * @return A LlvmirLocation object representing the location in the source code.
	 */
	private LlvmirLocation constructLocation(final ParserRuleContext ctx) {
		return new LlvmirLocation(mFilename, ctx.getStart().getLine(), ctx.getStop().getLine(),
				ctx.getStart().getCharPositionInLine(), ctx.getStop().getCharPositionInLine());
	}

	/**
	 * Constructs a specification from a given identifier and location.
	 *
	 * This method constructs a ModifiesSpecification that indicates the specified variable is modified in the Boogie
	 * AST.
	 *
	 * @param identifier The identifier of the variable to be modified.
	 * @param location   The location in the source code where this specification is defined.
	 * @return A ModifiesSpecification object representing the modifies specification for the given identifier.
	 */
	private static ModifiesSpecification constructSpecFromIdentifier(final String identifier,
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
	 * Constructs initial declarations for global variables and the ULTIMATE.start procedure.
	 *
	 * This method initializes the global variables and constructs the ULTIMATE.start procedure that will be executed at
	 * the start of the program. It also constructs an aux#init procedure for global variable initialization.
	 *
	 * Using addFirst ensures that the initial declarations are at the beginning of the Boogie AST unit.
	 */
	private void constructInitialDeclarations() {
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

		final String initIdentifier = "aux#init";
		mDeclarations.addFirst(constructInitialProcedure(mLocation, initIdentifier, new VariableDeclaration[] {},
				stmts.toArray(Statement[]::new), specs.toArray(Specification[]::new)));
		final CallStatement initCall = new CallStatement(mLocation, false, new VariableLHS[] {}, initIdentifier,
				new Expression[] {});

		VariableLHS[] lhsVars;
		VariableDeclaration[] varDecls;
		final String mainReturnType = getMainReturnType();
		if (mainReturnType.equals("void")) {
			lhsVars = new VariableLHS[] {};
			varDecls = new VariableDeclaration[] {};
		} else {
			final String tmpVarIdentifier = "aux#tmp";
			final VariableLHS varLhs = new VariableLHS(mLocation, tmpVarIdentifier);
			lhsVars = new VariableLHS[] { varLhs };
			varDecls = new VariableDeclaration[] {
					constructVarDecFromString(mainReturnType, tmpVarIdentifier, mLocation) };
		}
		final CallStatement mainCall = new CallStatement(mLocation, false, lhsVars, "#main", new Expression[] {});

		mDeclarations.addFirst(constructInitialProcedure(mLocation, "ULTIMATE.start", varDecls,
				new Statement[] { initCall, mainCall }, specs.toArray(Specification[]::new)));

		mDeclarations.addAll(0, decls);
	}

	/**
	 * Retrieves the return type of the #main procedure.
	 *
	 * This method searches for the #main procedure in the declarations and returns its return type as a String. If no
	 * such procedure is found, it throws an IllegalStateException.
	 *
	 * @return The return type of the #main procedure.
	 * @throws IllegalStateException if no #main procedure is found in the declarations.
	 */
	private String getMainReturnType() throws IllegalStateException {
		final Procedure main = (Procedure) mDeclarations.stream()
				.filter(decl -> decl instanceof Procedure && ((Procedure) decl).getIdentifier().equals("#main"))
				.findFirst().orElseThrow(() -> new IllegalStateException("No #main declaration found"));
		final String retString = main.getOutParams().length > 0 ? main.getOutParams()[0].getType().toString() : "void";
		return retString.contains("int") ? "int" : retString.contains("bool") ? "bool" : "void";
	}

	/**
	 * Constructs a variable declaration from a type and identifier.
	 *
	 * This method constructs a VariableDeclaration object with the specified type and identifier, using the provided
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

	/**
	 * Constructs a variable declaration from a type context, identifier, and location.
	 *
	 * This method constructs a VariableDeclaration object based on the provided type context and identifier.
	 *
	 * @param typeContext The type context from which to extract the type information.
	 * @param identifier  The identifier for the variable.
	 * @param location    The location in the source code where this variable is declared.
	 * @return A VariableDeclaration object representing the variable declaration.
	 * @throws AssertionError if the type context is not supported or does not contain an intType.
	 */
	private static VariableDeclaration constructVarDecFromTypeContext(final ParserRuleContext typeContext,
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
	 * Constructs an expression from a value context, type context, and location.
	 *
	 * This method constructs an Expression based on the provided value context, type context, and location. It handles
	 * both local identifiers and constants, converting them into appropriate expressions.
	 *
	 * @param valueContext The context containing the value to be converted into an expression.
	 * @param typeContext  The context containing the type information for the value.
	 * @param location     The location in the source code where this value is defined.
	 * @param isSigned     Indicates whether the value should be treated as signed or unsigned.
	 * @return An Expression representing the value.
	 * @throws AssertionError if the value type is not supported.
	 */
	private static Expression constructExpressionFromValue(final LLVMIRParser.ValueContext valueContext,
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
	 * @param constantContext The context containing the constant value.
	 * @param typeContext     The context containing the type information for the constant.
	 * @param location        The location in the source code where this constant is defined.
	 * @param isSigned        Indicates whether the constant should be treated as signed or unsigned.
	 * @return An Expression representing the constant value.
	 * @throws AssertionError if the constant type is not supported.
	 */
	private static Expression constructExpressionFromConstant(final LLVMIRParser.ConstantContext constantContext,
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
			return new IdentifierExpression(location, mUndefIdentifier);
		}
		throw new AssertionError("Unsupported constant type: " + constantContext.getText());
	}

	/**
	 * Computes the euclidean modulus of a value based on the specified bit length and signedness.
	 *
	 * This method calculates the modulus of a given value with respect to a power of two, ensuring that the result is
	 * always non-negative. It handles both signed and unsigned integers by adjusting the modulus accordingly.
	 *
	 * @param value     The value for which to compute the modulus.
	 * @param bitLength The bit length to use for the modulus calculation.
	 * @param isSigned  Indicates whether the value is signed or unsigned.
	 * @return A BigInteger representing the non-negative modulus of the value.
	 */
	public static BigInteger euclideanMod(final BigInteger value, final int bitLength, final boolean isSigned) {
		final BigInteger modulus = BigInteger.ONE.shiftLeft(bitLength - (isSigned ? 1 : 0));
		return ((value.mod(modulus)).add(modulus)).mod(modulus);
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
	 * Constructs a bit length literal based on the provided bit length.
	 *
	 * This method creates an IntegerLiteral that represents (2^bitLength-isSigned).
	 *
	 * @param location  The location in the source code where this literal is defined.
	 * @param bitLength The bit length for which to construct the literal.
	 * @param isSigned  Indicates whether the bit length is for a signed integer.
	 * @return An IntegerLiteral representing (2^bitLength-isSigned).
	 * @throws AssertionError if the bit length is not a positive integer.
	 */
	private static IntegerLiteral constructBitLengthLiteral(final LlvmirLocation location, final int bitLength,
			final boolean isSigned) {
		if (bitLength <= 0) {
			throw new AssertionError("Bit length must be a positive integer.");
		}
		return new IntegerLiteral(location, BigInteger.ONE.shiftLeft(bitLength - (isSigned ? 1 : 0)).toString());
	}

	/**
	 * Constructs an identifier expression from a value context and type context.
	 *
	 * This method constructs an IdentifierExpression based on the provided value context and type context. It assumes
	 * that the value context contains a local identifier and uses the type context to determine the type of the
	 * identifier.
	 *
	 * @param location     The location in the source code where this identifier is defined.
	 * @param valueContext The context containing the value to be converted into an identifier expression.
	 * @param typeContext  The context containing the type information for the identifier.
	 * @return An IdentifierExpression representing the local identifier.
	 * @throws AssertionError if the value context does not contain a local identifier or if the contexts are null.
	 */
	private static IdentifierExpression constructIdentifierExpression(final LlvmirLocation location,
			final LLVMIRParser.ValueContext valueContext, final ParserRuleContext typeContext) throws AssertionError {
		if (valueContext == null || typeContext == null) {
			throw new AssertionError("Value context and type context must not be null.");
		}
		if (valueContext.LocalIdent() == null) {
			throw new AssertionError("Value context must contain a LocalIdent.");
		}

		final BoogiePrimitiveType type = typeContext.getText().equals("i1") ? BoogieType.TYPE_BOOL
				: BoogieType.TYPE_INT;
		final String operandName = valueContext.LocalIdent().getText();
		final DeclarationInformation.StorageClass storageClass = isParamInProcedure(unifyIdentifier(operandName),
				valueContext) ? DeclarationInformation.StorageClass.PROC_FUNC_INPARAM
						: DeclarationInformation.StorageClass.LOCAL;
		final String procedureIdentifier = getProcedureIdentifierFromContext(valueContext);
		final DeclarationInformation declInfo = new DeclarationInformation(storageClass, procedureIdentifier);
		return new IdentifierExpression(location, type, unifyIdentifier(operandName), declInfo);
	}

	/**
	 * Retrieves the procedure identifier from the context by traversing the parent hierarchy.
	 *
	 * This method searches for the nearest FuncDefContext in the parent hierarchy of the given context and extracts the
	 * procedure identifier from its FuncHeaderContext.
	 *
	 * @param ctx The context from which to start searching for the procedure identifier.
	 * @return The procedure identifier as a String.
	 * @throws AssertionError if the context is null or if no FuncDefContext or GlobalIdent is found.
	 */
	private static String getProcedureIdentifierFromContext(final ParserRuleContext ctx) throws AssertionError {
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
	 * @param identifier The identifier to check.
	 * @param ctx        The context from which to start searching for the function definition.
	 * @return true if the identifier is a parameter in the procedure; false otherwise.
	 * @throws AssertionError if the context or identifier is null or empty, or if no function definition is found.
	 */
	private static boolean isParamInProcedure(final String identifier, final ParserRuleContext ctx)
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
	 * @param ctx           The context from which to start searching for the function body.
	 * @param incIdentifier The identifier of the label to find.
	 * @return The index of the label in the function body.
	 * @throws AssertionError if the context or identifier is null or empty, or if no label is found.
	 */
	private static int getLabelIndexFromFuncBody(final ParserRuleContext ctx, final String incIdentifier)
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
	 * Constructs an assignment statement to assign a label index to the label variable.
	 *
	 * This method constructs an assignment statement that assigns the specified label index to the label variable
	 * identified by `mLabelIdentifier`.
	 *
	 * @param location   The location in the source code where this assignment occurs.
	 * @param labelIndex The index of the label to be assigned.
	 * @return An AssignmentStatement object representing the assignment.
	 */
	private static AssignmentStatement constructLabelAssignment(final LlvmirLocation location, final int labelIndex) {
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
	 * Constructs a havoc statement for arithmetic or logic instructions.
	 *
	 * This method generates a havoc statement for arithmetic or logic instructions based on the type of the
	 * instruction. It constructs a local variable with either "bool" or "int" type and adds a havoc statement to the
	 * result.
	 *
	 * @param result     The result to which the havoc statement will be added.
	 * @param typeValue  The type value context from the LLVM IR parse tree.
	 * @param location   The location in the source code where this instruction is defined.
	 * @param identifier The identifier for the local variable to be constructed.
	 */
	private static void constructHavocStatementFromTypeValue(final Result result,
			final LLVMIRParser.TypeValueContext typeValue, final LlvmirLocation location, final String identifier,
			final String reason) {
		final LLVMIRParser.ConcreteTypeContext tpyeContext = typeValue.firstClassType().concreteType();
		result.addFuncLocalVar(constructVarDecFromTypeContext(tpyeContext, identifier, location));
		final VariableLHS varLhs = new VariableLHS(location, identifier);
		final HavocStatement havocStmt = new HavocStatement(location, new VariableLHS[] { varLhs });
		final Overapprox overapprox = new Overapprox(reason, location);
		overapprox.annotate(havocStmt);
		result.addFuncBlock(havocStmt);
	}

	/**
	 * Constructs an expression that converts an unsigned integer to a signed integer based on the specified bit length.
	 *
	 * This method checks if the given expression is greater than or equal to the maximum value for the specified bit
	 * length. If it is, it subtracts the maximum value from the expression to convert it to a signed representation.
	 *
	 * @param expr      The expression to be converted.
	 * @param bitLength The bit length for the conversion.
	 * @param location  The location in the source code where this conversion occurs.
	 * @return An IfThenElseExpression representing the signed conversion.
	 */
	private static Expression constructSignedExpression(final Expression expr, final int bitLength,
			final LlvmirLocation location) {
		final IntegerLiteral maxValueLiteral = new IntegerLiteral(location,
				BigInteger.ONE.shiftLeft(bitLength - 1).subtract(BigInteger.ONE).toString());
		final IntegerLiteral bitLengthLiteral = new IntegerLiteral(location,
				BigInteger.ONE.shiftLeft(bitLength).toString());
		final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.COMPGT, expr, maxValueLiteral);
		final BinaryExpression thenExpr = new BinaryExpression(location, Operator.ARITHMINUS, expr, bitLengthLiteral);
		final IfThenElseExpression ifThenElseExpr = new IfThenElseExpression(location, binaryExpr, thenExpr, expr);
		return ifThenElseExpr;
	}

	/**
	 * Retrieves a Procedure object from the list of declarations based on the given identifier.
	 *
	 * @param identifier   The identifier of the procedure to retrieve.
	 * @param declarations The list of declarations to search.
	 * @return The Procedure object corresponding to the identifier.
	 * @throws AssertionError if no procedure with the given identifier is found.
	 */
	private static Procedure getProcedureFromDeclarations(final String identifier,
			final ArrayList<Declaration> declarations) throws AssertionError {
		return declarations.stream().filter(dec -> dec instanceof Procedure).map(dec -> (Procedure) dec)
				.filter(proc -> proc.getIdentifier().equals(identifier)).findFirst()
				.orElseThrow(() -> new AssertionError("Procedure with identifier '" + identifier + "' not found."));
	}

	/**
	 * Constructs the aux#cdiv function for signed and unsigned integer division.
	 *
	 * This method creates a FunctionDeclaration for the aux#cdiv function, which performs division while handling
	 * signedness and absolute values. It takes into account various cases of operand signs to ensure correct division
	 * results.
	 *
	 * @param location The location in the source code where this function is defined.
	 * @return A FunctionDeclaration representing the aux#cdiv function.
	 */
	private static FunctionDeclaration constructCDivFunction(final LlvmirLocation location) {
		final String xIdentifier = "aux#x";
		final String yIdentifier = "aux#y";
		final String maxFromBitLengthIdentifier = "aux#maxFromBitLength";
		final String isSignedIdentifier = "aux#isSigned";

		final Expression xExpr = new IdentifierExpression(location, xIdentifier);
		final Expression yExpr = new IdentifierExpression(location, yIdentifier);
		final Expression maxFromBitLengthExpr = new IdentifierExpression(location, maxFromBitLengthIdentifier);
		final Expression isSignedExpr = new IdentifierExpression(location, isSignedIdentifier);
		final Expression zeroExpr = new IntegerLiteral(location, "0");

		final Expression signedPlusOneExpr = new BinaryExpression(location, Operator.ARITHPLUS, isSignedExpr,
				new IntegerLiteral(location, "1"));
		final Expression signedMaxFromBitLengthExpr = new BinaryExpression(location, Operator.ARITHDIV,
				maxFromBitLengthExpr, signedPlusOneExpr);

		final Expression xNonNeg = new BinaryExpression(location, Operator.COMPLT, xExpr, signedMaxFromBitLengthExpr);
		final Expression yNonNeg = new BinaryExpression(location, Operator.COMPLT, yExpr, signedMaxFromBitLengthExpr);
		final Expression xIsNeg = new BinaryExpression(location, Operator.COMPGEQ, xExpr, signedMaxFromBitLengthExpr);
		final Expression yIsNeg = new BinaryExpression(location, Operator.COMPGEQ, yExpr, signedMaxFromBitLengthExpr);

		final BinaryExpression xAbs = new BinaryExpression(location, Operator.ARITHMINUS, maxFromBitLengthExpr, xExpr);
		final BinaryExpression yAbs = new BinaryExpression(location, Operator.ARITHMINUS, maxFromBitLengthExpr, yExpr);

		final Expression noneAbsdivExpr = new BinaryExpression(location, Operator.ARITHDIV, xExpr, yExpr);
		final Expression bothAbsDivExpr = new BinaryExpression(location, Operator.ARITHDIV, xAbs, yAbs);
		final Expression xAbsDivExpr = new BinaryExpression(location, Operator.ARITHDIV, xAbs, yExpr);
		final Expression yAbsDivExpr = new BinaryExpression(location, Operator.ARITHDIV, xExpr, yAbs);

		final Expression bothNonNeg = new BinaryExpression(location, Operator.LOGICAND, xNonNeg, yNonNeg);
		final Expression bothNeg = new BinaryExpression(location, Operator.LOGICAND, xIsNeg, yIsNeg);

		final Expression resultIsNeg = new IfThenElseExpression(location, xIsNeg, xAbsDivExpr, yAbsDivExpr);
		final Expression negatedResult = new BinaryExpression(location, Operator.ARITHMINUS, zeroExpr, resultIsNeg);

		final Expression resultIsPosBothNeg = new IfThenElseExpression(location, bothNeg, bothAbsDivExpr,
				negatedResult);

		final Expression resultIsPosNoneNeg = new IfThenElseExpression(location, bothNonNeg, noneAbsdivExpr,
				resultIsPosBothNeg);

		final ArrayList<VarList> inParams = new ArrayList<>();
		final PrimitiveType intTypePrim = new PrimitiveType(location, "int");
		final VarList varListX = new VarList(location, new String[] { xIdentifier }, intTypePrim);
		inParams.add(varListX);
		final VarList varListY = new VarList(location, new String[] { yIdentifier }, intTypePrim);
		inParams.add(varListY);
		final VarList varListBitLength = new VarList(location, new String[] { maxFromBitLengthIdentifier },
				intTypePrim);
		inParams.add(varListBitLength);
		// isSigned is 1 if signed, 0 if unsigned
		final VarList varListIsSigned = new VarList(location, new String[] { isSignedIdentifier }, intTypePrim);
		inParams.add(varListIsSigned);

		final VarList outParam = new VarList(location, new String[] {}, intTypePrim);

		return new FunctionDeclaration(location, new Attribute[] {}, mCDivIdentifier, new String[] {},
				inParams.toArray(VarList[]::new), outParam, resultIsPosNoneNeg);
	}

	/**
	 * Constructs the aux#rem function for signed and unsigned integer remainder.
	 *
	 * This method creates a FunctionDeclaration for the aux#rem function, which computes the remainder while handling
	 * signedness and absolute values. It takes into account various cases of operand signs to ensure correct remainder
	 * results.
	 *
	 * @param location The location in the source code where this function is defined.
	 * @return A FunctionDeclaration representing the aux#rem function.
	 */
	private static FunctionDeclaration contructRemainderFunction(final LlvmirLocation location) {
		final String xIdentifier = "aux#x";
		final String yIdentifier = "aux#y";
		final String maxFromBitLengthIdentifier = "aux#maxFromBitLength";
		final String isSignedIdentifier = "aux#isSigned";

		final Expression xExpr = new IdentifierExpression(location, xIdentifier);
		final Expression yExpr = new IdentifierExpression(location, yIdentifier);
		final Expression maxFromBitLengthExpr = new IdentifierExpression(location, maxFromBitLengthIdentifier);
		final Expression isSignedExpr = new IdentifierExpression(location, isSignedIdentifier);
		final Expression zeroExpr = new IntegerLiteral(location, "0");

		final Expression signedPlusOneExpr = new BinaryExpression(location, Operator.ARITHPLUS, isSignedExpr,
				new IntegerLiteral(location, "1"));
		final Expression signedMaxFromBitLengthExpr = new BinaryExpression(location, Operator.ARITHDIV,
				maxFromBitLengthExpr, signedPlusOneExpr);

		final FunctionApplication cdivCall = new FunctionApplication(location, mCDivIdentifier,
				new Expression[] { xExpr, yExpr, maxFromBitLengthExpr, isSignedExpr });

		final Expression xNonNeg = new BinaryExpression(location, Operator.COMPLT, xExpr, signedMaxFromBitLengthExpr);
		final Expression yNonNeg = new BinaryExpression(location, Operator.COMPLT, yExpr, signedMaxFromBitLengthExpr);
		final Expression xIsNeg = new BinaryExpression(location, Operator.COMPGEQ, xExpr, signedMaxFromBitLengthExpr);
		final Expression yIsNeg = new BinaryExpression(location, Operator.COMPGEQ, yExpr, signedMaxFromBitLengthExpr);

		final BinaryExpression xAbs = new BinaryExpression(location, Operator.ARITHMINUS, maxFromBitLengthExpr, xExpr);
		final BinaryExpression yAbs = new BinaryExpression(location, Operator.ARITHMINUS, maxFromBitLengthExpr, yExpr);
		final BinaryExpression xValue = new BinaryExpression(location, Operator.ARITHMINUS, xExpr,
				maxFromBitLengthExpr);
		final BinaryExpression yValue = new BinaryExpression(location, Operator.ARITHMINUS, yExpr,
				maxFromBitLengthExpr);

		final BinaryExpression yMulCdiv = new BinaryExpression(location, Operator.ARITHMUL, yExpr, cdivCall);
		final BinaryExpression yAbsMulCdiv = new BinaryExpression(location, Operator.ARITHMUL, yAbs, cdivCall);
		final BinaryExpression yValueMulCdiv = new BinaryExpression(location, Operator.ARITHMUL, yValue, cdivCall);

		final BinaryExpression xMinusYMulCdiv = new BinaryExpression(location, Operator.ARITHMINUS, xExpr, yMulCdiv);
		final BinaryExpression xAbsMinusYAbsMulCdiv = new BinaryExpression(location, Operator.ARITHMINUS, xAbs,
				yAbsMulCdiv);
		final BinaryExpression negatedXAbsMinusYAbsMulCdiv = new BinaryExpression(location, Operator.ARITHMINUS,
				zeroExpr, xAbsMinusYAbsMulCdiv);
		final BinaryExpression xValueMinusYMulCdiv = new BinaryExpression(location, Operator.ARITHMINUS, xValue,
				yMulCdiv);
		final BinaryExpression xMinusYValueMulCdiv = new BinaryExpression(location, Operator.ARITHMINUS, xExpr,
				yValueMulCdiv);

		final Expression bothNonNeg = new BinaryExpression(location, Operator.LOGICAND, xNonNeg, yNonNeg);
		final Expression bothNeg = new BinaryExpression(location, Operator.LOGICAND, xIsNeg, yIsNeg);

		final Expression resultOneNeg = new IfThenElseExpression(location, xIsNeg, xValueMinusYMulCdiv,
				xMinusYValueMulCdiv);
		final Expression resultBothNeg = new IfThenElseExpression(location, bothNeg, negatedXAbsMinusYAbsMulCdiv,
				resultOneNeg);
		final Expression resultNoneNeg = new IfThenElseExpression(location, bothNonNeg, xMinusYMulCdiv, resultBothNeg);

		final ArrayList<VarList> inParams = new ArrayList<>();
		final PrimitiveType intTypePrim = new PrimitiveType(location, "int");
		final VarList varListX = new VarList(location, new String[] { xIdentifier }, intTypePrim);
		inParams.add(varListX);
		final VarList varListY = new VarList(location, new String[] { yIdentifier }, intTypePrim);
		inParams.add(varListY);
		final VarList varListBitLength = new VarList(location, new String[] { maxFromBitLengthIdentifier },
				intTypePrim);
		inParams.add(varListBitLength);
		// isSigned is 1 if signed, 0 if unsigned
		final VarList varListIsSigned = new VarList(location, new String[] { isSignedIdentifier }, intTypePrim);
		inParams.add(varListIsSigned);

		final VarList outParam = new VarList(location, new String[] {}, intTypePrim);

		return new FunctionDeclaration(location, new Attribute[] {}, mRemIdentifier, new String[] {},
				inParams.toArray(VarList[]::new), outParam, resultNoneNeg);
	}

	/**
	 * This method searches the list of declarations for a TypeDeclaration with an identifier matching the format
	 * "i{bitLength}Pair".
	 *
	 * @param bitLength    The bit length to check for.
	 * @param declarations The list of declarations to search.
	 * @return true if a matching TypeDeclaration exists, false otherwise.
	 */
	public static boolean bitLengthPairExists(final int bitLength, final ArrayList<Declaration> declarations) {
		final Optional<TypeDeclaration> typeDec = declarations.stream().filter(dec -> dec instanceof TypeDeclaration)
				.map(dec -> (TypeDeclaration) dec)
				.filter(typeDecl -> typeDecl.getIdentifier().equals("i" + bitLength + "Pair")).findFirst();
		return typeDec.isPresent();
	}

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
	 * Constructs a variable declaration and an assignment statement for an LLVM operation with overflow handling.
	 *
	 * This method creates a VariableDeclaration for a struct type that holds the result of the operation and an
	 * overflow flag. It also constructs an AssignmentStatement that assigns the result of the operation and the
	 * overflow status to the struct fields.
	 *
	 * @param operation  The expression representing the LLVM operation.
	 * @param bitLength  The bit length of the integer type involved in the operation.
	 * @param isSigned   Indicates whether the integer type is signed or unsigned.
	 * @param Identifier The identifier for the variable to be declared and assigned.
	 * @param location   The location in the source code where this operation occurs.
	 * @return A Pair containing the VariableDeclaration and AssignmentStatement.
	 */
	public static Pair<VariableDeclaration, AssignmentStatement> constructLlvmOperationWithOverflow(
			final Expression operation, final int bitLength, final boolean isSigned, final String Identifier,
			final LlvmirLocation location) {
		final NamedType namedType = new NamedType(location, "i" + bitLength + "Pair", new ASTType[] {});
		final VarList varList = new VarList(location, new String[] { Identifier }, namedType);
		final VariableDeclaration varDec = new VariableDeclaration(location, new Attribute[] {},
				new VarList[] { varList });

		final String[] fieldIdentifiers = { "e0", "e1" };
		final Expression[] fieldValues = {};
		final IntegerLiteral bitLengthLiteral = constructBitLengthLiteral(location, bitLength, false);
		final BinaryExpression binaryExpr1 = new BinaryExpression(location, Operator.ARITHMOD, operation,
				bitLengthLiteral);
		fieldValues[0] = binaryExpr1;

		final IntegerLiteral signedBitLengthLiteral = constructBitLengthLiteral(location, bitLength, isSigned);
		final BinaryExpression binaryExpr2 = new BinaryExpression(location, Operator.COMPGT, operation,
				signedBitLengthLiteral);

		final Expression expr = isSigned
				? new UnaryExpression(location, UnaryExpression.Operator.ARITHNEGATIVE, signedBitLengthLiteral)
				: new IntegerLiteral(location, "0");
		final BinaryExpression binaryExpr3 = new BinaryExpression(location, Operator.ARITHPLUS, operation, expr);

		final BinaryExpression binaryExpr4 = new BinaryExpression(location, Operator.LOGICOR, binaryExpr2, binaryExpr3);
		fieldValues[1] = binaryExpr4;

		final StructConstructor structConstructor = new StructConstructor(location, fieldIdentifiers, fieldValues);
		final VariableLHS varLhs = new VariableLHS(location, Identifier);
		final AssignmentStatement assignmentStmt = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
				new Expression[] { structConstructor });

		return new Pair<>(varDec, assignmentStmt);
	}

	/**
	 * Checks if a procedure with the same signature already exists in the list of declarations.
	 *
	 * This method compares the identifier, input parameters, and output parameters of the given procedure with those in
	 * the list of declarations to determine if an identical procedure is already present.
	 *
	 * @param procedure    The procedure to check for duplicates.
	 * @param declarations The list of declarations to search.
	 * @return true if an identical procedure is found, false otherwise.
	 */
	private static boolean procedureAlreadyPresent(final Procedure procedure,
			final ArrayList<Declaration> declarations) {
		return declarations.stream().filter(dec -> dec instanceof Procedure).map(dec -> (Procedure) dec)
				.anyMatch(proc -> {
					if (!proc.getIdentifier().equals(procedure.getIdentifier())) {
						return false;
					}
					if (proc.getInParams().length != procedure.getInParams().length) {
						return false;
					}
					for (int i = 0; i < proc.getInParams().length; i++) {
						for (int j = 0; j < proc.getInParams()[i].getIdentifiers().length; j++) {
							if (!proc.getInParams()[i].getIdentifiers()[j]
									.equals(procedure.getInParams()[i].getIdentifiers()[j])) {
								return false;
							}
							if (!proc.getInParams()[i].getType().equals(procedure.getInParams()[i].getType())) {
								return false;
							}
						}
					}
					for (int i = 0; i < proc.getOutParams().length; i++) {
						for (int j = 0; j < proc.getOutParams()[i].getIdentifiers().length; j++) {
							if (!proc.getOutParams()[i].getIdentifiers()[j]
									.equals(procedure.getOutParams()[i].getIdentifiers()[j])) {
								return false;
							}
							if (!proc.getOutParams()[i].getType().equals(procedure.getOutParams()[i].getType())) {
								return false;
							}
						}
					}
					return true;
				});
	}

	/**
	 * Handles the visit event for the compilation unit in the LLVM IR parse tree.
	 *
	 * This method initializes the location and processes the children of the compilation unit context to construct
	 * declarations and the final Boogie AST unit.
	 *
	 * @param ctx The parse tree context for the compilation unit.
	 * @return A Result object containing the final Boogie AST unit.
	 */
	@Override
	public Result visitCompilationUnit(final LLVMIRParser.CompilationUnitContext ctx) {
		mLocation = constructLocation(ctx);
		mDeclarations.add(constructCDivFunction(mLocation));
		mDeclarations.add(contructRemainderFunction(mLocation));

		ParseTree mainFunc = null;

		for (final ParseTree child : ctx.children) {
			if (!(child.getChild(0) instanceof LLVMIRParser.FuncDefContext)) {
				visit(child); // visit non-function definitions immediately
				continue;
			}

			final LLVMIRParser.FuncDefContext funcDef = (LLVMIRParser.FuncDefContext) child.getChild(0);
			final String funcName = funcDef.funcHeader().GlobalIdent().getText();

			if ("@main".equals(funcName)) {
				mainFunc = child;
			} else {
				visit(child); // visit non-main immediately
			}
		}

		// process main last
		if (mainFunc != null) {
			visit(mainFunc);
		}

		constructInitialDeclarations();
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

		final LlvmirLocation location = constructLocation(ctx);

		final Body body = new Body(location, result.getFuncLocalVars().toArray(VariableDeclaration[]::new),
				result.getFuncBlock().toArray(Statement[]::new));
		final ArrayList<Attribute> attributes = new ArrayList<>();
		final ArrayList<String> typeParams = new ArrayList<>();
		final ArrayList<VarList> inParams = new ArrayList<>();
		final ArrayList<VarList> outParams = new ArrayList<>();

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
				result.getFuncModifiedGlobalVars().toArray(Specification[]::new), body);

		if (!procedureAlreadyPresent(procedure, mDeclarations)) {
			mDeclarations.add(procedure);
		}

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
	 * This method processes the basic block context, constructs a label for it, and processes its children to generate
	 * statements for the Boogie AST. It also handles terminators like conditional and unconditional branches.
	 *
	 * @param ctx The parse tree context for the basic block.
	 * @return A Result object containing the generated statements for the basic block.
	 */
	@Override
	public Result visitBasicBlock(final LLVMIRParser.BasicBlockContext ctx) {
		final LlvmirLocation location = constructLocation(ctx);
		final Result result = new Result();

		final LLVMIRParser.FuncBodyContext funcBodyCtx = (LLVMIRParser.FuncBodyContext) ctx.getParent();
		final List<LLVMIRParser.BasicBlockContext> blocks = funcBodyCtx.basicBlock();
		final int index = blocks.indexOf(ctx);

		final String labelName = unifyIdentifier(ctx.LabelIdent().getText());
		final Label label = new Label(location, labelName, new NamedAttribute[] {});
		result.addFuncBlock(label);

		for (final ParseTree child : ctx.children) {
			// If the child is a branching term (CondBrTerm or BrTerm), we add an assignment to the label variable, it
			// is necessary to know the last visited label to properly handle phi instructions.
			if (child.getChild(0) instanceof LLVMIRParser.CondBrTermContext
					|| child.getChild(0) instanceof LLVMIRParser.BrTermContext) {
				result.addFuncBlock(constructLabelAssignment(location, index));
			}
			final Result childResult = child.accept(this);
			if (childResult != null) {
				result.merge(childResult);
			}
		}

		// If this is not the last block, we add an assignment to the label variable, it is necessary to know the last
		// visited label to properly handle phi instructions.
		if (!(index == blocks.size() - 1)) {
			result.addFuncBlock(constructLabelAssignment(location, index));
		}

		return result;
	}

	/**
	 * Handles the visit event for a return term in the LLVM IR parse tree.
	 *
	 * This method processes the return statement, handling both void returns and returns with values. It constructs
	 * appropriate Boogie statements based on the return type.
	 *
	 * @param ctx The parse tree context for the return term.
	 * @return A Result object containing the generated statements for the return term.
	 * @throws AssertionError if the return type is not supported.
	 */
	@Override
	public Result visitRetTerm(final LLVMIRParser.RetTermContext ctx) throws AssertionError {
		final Result result = new Result();
		final LlvmirLocation location = constructLocation(ctx);

		if (ctx.value() == null) {
			// If there is no value, we assume a void return type
			final ReturnStatement returnStmt = new ReturnStatement(location);
			result.addFuncBlock(returnStmt);
		} else {
			final LLVMIRParser.ConcreteTypeContext returnType = ctx.concreteType();
			if (returnType.intType() == null) {
				throw new AssertionError("The support for return types other than integers is not implemented yet.");
			}
			final VariableLHS returnVar = new VariableLHS(location, "ret");
			final AssignmentStatement assignmentStmt = new AssignmentStatement(location,
					new LeftHandSide[] { returnVar },
					new Expression[] { constructExpressionFromValue(ctx.value(), returnType, location, false) });
			final ReturnStatement returnStmt = new ReturnStatement(location);
			result.addFuncBlocks(Arrays.asList(assignmentStmt, returnStmt));
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
		final LlvmirLocation location = constructLocation(ctx);

		if (type.intType() == null) {
			throw new AssertionError("The support for types other than integers is not implemented yet.");
		}

		final String typeString = type.intType().getText().equals("i1") ? "bool" : "int";
		final VariableDeclaration varDecl = constructVarDecFromString(typeString, identifier, location);

		final VariableLHS varLhs = new VariableLHS(location, identifier);
		final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
				new Expression[] { constructExpressionFromConstant(ctx.constant(), type, location, false) });

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
		final LlvmirLocation location = constructLocation(ctx);

		if (instructionType.loadInst() != null) {
			final LLVMIRParser.TypeContext variableType = instructionType.loadInst().type();
			if (variableType.intType() == null) {
				throw new AssertionError(
						"The support for types other than integers in load instructions is not implemented yet.");
			}
			result.addFuncLocalVar(constructVarDecFromTypeContext(variableType, identifier, location));
			final VariableLHS varLhs = new VariableLHS(location, identifier);

			String loadVarIdentifier = null;
			if (instructionType.loadInst().typeValue().value().LocalIdent() != null) {
				loadVarIdentifier = unifyIdentifier(
						instructionType.loadInst().typeValue().value().LocalIdent().getText());
			} else if (instructionType.loadInst().typeValue().value().constant() != null) {
				loadVarIdentifier = instructionType.loadInst().typeValue().value().constant().GlobalIdent().getText();
			} else {
				throw new AssertionError("Something went wrong while parsing the load instruction:");
			}

			final IdentifierExpression loadVarExpr = new IdentifierExpression(location,
					unifyIdentifier(loadVarIdentifier));
			final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
					new Expression[] { loadVarExpr });
			result.addFuncBlock(assignment);
		} else if (instructionType.iCmpInst() != null) {
			result.addFuncLocalVar(constructVarDecFromString("bool", identifier, location));
			final LLVMIRParser.ConcreteTypeContext typeContext = instructionType.iCmpInst().typeValue().firstClassType()
					.concreteType();

			Expression leftExpr = null;
			Expression rightExpr = null;
			final String operatorString = instructionType.iCmpInst().iPred().getText();
			final Operator operator = getCompOperatorFromOperatorValue(operatorString);
			final boolean isSigned = operatorString.startsWith("s");

			final LLVMIRParser.ValueContext leftValue = instructionType.iCmpInst().typeValue().value();
			leftExpr = constructExpressionFromValue(leftValue, typeContext, location, isSigned);

			final LLVMIRParser.ValueContext rightValue = instructionType.iCmpInst().value();
			rightExpr = constructExpressionFromValue(rightValue, typeContext, location, isSigned);

			if (isSigned && typeContext.intType() != null && !typeContext.intType().getText().equals("i1")) {
				final int bitLength = getBitLengthFromType(typeContext);
				if (operator == Operator.COMPLEQ || operator == Operator.COMPLT || operator == Operator.COMPGEQ
						|| operator == Operator.COMPGT) {
					leftExpr = constructSignedExpression(leftExpr, bitLength, location);
					rightExpr = constructSignedExpression(rightExpr, bitLength, location);
				}
			}

			final VariableLHS varLhs = new VariableLHS(location, identifier);
			final BinaryExpression binaryExpr = new BinaryExpression(location, operator, leftExpr, rightExpr);
			final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
					new Expression[] { binaryExpr });
			result.addFuncBlock(assignment);
		} else if (instructionType.phiInst() != null) {
			final LLVMIRParser.TypeContext typeContext = instructionType.phiInst().type();
			result.addFuncLocalVar(constructVarDecFromTypeContext(typeContext, identifier, location));
			for (final LLVMIRParser.IncContext inc : instructionType.phiInst().inc()) {
				final String incIdentifier = unifyIdentifier(inc.LocalIdent().getText());
				final int labelIndex = getLabelIndexFromFuncBody(ctx, incIdentifier);
				final IdentifierExpression incExpr = new IdentifierExpression(location, mLabelIdentifier);
				final IntegerLiteral labelIndexLiteral = new IntegerLiteral(location, Integer.toString(labelIndex));
				final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.COMPEQ, incExpr,
						labelIndexLiteral);
				final VariableLHS varLhs = new VariableLHS(location, identifier);
				final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
						new Expression[] { constructExpressionFromValue(inc.value(), typeContext, location, false) });
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
				final IfStatement ifStmt = new IfStatement(location,
						constructExpressionFromValue(instructionType.zExtInst().typeValue().value(), typeContext,
								location, false),
						new Statement[] { thenAssignment }, new Statement[] { elseAssignment });
				result.addFuncBlock(ifStmt);
			} else {
				final VariableLHS varLhs = new VariableLHS(location, identifier);
				final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
						new Expression[] { constructExpressionFromValue(instructionType.zExtInst().typeValue().value(),
								typeContext, location, false) });
				result.addFuncBlock(assignment);
			}
		} else if (instructionType.sExtInst() != null) {
			final LLVMIRParser.TypeContext newTypeContext = instructionType.sExtInst().type();
			final LLVMIRParser.ConcreteTypeContext oldTypeContext = instructionType.sExtInst().typeValue()
					.firstClassType().concreteType();
			final String oldTypeString = oldTypeContext.intType().getText();
			result.addFuncLocalVar(constructVarDecFromTypeContext(newTypeContext, identifier, location));
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
						constructExpressionFromValue(instructionType.sExtInst().typeValue().value(), oldTypeContext,
								location, false),
						new Statement[] { thenAssignment }, new Statement[] { elseAssignment });
				result.addFuncBlock(ifStmt);
			} else {
				final VariableLHS varLhs = new VariableLHS(location, identifier);
				final int oldBitLength = getBitLengthFromType(oldTypeContext);
				final int newBitLength = getBitLengthFromType(newTypeContext);
				final IntegerLiteral bitLengthLiteral = constructBitLengthLiteral(location, newBitLength, false);
				final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.ARITHMOD,
						constructSignedExpression(
								constructExpressionFromValue(instructionType.sExtInst().typeValue().value(),
										oldTypeContext, location, false),
								oldBitLength, location),
						bitLengthLiteral);
				final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
						new Expression[] { binaryExpr });
				result.addFuncBlock(assignment);
			}
		} else if (instructionType.addInst() != null) {
			final LLVMIRParser.ConcreteTypeContext typeContext = instructionType.addInst().typeValue().firstClassType()
					.concreteType();
			result.addFuncLocalVar(constructVarDecFromTypeContext(typeContext, identifier, location));
			final int bitLength = getBitLengthFromType(typeContext);
			final VariableLHS varLhs = new VariableLHS(location, identifier);
			final Expression leftExpr = constructExpressionFromValue(instructionType.addInst().typeValue().value(),
					typeContext, location, false);
			final Expression rightExpr = constructExpressionFromValue(instructionType.addInst().value(), typeContext,
					location, false);
			final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.ARITHPLUS, leftExpr, rightExpr);
			final IntegerLiteral bitLengthLiteral = constructBitLengthLiteral(location, bitLength, false);
			final BinaryExpression signedExpr = new BinaryExpression(location, Operator.ARITHMOD, binaryExpr,
					bitLengthLiteral);
			final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
					new Expression[] { signedExpr });
			result.addFuncBlock(assignment);
		} else if (instructionType.sDivInst() != null) {
			final LLVMIRParser.ConcreteTypeContext typeContext = instructionType.sDivInst().typeValue().firstClassType()
					.concreteType();
			result.addFuncLocalVar(constructVarDecFromTypeContext(typeContext, identifier, location));
			final int bitLength = getBitLengthFromType(typeContext);
			final VariableLHS varLhs = new VariableLHS(location, identifier);
			final Expression leftExpr = constructExpressionFromValue(instructionType.sDivInst().typeValue().value(),
					typeContext, location, false);
			final Expression rightExpr = constructExpressionFromValue(instructionType.sDivInst().value(), typeContext,
					location, false);
			final Expression maxFromBitLengthExpr = constructBitLengthLiteral(location, bitLength, false);
			final Expression isSignedExpr = new IntegerLiteral(location, "1");

			final FunctionApplication funcApp = new FunctionApplication(location, mCDivIdentifier,
					new Expression[] { leftExpr, rightExpr, maxFromBitLengthExpr, isSignedExpr });

			final IntegerLiteral bitLengthLiteral = constructBitLengthLiteral(location, bitLength, false);
			final BinaryExpression signedExpr = new BinaryExpression(location, Operator.ARITHMOD, funcApp,
					bitLengthLiteral);
			final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
					new Expression[] { signedExpr });
			result.addFuncBlock(assignment);
		} else if (instructionType.uDivInst() != null) {
			final LLVMIRParser.ConcreteTypeContext typeContext = instructionType.uDivInst().typeValue().firstClassType()
					.concreteType();
			result.addFuncLocalVar(constructVarDecFromTypeContext(typeContext, identifier, location));
			final int bitLength = getBitLengthFromType(typeContext);
			final VariableLHS varLhs = new VariableLHS(location, identifier);
			final Expression leftExpr = constructExpressionFromValue(instructionType.uDivInst().typeValue().value(),
					typeContext, location, false);
			final Expression rightExpr = constructExpressionFromValue(instructionType.uDivInst().value(), typeContext,
					location, false);
			final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.ARITHDIV, leftExpr, rightExpr);
			final IntegerLiteral bitLengthLiteral = constructBitLengthLiteral(location, bitLength, false);
			final BinaryExpression signedExpr = new BinaryExpression(location, Operator.ARITHMOD, binaryExpr,
					bitLengthLiteral);
			final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
					new Expression[] { signedExpr });
			result.addFuncBlock(assignment);
		} else if (instructionType.uRemInst() != null) {
			final LLVMIRParser.ConcreteTypeContext typeContext = instructionType.uRemInst().typeValue().firstClassType()
					.concreteType();
			result.addFuncLocalVar(constructVarDecFromTypeContext(typeContext, identifier, location));
			final int bitLength = getBitLengthFromType(typeContext);
			final VariableLHS varLhs = new VariableLHS(location, identifier);
			final Expression leftExpr = constructExpressionFromValue(instructionType.uRemInst().typeValue().value(),
					typeContext, location, false);
			final Expression rightExpr = constructExpressionFromValue(instructionType.uRemInst().value(), typeContext,
					location, false);
			final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.ARITHMOD, leftExpr, rightExpr);
			final IntegerLiteral bitLengthLiteral = constructBitLengthLiteral(location, bitLength, false);
			final BinaryExpression signedExpr = new BinaryExpression(location, Operator.ARITHMOD, binaryExpr,
					bitLengthLiteral);
			final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
					new Expression[] { signedExpr });
			result.addFuncBlock(assignment);
		} else if (instructionType.sRemInst() != null) {
			final LLVMIRParser.ConcreteTypeContext typeContext = instructionType.sRemInst().typeValue().firstClassType()
					.concreteType();
			result.addFuncLocalVar(constructVarDecFromTypeContext(typeContext, identifier, location));
			final int bitLength = getBitLengthFromType(typeContext);
			final VariableLHS varLhs = new VariableLHS(location, identifier);
			final Expression leftExpr = constructExpressionFromValue(instructionType.sRemInst().typeValue().value(),
					typeContext, location, false);
			final Expression rightExpr = constructExpressionFromValue(instructionType.sRemInst().value(), typeContext,
					location, false);
			final Expression maxFromBitLengthExpr = constructBitLengthLiteral(location, bitLength, false);
			final Expression isSignedExpr = new IntegerLiteral(location, "1");

			final FunctionApplication remCall = new FunctionApplication(mLocation, mRemIdentifier,
					new Expression[] { leftExpr, rightExpr, maxFromBitLengthExpr, isSignedExpr });

			final IntegerLiteral bitLengthLiteral = constructBitLengthLiteral(location, bitLength, false);
			final BinaryExpression signedExpr = new BinaryExpression(location, Operator.ARITHMOD, remCall,
					bitLengthLiteral);
			final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
					new Expression[] { signedExpr });
			result.addFuncBlock(assignment);
		} else if (instructionType.subInst() != null) {
			final LLVMIRParser.ConcreteTypeContext typeContext = instructionType.subInst().typeValue().firstClassType()
					.concreteType();
			result.addFuncLocalVar(constructVarDecFromTypeContext(typeContext, identifier, location));
			final int bitLength = getBitLengthFromType(typeContext);
			final VariableLHS varLhs = new VariableLHS(location, identifier);
			final Expression leftExpr = constructExpressionFromValue(instructionType.subInst().typeValue().value(),
					typeContext, location, false);
			final Expression rightExpr = constructExpressionFromValue(instructionType.subInst().value(), typeContext,
					location, false);
			final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.ARITHMINUS, leftExpr,
					rightExpr);
			final IntegerLiteral bitLengthLiteral = constructBitLengthLiteral(location, bitLength, false);
			final BinaryExpression signedExpr = new BinaryExpression(location, Operator.ARITHMOD, binaryExpr,
					bitLengthLiteral);
			final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
					new Expression[] { signedExpr });
			result.addFuncBlock(assignment);
		} else if (instructionType.mulInst() != null) {
			final LLVMIRParser.ConcreteTypeContext typeContext = instructionType.mulInst().typeValue().firstClassType()
					.concreteType();
			result.addFuncLocalVar(constructVarDecFromTypeContext(typeContext, identifier, location));
			final int bitLength = getBitLengthFromType(typeContext);
			final VariableLHS varLhs = new VariableLHS(location, identifier);
			final Expression leftExpr = constructExpressionFromValue(instructionType.mulInst().typeValue().value(),
					typeContext, location, false);
			final Expression rightExpr = constructExpressionFromValue(instructionType.mulInst().value(), typeContext,
					location, false);
			final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.ARITHMUL, leftExpr, rightExpr);
			final IntegerLiteral bitLengthLiteral = constructBitLengthLiteral(location, bitLength, false);
			final BinaryExpression signedExpr = new BinaryExpression(location, Operator.ARITHMOD, binaryExpr,
					bitLengthLiteral);
			final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
					new Expression[] { signedExpr });
			result.addFuncBlock(assignment);
		} else if (instructionType.allocaInst() != null) {
			final LLVMIRParser.TypeContext typeContext = instructionType.allocaInst().type();
			result.addFuncLocalVar(constructVarDecFromTypeContext(typeContext, identifier, location));
		} else if (instructionType.callInst() != null) {
			LLVMIRParser.TypeContext typeContext;
			if (instructionType.callInst().type().type() != null) {
				typeContext = instructionType.callInst().type().type();
			} else if (instructionType.callInst().type() != null) {
				typeContext = instructionType.callInst().type();
			} else {
				throw new AssertionError("The support for call instructions without a type is not implemented yet.");
			}
			result.addFuncLocalVar(constructVarDecFromTypeContext(typeContext, identifier, location));
			final String callIdentifier = instructionType.callInst().value().constant().getText();
			if (callIdentifier.equals("@printf")) {
				final VariableLHS varLhs = new VariableLHS(location, identifier);
				final HavocStatement havocStmt = new HavocStatement(location, new VariableLHS[] { varLhs });
				result.addFuncBlock(havocStmt);
			} else if (callIdentifier.equals("@__VERIFIER_nondet_int")
					|| callIdentifier.equals("@__VERIFIER_nondet_short")
					|| callIdentifier.equals("@__VERIFIER_nondet_ushort")
					|| callIdentifier.equals("@__VERIFIER_nondet_bool")
					|| callIdentifier.equals("@__VERIFIER_nondet_ulong")
					|| callIdentifier.equals("@__VERIFIER_nondet_uint128")
					|| callIdentifier.equals("@__VERIFIER_nondet_uint")
					|| callIdentifier.equals("@__VERIFIER_nondet_ulonglong")
					|| callIdentifier.equals("@__VERIFIER_nondet_char")
					|| callIdentifier.equals("@__VERIFIER_nondet_uchar")) {
				final VariableLHS varLhs = new VariableLHS(location, identifier);
				final HavocStatement havocStmt = new HavocStatement(location, new VariableLHS[] { varLhs });
				result.addFuncBlock(havocStmt);

				final int bitLength = getBitLengthFromType(typeContext);

				final IntegerLiteral maxValueLiteral = new IntegerLiteral(location,
						BigInteger.ONE.shiftLeft(bitLength).subtract(BigInteger.ONE).toString());
				final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.COMPLEQ,
						new IdentifierExpression(location, identifier), maxValueLiteral);
				final AssumeStatement assumeStmt = new AssumeStatement(location, new NamedAttribute[] {}, binaryExpr);
				result.addFuncBlock(assumeStmt);

				final IntegerLiteral minValueLiteral = new IntegerLiteral(location, "0");
				final BinaryExpression binaryExpr2 = new BinaryExpression(location, Operator.COMPGEQ,
						new IdentifierExpression(location, identifier), minValueLiteral);
				final AssumeStatement assumeStmt2 = new AssumeStatement(location, new NamedAttribute[] {}, binaryExpr2);
				result.addFuncBlock(assumeStmt2);
			} else if (callIdentifier.equals("@llvm.abs.i32")) {
				final LLVMIRParser.ArgContext arg = instructionType.callInst().args().arg(0);
				final LLVMIRParser.ConcreteTypeContext argType = arg.concreteType();
				final LLVMIRParser.ValueContext argValue = arg.value();
				final int bitLength = getBitLengthFromType(argType);
				final IntegerLiteral intLiteral0 = new IntegerLiteral(location, "0");
				final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.COMPLT,
						constructSignedExpression(constructExpressionFromValue(argValue, argType, location, false),
								bitLength, location),
						intLiteral0);
				final IntegerLiteral zeroLiteral = new IntegerLiteral(location, "0");
				final BinaryExpression nagationExpr = new BinaryExpression(location, Operator.ARITHMINUS, zeroLiteral,
						constructSignedExpression(constructExpressionFromValue(argValue, argType, location, false),
								bitLength, location));
				final IntegerLiteral bitLengthLiteral = constructBitLengthLiteral(location, bitLength, false);
				final BinaryExpression thenExpr = new BinaryExpression(location, Operator.ARITHMOD, nagationExpr,
						bitLengthLiteral);
				final Expression elseExpr = constructExpressionFromValue(argValue, argType, location, false);
				final IfThenElseExpression ifThenElseExpr = new IfThenElseExpression(location, binaryExpr, thenExpr,
						elseExpr);
				final VariableLHS varLhs = new VariableLHS(location, identifier);
				final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
						new Expression[] { ifThenElseExpr });
				result.addFuncBlock(assignment);
			} else if (callIdentifier.startsWith("@llvm.sadd.with.overflow")) {
				final LLVMIRParser.ArgContext arg0 = instructionType.callInst().args().arg(0);
				final LLVMIRParser.ArgContext arg1 = instructionType.callInst().args().arg(1);
				final LLVMIRParser.ConcreteTypeContext arg0Type = arg0.concreteType();
				final LLVMIRParser.ValueContext arg0Value = arg0.value();
				final LLVMIRParser.ValueContext arg1Value = arg1.value();
				final int bitLength = getBitLengthFromType(arg0Type);
				final BinaryExpression expr = new BinaryExpression(location, Operator.ARITHPLUS,
						constructSignedExpression(constructExpressionFromValue(arg0Value, arg0Type, location, false),
								bitLength, location),
						constructSignedExpression(constructExpressionFromValue(arg1Value, arg0Type, location, false),
								bitLength, location));
				if (!bitLengthPairExists(bitLength, mDeclarations)) {
					mDeclarations.add(constructBitLengthPairTypeDeclaration(bitLength, location));
				}
				final Pair<VariableDeclaration, AssignmentStatement> operationWithOverflowPair = constructLlvmOperationWithOverflow(
						expr, bitLength, true, identifier, location);
				result.addFuncLocalVar(operationWithOverflowPair.getFirst());
				result.addFuncBlock(operationWithOverflowPair.getSecond());
			} else if (callIdentifier.startsWith("@llvm.uadd.with.overflow")) {
				final LLVMIRParser.ArgContext arg0 = instructionType.callInst().args().arg(0);
				final LLVMIRParser.ArgContext arg1 = instructionType.callInst().args().arg(1);
				final LLVMIRParser.ConcreteTypeContext arg0Type = arg0.concreteType();
				final LLVMIRParser.ValueContext arg0Value = arg0.value();
				final LLVMIRParser.ValueContext arg1Value = arg1.value();
				final int bitLength = getBitLengthFromType(arg0Type);
				final BinaryExpression expr = new BinaryExpression(location, Operator.ARITHPLUS,
						constructExpressionFromValue(arg0Value, arg0Type, location, false),
						constructExpressionFromValue(arg1Value, arg0Type, location, false));
				if (!bitLengthPairExists(bitLength, mDeclarations)) {
					mDeclarations.add(constructBitLengthPairTypeDeclaration(bitLength, location));
				}
				final Pair<VariableDeclaration, AssignmentStatement> operationWithOverflowPair = constructLlvmOperationWithOverflow(
						expr, bitLength, false, identifier, location);
				result.addFuncLocalVar(operationWithOverflowPair.getFirst());
				result.addFuncBlock(operationWithOverflowPair.getSecond());
			} else if (callIdentifier.startsWith("@llvm.ssub.with.overflow")) {
				final LLVMIRParser.ArgContext arg0 = instructionType.callInst().args().arg(0);
				final LLVMIRParser.ArgContext arg1 = instructionType.callInst().args().arg(1);
				final LLVMIRParser.ConcreteTypeContext arg0Type = arg0.concreteType();
				final LLVMIRParser.ValueContext arg0Value = arg0.value();
				final LLVMIRParser.ValueContext arg1Value = arg1.value();
				final int bitLength = getBitLengthFromType(arg0Type);
				final BinaryExpression expr = new BinaryExpression(location, Operator.ARITHMINUS,
						constructSignedExpression(constructExpressionFromValue(arg0Value, arg0Type, location, false),
								bitLength, location),
						constructSignedExpression(constructExpressionFromValue(arg1Value, arg0Type, location, false),
								bitLength, location));
				if (!bitLengthPairExists(bitLength, mDeclarations)) {
					mDeclarations.add(constructBitLengthPairTypeDeclaration(bitLength, location));
				}
				final Pair<VariableDeclaration, AssignmentStatement> operationWithOverflowPair = constructLlvmOperationWithOverflow(
						expr, bitLength, true, identifier, location);
				result.addFuncLocalVar(operationWithOverflowPair.getFirst());
				result.addFuncBlock(operationWithOverflowPair.getSecond());
			} else if (callIdentifier.startsWith("@llvm.usub.with.overflow")) {
				final LLVMIRParser.ArgContext arg0 = instructionType.callInst().args().arg(0);
				final LLVMIRParser.ArgContext arg1 = instructionType.callInst().args().arg(1);
				final LLVMIRParser.ConcreteTypeContext arg0Type = arg0.concreteType();
				final LLVMIRParser.ValueContext arg0Value = arg0.value();
				final LLVMIRParser.ValueContext arg1Value = arg1.value();
				final int bitLength = getBitLengthFromType(arg0Type);
				final BinaryExpression expr = new BinaryExpression(location, Operator.ARITHMINUS,
						constructExpressionFromValue(arg0Value, arg0Type, location, false),
						constructExpressionFromValue(arg1Value, arg0Type, location, false));
				if (!bitLengthPairExists(bitLength, mDeclarations)) {
					mDeclarations.add(constructBitLengthPairTypeDeclaration(bitLength, location));
				}
				final Pair<VariableDeclaration, AssignmentStatement> operationWithOverflowPair = constructLlvmOperationWithOverflow(
						expr, bitLength, false, identifier, location);
				result.addFuncLocalVar(operationWithOverflowPair.getFirst());
				result.addFuncBlock(operationWithOverflowPair.getSecond());
			} else if (callIdentifier.startsWith("@llvm.smul.with.overflow")) {
				final LLVMIRParser.ArgContext arg0 = instructionType.callInst().args().arg(0);
				final LLVMIRParser.ArgContext arg1 = instructionType.callInst().args().arg(1);
				final LLVMIRParser.ConcreteTypeContext arg0Type = arg0.concreteType();
				final LLVMIRParser.ValueContext arg0Value = arg0.value();
				final LLVMIRParser.ValueContext arg1Value = arg1.value();
				final int bitLength = getBitLengthFromType(arg0Type);
				final BinaryExpression expr = new BinaryExpression(location, Operator.ARITHMUL,
						constructSignedExpression(constructExpressionFromValue(arg0Value, arg0Type, location, false),
								bitLength, location),
						constructSignedExpression(constructExpressionFromValue(arg1Value, arg0Type, location, false),
								bitLength, location));
				if (!bitLengthPairExists(bitLength, mDeclarations)) {
					mDeclarations.add(constructBitLengthPairTypeDeclaration(bitLength, location));
				}
				final Pair<VariableDeclaration, AssignmentStatement> operationWithOverflowPair = constructLlvmOperationWithOverflow(
						expr, bitLength, true, identifier, location);
				result.addFuncLocalVar(operationWithOverflowPair.getFirst());
				result.addFuncBlock(operationWithOverflowPair.getSecond());
			} else if (callIdentifier.startsWith("@llvm.umul.with.overflow")) {
				final LLVMIRParser.ArgContext arg0 = instructionType.callInst().args().arg(0);
				final LLVMIRParser.ArgContext arg1 = instructionType.callInst().args().arg(1);
				final LLVMIRParser.ConcreteTypeContext arg0Type = arg0.concreteType();
				final LLVMIRParser.ValueContext arg0Value = arg0.value();
				final LLVMIRParser.ValueContext arg1Value = arg1.value();
				final int bitLength = getBitLengthFromType(arg0Type);
				final BinaryExpression expr = new BinaryExpression(location, Operator.ARITHMUL,
						constructExpressionFromValue(arg0Value, arg0Type, location, false),
						constructExpressionFromValue(arg1Value, arg0Type, location, false));
				if (!bitLengthPairExists(bitLength, mDeclarations)) {
					mDeclarations.add(constructBitLengthPairTypeDeclaration(bitLength, location));
				}
				final Pair<VariableDeclaration, AssignmentStatement> operationWithOverflowPair = constructLlvmOperationWithOverflow(
						expr, bitLength, false, identifier, location);
				result.addFuncLocalVar(operationWithOverflowPair.getFirst());
				result.addFuncBlock(operationWithOverflowPair.getSecond());
			} else {
				final Procedure proc = getProcedureFromDeclarations(unifyIdentifier(callIdentifier), mDeclarations);
				for (final Specification spec : proc.getSpecification()) {
					if (!(spec instanceof ModifiesSpecification)) {
						continue;
					}
					for (final VariableLHS varLhs : ((ModifiesSpecification) spec).getIdentifiers()) {
						final String varIdentifier = varLhs.getIdentifier();
						result.addFuncModifiedGlobalVar(constructSpecFromIdentifier(varIdentifier, location));
					}
				}
				final ArrayList<Expression> args = new ArrayList<>();
				for (final LLVMIRParser.ArgContext arg : instructionType.callInst().args().arg()) {
					args.add(constructExpressionFromValue(arg.value(), typeContext, location, false));
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
					typeContext0, location, false);
			final Expression thenExpr = constructExpressionFromValue(instructionType.selectInst().typeValue(1).value(),
					typeContext1, location, false);
			final Expression elseExpr = constructExpressionFromValue(instructionType.selectInst().typeValue(2).value(),
					typeContext1, location, false);
			result.addFuncLocalVar(constructVarDecFromTypeContext(typeContext1, identifier, location));
			final VariableLHS thenVarLhs = new VariableLHS(location, identifier);
			final VariableLHS elseVarLhs = new VariableLHS(location, identifier);
			final AssignmentStatement thenAssignment = new AssignmentStatement(location,
					new LeftHandSide[] { thenVarLhs }, new Expression[] { thenExpr });
			final AssignmentStatement elseAssignment = new AssignmentStatement(location,
					new LeftHandSide[] { elseVarLhs }, new Expression[] { elseExpr });
			final IfStatement ifStmt = new IfStatement(location, ifExpr, new Statement[] { thenAssignment },
					new Statement[] { elseAssignment });
			result.addFuncBlock(ifStmt);
		} else if (instructionType.truncInst() != null) {
			final LLVMIRParser.TypeContext newTypeContext = instructionType.truncInst().type();
			final LLVMIRParser.ConcreteTypeContext oldTypeContext = instructionType.truncInst().typeValue()
					.firstClassType().concreteType();
			final int newBitLength = getBitLengthFromType(newTypeContext);
			final VariableDeclaration varDecl = (constructVarDecFromTypeContext(newTypeContext, identifier, location));
			result.addFuncLocalVar(varDecl);
			if (newBitLength == 1) {
				final IntegerLiteral oneLiteral = new IntegerLiteral(location, "1");
				final IntegerLiteral twoLiteral = new IntegerLiteral(location, "2");
				final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.ARITHMOD,
						constructExpressionFromValue(instructionType.truncInst().typeValue().value(), oldTypeContext,
								location, false),
						twoLiteral);
				final BinaryExpression conditionalExpr = new BinaryExpression(location, Operator.COMPEQ, binaryExpr,
						oneLiteral);
				final VariableLHS varLhs = new VariableLHS(location, identifier);
				final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
						new Expression[] { conditionalExpr });
				result.addFuncBlock(assignment);
			} else {
				final IntegerLiteral bitLengthLiteral = constructBitLengthLiteral(location, newBitLength, false);
				final BinaryExpression binaryExpr = new BinaryExpression(location, Operator.ARITHMOD,
						constructExpressionFromValue(instructionType.truncInst().typeValue().value(), oldTypeContext,
								location, false),
						bitLengthLiteral);
				final VariableLHS varLhs = new VariableLHS(location, identifier);
				final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
						new Expression[] { binaryExpr });
				result.addFuncBlock(assignment);
			}
		} else if (instructionType.extractValueInst() != null) {
			if (instructionType.extractValueInst().typeValue().firstClassType().concreteType().structType() == null) {
				throw new AssertionError(
						"The support for extractValue instructions without a struct type is not implemented yet.");
			}
			final int indexNumber = Integer.parseInt(instructionType.extractValueInst().IntLit(0).toString());
			final LLVMIRParser.TypeContext typeContext = instructionType.extractValueInst().typeValue().firstClassType()
					.concreteType().structType().type(indexNumber);
			final VariableDeclaration varDecl = (constructVarDecFromTypeContext(typeContext, identifier, location));
			result.addFuncLocalVar(varDecl);
			final StructAccessExpression structAccessExpr = new StructAccessExpression(location,
					constructExpressionFromValue(instructionType.extractValueInst().typeValue().value(),
							instructionType.extractValueInst().typeValue().firstClassType().concreteType(), location,
							false),
					String.valueOf(indexNumber));
			final VariableLHS varLhs = new VariableLHS(location, identifier);
			final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
					new Expression[] { structAccessExpr });
			result.addFuncBlock(assignment);
		} else if (instructionType.andInst() != null) {
			constructHavocStatementFromTypeValue(result, instructionType.andInst().typeValue(), location, identifier,
					"andInst");
		} else if (instructionType.orInst() != null) {
			constructHavocStatementFromTypeValue(result, instructionType.orInst().typeValue(), location, identifier,
					"orInst");
		} else if (instructionType.xorInst() != null) {
			constructHavocStatementFromTypeValue(result, instructionType.xorInst().typeValue(), location, identifier,
					"xorInst");
		} else if (instructionType.shlInst() != null) {
			constructHavocStatementFromTypeValue(result, instructionType.shlInst().typeValue(), location, identifier,
					"shlInst");
		} else if (instructionType.aShrInst() != null) {
			constructHavocStatementFromTypeValue(result, instructionType.aShrInst().typeValue(), location, identifier,
					"aShrInst");
		} else if (instructionType.lShrInst() != null) {
			constructHavocStatementFromTypeValue(result, instructionType.lShrInst().typeValue(), location, identifier,
					"lShrInst");
		} else {
			throw new AssertionError("The support for the given instruction is not implemented yet.");
		}
		return result;
	}

	/**
	 * Handles the visit event for a branch terminator in the LLVM IR parse tree.
	 *
	 * This method processes the branch terminator and constructs a GotoStatement to jump to the specified label.
	 *
	 * @param ctx The parse tree context for the branch terminator.
	 * @return A Result object containing the GotoStatement.
	 */
	@Override
	public Result visitBrTerm(final LLVMIRParser.BrTermContext ctx) {
		final LlvmirLocation location = constructLocation(ctx);
		final Result result = new Result();
		final String labelIdentifier = unifyIdentifier(ctx.label().LocalIdent().getText());
		final GotoStatement gotoStmt = new GotoStatement(location, new String[] { labelIdentifier });
		result.addFuncBlock(gotoStmt);

		return result;
	}

	/**
	 * Handles the visit event for a conditional branch terminator in the LLVM IR parse tree.
	 *
	 * This method processes the conditional branch terminator and constructs an IfStatement to handle the condition,
	 * along with GotoStatements for the true and false branches.
	 *
	 * @param ctx The parse tree context for the conditional branch terminator.
	 * @return A Result object containing the IfStatement and GotoStatements.
	 */
	@Override
	public Result visitCondBrTerm(final LLVMIRParser.CondBrTermContext ctx) {
		final LlvmirLocation location = constructLocation(ctx);
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
	 * This method processes the store instruction and constructs an AssignmentStatement to assign a value to a
	 * variable.
	 *
	 * @param ctx The parse tree context for the store instruction.
	 * @return A Result object containing the AssignmentStatement.
	 */
	@Override
	public Result visitStoreInst(final LLVMIRParser.StoreInstContext ctx) {
		final Result result = new Result();
		final LlvmirLocation location = constructLocation(ctx);

		String identifier = null;
		final LLVMIRParser.ValueContext valueContext1 = ctx.typeValue(1).value();
		if (valueContext1.LocalIdent() != null) {
			identifier = unifyIdentifier(ctx.typeValue(1).value().LocalIdent().getText());
		} else if (valueContext1.constant() != null) {
			identifier = unifyIdentifier(valueContext1.constant().GlobalIdent().getText());
			result.addFuncModifiedGlobalVar(constructSpecFromIdentifier(identifier, location));
		} else {
			throw new AssertionError("Something went wrong while parsing the store instruction:");
		}
		final VariableLHS varLhs = new VariableLHS(location, identifier);
		final AssignmentStatement assignment = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
				new Expression[] { constructExpressionFromValue(ctx.typeValue(0).value(),
						ctx.typeValue(0).firstClassType().concreteType(), location, false) });
		result.addFuncBlock(assignment);

		return result;
	}

	/**
	 * Handles the visit event for a call instruction in the LLVM IR parse tree.
	 *
	 * This method processes the call instruction and constructs a CallStatement or an AssertStatement based on the
	 * called function.
	 *
	 * @param ctx The parse tree context for the call instruction.
	 * @return A Result object containing the CallStatement or AssertStatement.
	 */
	@Override
	public Result visitCallInst(final LLVMIRParser.CallInstContext ctx) {
		final Result result = new Result();
		final LlvmirLocation location = constructLocation(ctx);

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
			final Procedure proc = getProcedureFromDeclarations(unifyIdentifier(callIdentifier), mDeclarations);
			for (final Specification spec : proc.getSpecification()) {
				if (!(spec instanceof ModifiesSpecification)) {
					continue;
				}
				for (final VariableLHS varLhs : ((ModifiesSpecification) spec).getIdentifiers()) {
					final String varIdentifier = varLhs.getIdentifier();

					result.addFuncModifiedGlobalVar(constructSpecFromIdentifier(varIdentifier, location));
				}
			}
			final ArrayList<Expression> args = new ArrayList<>();
			for (final LLVMIRParser.ArgContext arg : ctx.args().arg()) {
				args.add(constructExpressionFromValue(arg.value(), arg.concreteType(), location, false));
			}
			final CallStatement callStmt = new CallStatement(location, false, new VariableLHS[] {},
					unifyIdentifier(callIdentifier), args.toArray(Expression[]::new));
			result.addFuncBlock(callStmt);
		}
		return result;
	}

	/**
	 * Handles the visit event for a switch terminator in the LLVM IR parse tree.
	 *
	 * This method processes the switch terminator and constructs an IfStatement for each case, along with a
	 * GotoStatement for the default case.
	 *
	 * @param ctx The parse tree context for the switch terminator.
	 * @return A Result object containing the IfStatements and GotoStatement.
	 */
	@Override
	public Result visitSwitchTerm(final LLVMIRParser.SwitchTermContext ctx) {
		final Result result = new Result();
		final LlvmirLocation location = constructLocation(ctx);

		final LLVMIRParser.BasicBlockContext basicBlockContext = getEnclosingBasicBlock(ctx);
		final IntegerLiteral currentLabelLiteral = new IntegerLiteral(location, String
				.valueOf(getLabelIndexFromFuncBody(ctx, unifyIdentifier(basicBlockContext.LabelIdent().getText()))));
		final VariableLHS varLhs = new VariableLHS(location, mLabelIdentifier);

		final AssignmentStatement assignCurrentLabel = new AssignmentStatement(location, new LeftHandSide[] { varLhs },
				new Expression[] { currentLabelLiteral });
		result.addFuncBlock(assignCurrentLabel);

		final LLVMIRParser.ConcreteTypeContext conditionTypeContext = ctx.typeValue().firstClassType().concreteType();
		final List<LLVMIRParser.CaseContext> caseContexts = ctx.case_();
		if (caseContexts.size() == 2) {
			final String case0LabelIdentifier = unifyIdentifier(caseContexts.get(0).label().LocalIdent().getText());
			final String case1LabelIdentifier = unifyIdentifier(caseContexts.get(1).label().LocalIdent().getText());
			final GotoStatement thenGoto = new GotoStatement(location, new String[] { case0LabelIdentifier });
			final GotoStatement elseGoto = new GotoStatement(location, new String[] { case1LabelIdentifier });
			final IfStatement ifStmt = new IfStatement(location,
					new UnaryExpression(location, UnaryExpression.Operator.LOGICNEG, constructExpressionFromValue(
							ctx.typeValue().value(), conditionTypeContext, location, false)),
					new Statement[] { thenGoto }, new Statement[] { elseGoto });
			result.addFuncBlock(ifStmt);
		} else {
			for (final LLVMIRParser.CaseContext caseContext : caseContexts) {
				final LLVMIRParser.ConcreteTypeContext caseTypeContext = caseContext.typeConst().firstClassType()
						.concreteType();
				final BinaryExpression conditionExpr = new BinaryExpression(location, Operator.COMPEQ,
						constructExpressionFromValue(ctx.typeValue().value(), conditionTypeContext, location, false),
						constructExpressionFromConstant(caseContext.typeConst().constant(), caseTypeContext, location,
								false));
				final String caseLabelIdentifier = unifyIdentifier(caseContext.label().LocalIdent().getText());
				final GotoStatement thenGoto = new GotoStatement(location, new String[] { caseLabelIdentifier });
				final IfStatement ifStmt = new IfStatement(location, conditionExpr, new Statement[] { thenGoto },
						new Statement[] {});
				result.addFuncBlock(ifStmt);
			}
		}
		final String defaultLabelIdentifier = unifyIdentifier(ctx.label().LocalIdent().getText());
		final GotoStatement defaultGoto = new GotoStatement(location, new String[] { defaultLabelIdentifier });
		result.addFuncBlock(defaultGoto);
		return result;
	}

	/**
	 * Retrieves the enclosing basic block context for a given parser rule context.
	 *
	 * This method traverses the parse tree upwards from the provided context until it finds a BasicBlockContext. If no
	 * such context is found, an AssertionError is thrown.
	 *
	 * @param ctx The parser rule context from which to start the search.
	 * @return The enclosing BasicBlockContext.
	 * @throws AssertionError if the provided context is not enclosed in a basic block.
	 */
	private static LLVMIRParser.BasicBlockContext getEnclosingBasicBlock(final ParserRuleContext ctx) {
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
