/*
 * Copyright (C) 2013-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RequiresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CTranslationUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.FunctionDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TypeHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler.MemoryModelDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.BitvectorTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitiveCategory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.InitializerResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Class caring for some post processing steps, like creating an initializer procedure and the start procedure.
 *
 * @author Markus Lindenmann
 * @date 12.10.2012
 */
public class PostProcessor {
//	/**
//	 * Holds the Boogie identifiers of the initialized global variables. Used for filling the modifies clause of
//	 * Ultimate.start and Ultimate.init.
//	 */
//	private final LinkedHashSet<String> mInitializedGlobals;

	private final Dispatcher mDispatcher;
	private final ILogger mLogger;

	private final ExpressionTranslation mExpressionTranslation;
	private final boolean mOverapproximateFloatingPointOperations;

	/*
	 * Decides if the PostProcessor declares the special function that we use for converting Boogie-Real to a
	 * Boogie-Int. This is needed when we do a cast from float to int in C.
	 */
	public boolean mDeclareToIntFunction = false;

	private final BoogieTypeHelper mBoogieTypeHelper;

	/**
	 * Constructor.
	 *
	 * @param overapproximateFloatingPointOperations
	 */
	public PostProcessor(final Dispatcher dispatcher, final ILogger logger,
			final ExpressionTranslation expressionTranslation, final boolean overapproximateFloatingPointOperations) {
//		mInitializedGlobals = new LinkedHashSet<>();
		mDispatcher = dispatcher;
		mLogger = logger;
		mExpressionTranslation = expressionTranslation;
		mOverapproximateFloatingPointOperations = overapproximateFloatingPointOperations;
		mBoogieTypeHelper = dispatcher.mCHandler.getBoogieTypeHelper();
	}

	/**
	 * Start method for the post processing.
	 *
	 * @param main
	 *            a reference to the main dispatcher.
	 * @param loc
	 *            the location of the translation unit.
	 * @param memoryHandler
	 * @param arrayHandler
	 *            a reference to the arrayHandler.
	 * @param structHandler
	 * @param typeHandler
	 * @param initStatements
	 *            a list of all global init statements.
	 * @param procedures
	 *            a list of all procedures in the TU.
	 * @param modifiedGlobals
	 *            modified globals for all procedures.
	 * @param undefinedTypes
	 *            a list of used, but not declared types.
	 * @param functions
	 *            a list of functions to add to the TU.
	 * @param mDeclarationsGlobalInBoogie
	 * @param expressionTranslation
	 * @param uninitGlobalVars
	 *            a set of uninitialized global variables.
	 * @return a declaration list holding the init() and start() procedure.
	 */
	public ArrayList<Declaration> postProcess(final Dispatcher main, final ILocation loc) {
//			final LinkedHashMap<Declaration, CDeclaration> mDeclarationsGlobalInBoogie) {
		final ArrayList<Declaration> decl = new ArrayList<>();


		final Set<String> undefinedTypes = main.mTypeHandler.getUndefinedTypes();
		decl.addAll(declareUndefinedTypes(loc, undefinedTypes));

		final UltimateInitProcedure initProcedure = new UltimateInitProcedure(loc, main);//, mDeclarationsGlobalInBoogie);
		decl.add(initProcedure.getUltimateInitImplementation());

		final UltimateStartProcedure startProcedure = new UltimateStartProcedure(main, loc);
		decl.add(startProcedure.getUltimateStartDeclaration());
//		decl.addAll(createUltimateStartProcedure(main, loc, functionHandler,
//				initProcedure.getUltimateInitModifiesClauseContents()));

		decl.addAll(declareFunctionPointerProcedures(main));
		decl.addAll(declareConversionFunctions(main));

		final TypeHandler typeHandler = (TypeHandler) main.mTypeHandler;

		if ((typeHandler).isBitvectorTranslation()) {
			final ExpressionTranslation expressionTranslation = main.mCHandler.getExpressionTranslation();

			decl.addAll(PostProcessor.declarePrimitiveDataTypeSynonyms(loc, main.getTypeSizes(), typeHandler));

			if ((typeHandler).areFloatingTypesNeeded()) {
				decl.addAll(PostProcessor.declareFloatDataTypes(loc, main.getTypeSizes(), typeHandler,
						mOverapproximateFloatingPointOperations, expressionTranslation));
			}

			final String[] importantFunctions = new String[] { "bvadd" };
			final BitvectorTranslation bitvectorTranslation = (BitvectorTranslation) expressionTranslation;
			bitvectorTranslation.declareBinaryBitvectorFunctionsForAllIntegerDatatypes(loc, importantFunctions);
		}
		return decl;
	}

	private ArrayList<Declaration> declareConversionFunctions(final Dispatcher main) {
//			final FunctionHandler functionHandler, final MemoryHandler memoryHandler,
//			final StructHandler structHandler) {

		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();

		final ArrayList<Declaration> decls = new ArrayList<>();

		// function to_int
		final String inReal = "inReal";
		// IdentifierExpression inRealIdex = new IdentifierExpression(ignoreLoc, inReal);
		final String outInt = "outInt";
		// IdentifierExpression outIntIdex = new IdentifierExpression(ignoreLoc, outInt);
		final VarList realParam = new VarList(ignoreLoc, new String[] {}, new PrimitiveType(ignoreLoc, SFO.REAL));
		final VarList[] oneRealParam = new VarList[] { realParam };
		final VarList intParam = new VarList(ignoreLoc, new String[] { outInt }, new PrimitiveType(ignoreLoc, SFO.INT));
		// VarList[] oneIntParam = new VarList[] { intParam };
		// Expression inRealGeq0 = new BinaryExpression(ignoreLoc,
		// BinaryExpression.Operator.COMPGEQ, inRealIdex, new IntegerLiteral(ignoreLoc, SFO.NR0));
		//
		// Expression roundDown = new BinaryExpression(ignoreLoc, BinaryExpression.Operator.LOGICAND,
		// new BinaryExpression(ignoreLoc, BinaryExpression.Operator.COMPLEQ,
		// new BinaryExpression(ignoreLoc, BinaryExpression.Operator.ARITHMINUS, inRealIdex, new
		// IntegerLiteral(ignoreLoc, SFO.NR1)),
		// outIntIdex),
		// new BinaryExpression(ignoreLoc, BinaryExpression.Operator.COMPLEQ,
		// outIntIdex,
		// inRealIdex));
		// Expression roundUp = new BinaryExpression(ignoreLoc, BinaryExpression.Operator.LOGICAND,
		// new BinaryExpression(ignoreLoc, BinaryExpression.Operator.COMPLEQ,
		// inRealIdex,
		// outIntIdex),
		// new BinaryExpression(ignoreLoc, BinaryExpression.Operator.COMPLEQ,
		// new BinaryExpression(ignoreLoc, BinaryExpression.Operator.ARITHPLUS, inRealIdex, new
		// IntegerLiteral(ignoreLoc, SFO.NR1)),
		// outIntIdex));
		//
		// Specification toIntSpec = new EnsuresSpecification(ignoreLoc, false, new IfThenElseExpression(ignoreLoc,
		// inRealGeq0, roundDown, roundUp));
		// decls.add(new Procedure(ignoreLoc, new Attribute[0], SFO.TO_INT, new String[0], oneRealParam, oneIntParam,
		// new Specification[] { toIntSpec }, null));

		if (mDeclareToIntFunction) {
			decls.add(new FunctionDeclaration(ignoreLoc, new Attribute[0], SFO.TO_INT, new String[0], oneRealParam,
					intParam));
		}

		return decls;
	}

	private ArrayList<Declaration> declareFunctionPointerProcedures(final Dispatcher main) {
		final FunctionHandler functionHandler = main.mCHandler.getFunctionHandler();
		final MemoryHandler memoryHandler = main.mCHandler.getMemoryHandler();


		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		final ArrayList<Declaration> result = new ArrayList<>();
		for (final ProcedureSignature cFunc : functionHandler.getFunctionsSignaturesWithFunctionPointers()) {
			final String procName = cFunc.toString();

			final VarList[] inParams = functionHandler.getProcedureDeclaration(procName).getInParams();
			final VarList[] outParams = functionHandler.getProcedureDeclaration(procName).getOutParams();
			assert outParams.length <= 1;
			final Procedure functionPointerMuxProc =
					new Procedure(ignoreLoc, new Attribute[0], procName, new String[0], inParams, outParams,
							// FIXME: it seems an odd convention that giving it "null" as Specification makes it an
							// implementation
							// (instead of a procedure) in Boogie
							// new Specification[0],
							null,
							// functionHandler.getFunctionPointerFunctionBody(ignoreLoc, main, memoryHandler,
							// structHandler, procName, cFunc, inParams, outParams));
							getFunctionPointerFunctionBody(ignoreLoc, main, functionHandler, memoryHandler,
									procName, cFunc, inParams, outParams));
			result.add(functionPointerMuxProc);
		}
		return result;
	}

	/**
	 * Declares a type for each identifier in the set.
	 *
	 * @param loc
	 *            the location to be used for the declarations.
	 * @param undefinedTypes
	 *            a list of undefined, but used types.
	 * @return a list of type declarations.
	 */
	private static Collection<? extends Declaration> declareUndefinedTypes(final ILocation loc,
			final Set<String> undefinedTypes) {
		final ArrayList<Declaration> decl = new ArrayList<>();
		for (final String s : undefinedTypes) {
			decl.add(new TypeDeclaration(loc, new Attribute[0], false, s, new String[0]));
		}
		return decl;
	}

//	/**
//	 *
//	 *
//	 * @param initStatements
//	 * @return
//	 */
//	private boolean assertInitializedGlobalsTracksAllInitializedVariables(final Collection<Statement> initStatements) {
//		for (final Statement stmt : initStatements) {
//			if (stmt instanceof AssignmentStatement) {
//				final AssignmentStatement ass = (AssignmentStatement) stmt;
//				assert ass.getLhs().length == 1; // by construction ...
//				final LeftHandSide lhs = ass.getLhs()[0];
//				final String id = BoogieASTUtil.getLHSId(lhs);
//				if (!mInitializedGlobals.contains(id)) {
//					return false;
//				}
//			}
//		}
//		return true;
//	}

	/**
	 * Generate type declarations like, e.g., the following. type { :isUnsigned true } { :bitsize 16 } C_USHORT = bv16;
	 * This allow us to use type synonyms like C_USHORT during the translation. This is yet not consequently
	 * implemented. This is desired not only for bitvectors: it makes our translation more modular and can ease
	 * debugging. However, that this located in this class and fixed to bitvectors is a workaround.
	 *
	 * @param typeHandler
	 */
	public static ArrayList<Declaration> declarePrimitiveDataTypeSynonyms(final ILocation loc,
			final TypeSizes typeSizes, final TypeHandler typeHandler) {
		final ArrayList<Declaration> decls = new ArrayList<>();
		for (final CPrimitive.CPrimitives cPrimitive : CPrimitive.CPrimitives.values()) {
			final CPrimitive cPrimitiveO = new CPrimitive(cPrimitive);
			if (cPrimitiveO.getGeneralType() == CPrimitiveCategory.INTTYPE) {
				final Attribute[] attributes = new Attribute[2];
				attributes[0] = new NamedAttribute(loc, "isUnsigned",
						new Expression[] { new BooleanLiteral(loc, typeSizes.isUnsigned(cPrimitiveO)) });
				final int bytesize = typeSizes.getSize(cPrimitive);
				final int bitsize = bytesize * 8;
				attributes[1] = new NamedAttribute(loc, "bitsize",
						new Expression[] { new IntegerLiteral(loc, String.valueOf(bitsize)) });
				final String identifier = "C_" + cPrimitive.name();
				final String[] typeParams = new String[0];
				final String name = "bv" + bitsize;
				final ASTType astType = typeHandler.bytesize2asttype(loc, CPrimitiveCategory.INTTYPE, bytesize);
				decls.add(new TypeDeclaration(loc, attributes, false, identifier, typeParams, astType));
			}
		}
		return decls;
	}

	/**
	 * Generate FloatingPoint types
	 *
	 * @param loc
	 * @param typesizes
	 * @param typeHandler
	 * @param expressionTranslation
	 * @return
	 */
	public static ArrayList<Declaration> declareFloatDataTypes(final ILocation loc, final TypeSizes typesizes,
			final TypeHandler typeHandler, final boolean overapproximateFloat,
			final ExpressionTranslation expressionTranslation) {
		final ArrayList<Declaration> decls = new ArrayList<>();

		// Roundingmodes, for now RNE hardcoded
		final Attribute[] attributesRM;
		if (overapproximateFloat) {
			attributesRM = new Attribute[0];
		} else {
			final String smtlibRmIdentifier = "RoundingMode";
			attributesRM = new Attribute[1];
			attributesRM[0] = new NamedAttribute(loc, FunctionDeclarations.BUILTIN_IDENTIFIER,
					new Expression[] { new StringLiteral(loc, smtlibRmIdentifier) });
		}
		final String[] typeParamsRM = new String[0];
		decls.add(new TypeDeclaration(loc, attributesRM, false, BitvectorTranslation.BOOGIE_ROUNDING_MODE_IDENTIFIER,
				typeParamsRM));

		final Attribute[] attributesRNE;
		final Attribute[] attributesRTZ;
		if (overapproximateFloat) {
			attributesRNE = new Attribute[0];
			attributesRTZ = new Attribute[0];
		} else {
			final Attribute attributeRNE = new NamedAttribute(loc, FunctionDeclarations.BUILTIN_IDENTIFIER,
					new Expression[] { new StringLiteral(loc, "RNE") });
			final Attribute attributeRTZ = new NamedAttribute(loc, FunctionDeclarations.BUILTIN_IDENTIFIER,
					new Expression[] { new StringLiteral(loc, "RTZ") });
			attributesRNE = new Attribute[] { attributeRNE };
			attributesRTZ = new Attribute[] { attributeRTZ };
		}
		decls.add(new ConstDeclaration(loc, attributesRNE, false,
				new VarList(loc, new String[] { BitvectorTranslation.BOOGIE_ROUNDING_MODE_RNE },
						new NamedType(loc, BitvectorTranslation.BOOGIE_ROUNDING_MODE_IDENTIFIER, new ASTType[0])),
				null, false));
		decls.add(new ConstDeclaration(loc, attributesRTZ, false,
				new VarList(loc, new String[] { BitvectorTranslation.BOOGIE_ROUNDING_MODE_RTZ },
						new NamedType(loc, BitvectorTranslation.BOOGIE_ROUNDING_MODE_IDENTIFIER, new ASTType[0])),
				null, false));

		for (final CPrimitive.CPrimitives cPrimitive : CPrimitive.CPrimitives.values()) {

			final CPrimitive cPrimitive0 = new CPrimitive(cPrimitive);

			if (cPrimitive0.getGeneralType() == CPrimitiveCategory.FLOATTYPE && !cPrimitive0.isComplexType()) {

				if (!overapproximateFloat) {
					final BitvectorTranslation bt = ((BitvectorTranslation) expressionTranslation);
					// declare floating point constructors here because we might
					// always need them for our backtranslation
					bt.declareFloatingPointConstructors(loc, new CPrimitive(cPrimitive));
					bt.declareFloatConstant(loc, BitvectorTranslation.SMT_LIB_MINUS_INF, new CPrimitive(cPrimitive));
					bt.declareFloatConstant(loc, BitvectorTranslation.SMT_LIB_PLUS_INF, new CPrimitive(cPrimitive));
					bt.declareFloatConstant(loc, BitvectorTranslation.SMT_LIB_NAN, new CPrimitive(cPrimitive));
					bt.declareFloatConstant(loc, BitvectorTranslation.SMT_LIB_MINUS_ZERO, new CPrimitive(cPrimitive));
					bt.declareFloatConstant(loc, BitvectorTranslation.SMT_LIB_PLUS_ZERO, new CPrimitive(cPrimitive));
				}

				final Attribute[] attributes;
				if (overapproximateFloat) {
					attributes = new Attribute[0];
				} else {
					attributes = new Attribute[2];
					attributes[0] = new NamedAttribute(loc, FunctionDeclarations.BUILTIN_IDENTIFIER,
							new Expression[] { new StringLiteral(loc, "FloatingPoint") });
					final int bytesize = typesizes.getSize(cPrimitive);
					final int[] indices = new int[2];
					switch (bytesize) {
					case 4:
						indices[0] = 8;
						indices[1] = 24;
						break;
					case 8:
						indices[0] = 11;
						indices[1] = 53;
						break;
					case 12: // because of 80bit long doubles on linux x86
					case 16:
						indices[0] = 15;
						indices[1] = 113;
						break;
					default:
						throw new UnsupportedSyntaxException(loc, "unknown primitive type");
					}
					attributes[1] = new NamedAttribute(loc, FunctionDeclarations.INDEX_IDENTIFIER,
							new Expression[] { new IntegerLiteral(loc, String.valueOf(indices[0])),
									new IntegerLiteral(loc, String.valueOf(indices[1])) });
				}
				final String identifier = "C_" + cPrimitive.name();
				final String[] typeParams = new String[0];
				decls.add(new TypeDeclaration(loc, attributes, false, identifier, typeParams));
			}
		}
		return decls;
	}

	/**
	 * Generate the body for one of our internal function pointer dispatching procedures.
	 * See also {@link FunctionHandler.handleFunctionPointerCall} on how we treat function pointers.
	 *
	 *
	 * @param loc
	 * @param main
	 * @param functionHandler
	 * @param memoryHandler
	 * @param structHandler
	 * @param dispatchingProcedureName
	 * 			name of the dispatching procedure
	 * @param funcSignature
	 * 			signature of the dispatching procedure
	 * @param inParams
	 * 			in parameters of the dispatching procedure as it has been registered in FunctionHandler
	 * @param outParam
	 * 			out parameters of the dispatching procedure as it has been registered in FunctionHandler
	 * @return
	 */
	public Body getFunctionPointerFunctionBody(final ILocation loc, final Dispatcher main,
			final FunctionHandler functionHandler, final MemoryHandler memoryHandler,
			final String dispatchingProcedureName, final ProcedureSignature funcSignature, final VarList[] inParams,
			final VarList[] outParam) {

		final StructHandler structHandler = main.mCHandler.getStructHandler();

		final boolean resultTypeIsVoid = (funcSignature.getReturnType() == null);

//		final List<Statement> stmt = new ArrayList<>();
//		final List<VariableDeclaration> decl = new ArrayList<>();
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();

		/*
		 * Setup the input parameters for the dispatched procedures.
		 * The last inParam of the dispatching procedure is the function pointer in this case, which is not given to
		 *  the dispatched procedures.
		 *  --> therefore we iterate to inParams.lenth - 1 only..
		 */
		final ArrayList<Expression> args = new ArrayList<>();
		for (int i = 0; i < inParams.length - 1; i++) {
			final VarList vl = inParams[i];
			assert vl.getIdentifiers().length == 1;
			final String oldId = vl.getIdentifiers()[0];
			final String newId = oldId.replaceFirst("in", "");
//			decl.add(new VariableDeclaration(loc, new Attribute[0],
//					new VarList[] { new VarList(loc, new String[] { newId }, vl.getType()) }));
			builder.addDeclaration(new VariableDeclaration(loc, new Attribute[0],
					new VarList[] { new VarList(loc, new String[] { newId }, vl.getType()) }));
//			stmt.add(new AssignmentStatement(loc, new LeftHandSide[] { new VariableLHS(loc, newId) },
//					new Expression[] { new IdentifierExpression(loc, oldId) }));
			final IdentifierExpression oldIdExpr = //new IdentifierExpression(loc, oldId);
					ExpressionFactory.constructIdentifierExpression(loc,
							mBoogieTypeHelper.getBoogieTypeForBoogieASTType(vl.getType()), oldId,
							new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, dispatchingProcedureName));
			final VariableLHS newIdLhs = //new VariableLHS(loc, newId);
					ExpressionFactory.constructVariableLHS(loc,
							mBoogieTypeHelper.getBoogieTypeForBoogieASTType(vl.getType()),
							newId, new DeclarationInformation(StorageClass.LOCAL, dispatchingProcedureName));
			builder.addStatement(new AssignmentStatement(loc, new LeftHandSide[] { newIdLhs },
					new Expression[] { oldIdExpr }));
			final IdentifierExpression newIdIdExpr = //new IdentifierExpression(loc, newId);
					ExpressionFactory.constructIdentifierExpression(loc,
							mBoogieTypeHelper.getBoogieTypeForBoogieASTType(vl.getType()),
							newId, new DeclarationInformation(StorageClass.LOCAL, dispatchingProcedureName));
			args.add(newIdIdExpr);
		}

		// collect all functions that are addressoffed in the program and that
		// match the signature
		final ArrayList<String> fittingFunctions = new ArrayList<>();
		for (final Entry<String, Integer> en : main.getFunctionToIndex().entrySet()) {
			final CFunction ptdToFuncType = functionHandler.getCFunctionType(en.getKey());
			// if (ptdToFuncType.isCompatibleWith(calledFuncType)) {
			if (new ProcedureSignature(main, ptdToFuncType).equals(funcSignature)) {
				fittingFunctions.add(en.getKey());
			}
		}

		// add the functionPointerProcedure and the procedures it calls to the
		// call graph and modifiedGlobals
		// such that calculateTransitive (which is executed later, in
		// visit(TranslationUnit) after the postprocessor)
		// can compute the correct modifies clause
//		functionHandler.addModifiedGlobalEntry(fpfName);
		for (final String fittingFunc : fittingFunctions) {
//			functionHandler.addCallGraphEdge(fpfName, fittingFunc);
			functionHandler.registerCall(dispatchingProcedureName, fittingFunc);
		}

		// generate the actual body
		IdentifierExpression funcCallResult = null;
		if (fittingFunctions.isEmpty()) {
//			return new Body(loc, decl.toArray(new VariableDeclaration[decl.size()]),
//					stmt.toArray(new Statement[stmt.size()]));
			return new Body(loc,
					builder.getDeclarations().toArray(new VariableDeclaration[builder.getDeclarations().size()]),
					builder.getStatements().toArray(new Statement[builder.getStatements().size()]));
		} else if (fittingFunctions.size() == 1) {
//			final ExpressionResult rex = (ExpressionResult) functionHandler.makeTheFunctionCallItself(main, loc,
//					fittingFunctions.get(0), new ArrayList<Statement>(), new ArrayList<Declaration>(),
//					new LinkedHashMap<VariableDeclaration, ILocation>(), new ArrayList<Overapprox>(), args);
			final ExpressionResult rex = (ExpressionResult) functionHandler.makeTheFunctionCallItself(main, loc,
					fittingFunctions.get(0), new ExpressionResultBuilder(), args);
			funcCallResult = (IdentifierExpression) rex.mLrVal.getValue();
//			for (final Declaration dec : rex.mDecl) {
//				decl.add((VariableDeclaration) dec);
//			}
//			stmt.addAll(rex.mStmt);
			builder.addAllExceptLrValue(rex);

			assert outParam.length <= 1;
			if (outParam.length == 1) {
//				stmt.add(new AssignmentStatement(loc,
//						new LeftHandSide[] { new VariableLHS(loc, outParam[0].getIdentifiers()[0]) },
//						new Expression[] { funcCallResult }));
				final String id = outParam[0].getIdentifiers()[0];
				final ASTType astType = outParam[0].getType();
				final VariableLHS lhs = //new VariableLHS(loc, outParam[0].getIdentifiers()[0]);
						ExpressionFactory.constructVariableLHS(loc,
								mBoogieTypeHelper.getBoogieTypeForBoogieASTType(astType),
								id,
								new DeclarationInformation(StorageClass.IMPLEMENTATION_OUTPARAM,
										dispatchingProcedureName));
				builder.addStatement(new AssignmentStatement(loc,
						new LeftHandSide[] { lhs },
						new Expression[] { funcCallResult }));
			}
//			stmt.addAll(CHandler.createHavocsForAuxVars(rex.mAuxVars));
			builder.addStatements(CHandler.createHavocsForAuxVars(rex.mAuxVars));
//			stmt.add(new ReturnStatement(loc));
			builder.addStatement(new ReturnStatement(loc));

			return new Body(loc,
//					decl.toArray(new VariableDeclaration[decl.size()]),
					builder.getDeclarations().toArray(new VariableDeclaration[builder.getDeclarations().size()]),
					builder.getStatements().toArray(new Statement[builder.getStatements().size()]));
		} else {
//			final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();

//			final String tmpId = null;
			AuxVarInfo auxvar = null;
			if (!resultTypeIsVoid) {
//				tmpId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.FUNCPTRRES, null);
//				final VariableDeclaration tmpVarDec = new VariableDeclaration(loc, new Attribute[0],
//						new VarList[] { new VarList(loc, new String[] { tmpId }, funcSignature.getReturnType()) });
				auxvar = CTranslationUtil.constructAuxVarInfo(loc, main,
						funcSignature.getReturnType(),
						SFO.AUXVAR.FUNCPTRRES);
//				decl.add(tmpVarDec);
				builder.addDeclaration(auxvar.getVarDec());
//				auxVars.put(tmpVarDec, loc);
				builder.addAuxVar(auxvar);
				funcCallResult = //new IdentifierExpression(loc, tmpId);
//						ExpressionFactory.constructIdentifierExpression(loc,
//								mBoogieTypeHelper.getBoogieTypeForPointerType(), tmpId,
//								new DeclarationInformation(StorageClass.LOCAL, dispatchingProcedureName));
						auxvar.getExp();
			}

//			final ExpressionResult firstElseRex = (ExpressionResult) functionHandler.makeTheFunctionCallItself(main,
//					loc, fittingFunctions.get(0), new ArrayList<Statement>(), new ArrayList<Declaration>(),
//					new LinkedHashMap<VariableDeclaration, ILocation>(), new ArrayList<Overapprox>(), args);
			final ExpressionResult firstElseRex = (ExpressionResult) functionHandler.makeTheFunctionCallItself(main,
					loc, fittingFunctions.get(0), new ExpressionResultBuilder(), args);
			for (final Declaration dec : firstElseRex.mDecl) {
//				decl.add((VariableDeclaration) dec);
				builder.addDeclaration(dec);
			}
//			auxVars.putAll(firstElseRex.mAuxVars);
//			builder.putAuxVars(firstElseRex.getAuxVars());
			builder.addAuxVars(firstElseRex.getAuxVars());

			final ArrayList<Statement> firstElseStmt = new ArrayList<>();
			firstElseStmt.addAll(firstElseRex.mStmt);
			if (!resultTypeIsVoid) {
				final AssignmentStatement assignment =
						new AssignmentStatement(loc, new VariableLHS[] { auxvar.getLhs() },
								new Expression[] { firstElseRex.mLrVal.getValue() });
				firstElseStmt.add(assignment);
			}
			IfStatement currentIfStmt = null;

			for (int i = 1; i < fittingFunctions.size(); i++) {
//				final ExpressionResult currentRex = (ExpressionResult) functionHandler.makeTheFunctionCallItself(main,
//						loc, fittingFunctions.get(i), new ArrayList<Statement>(), new ArrayList<Declaration>(),
//						new LinkedHashMap<VariableDeclaration, ILocation>(), new ArrayList<Overapprox>(), args);
				final ExpressionResult currentRex = (ExpressionResult) functionHandler.makeTheFunctionCallItself(main,
						loc, fittingFunctions.get(i), new ExpressionResultBuilder(), args);
				for (final Declaration dec : currentRex.mDecl) {
//					decl.add((VariableDeclaration) dec);
					builder.addDeclaration(dec);
				}
//				auxVars.putAll(currentRex.mAuxVars);
				builder.addAuxVars(currentRex.mAuxVars);

				final ArrayList<Statement> newStmts = new ArrayList<>();
				newStmts.addAll(currentRex.mStmt);
				if (!resultTypeIsVoid) {
					final AssignmentStatement assignment =
							new AssignmentStatement(loc, new VariableLHS[] { auxvar.getLhs() },
									new Expression[] { currentRex.mLrVal.getValue() });
					newStmts.add(assignment);
				}

				final IdentifierExpression functionPointerIdex =
//						new IdentifierExpression(loc, inParams[inParams.length - 1].getIdentifiers()[0]);
						mBoogieTypeHelper.constructIdentifierExpression(loc, inParams[inParams.length -1].getType(),
								inParams[inParams.length - 1].getIdentifiers()[0],
								StorageClass.IMPLEMENTATION_INPARAM, dispatchingProcedureName);
				final IdentifierExpression functionPointerValueOfCurrentFittingFunctionIdex =
//						new IdentifierExpression(loc, SFO.FUNCTION_ADDRESS + fittingFunctions.get(i));
						mBoogieTypeHelper.constructIdentifierExpression(loc,
								mBoogieTypeHelper.getBoogieTypeForPointerType(),
								SFO.FUNCTION_ADDRESS + fittingFunctions.get(i),
								StorageClass.IMPLEMENTATION_INPARAM, dispatchingProcedureName);
				final Expression condition =
						ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ,
								functionPointerIdex, functionPointerValueOfCurrentFittingFunctionIdex);

				if (i == 1) {
					currentIfStmt = new IfStatement(loc, condition, newStmts.toArray(new Statement[newStmts.size()]),
							firstElseStmt.toArray(new Statement[firstElseStmt.size()]));
				} else {
					currentIfStmt = new IfStatement(loc, condition, newStmts.toArray(new Statement[newStmts.size()]),
							new Statement[] { currentIfStmt });
				}
			}

//			stmt.add(currentIfStmt);
			builder.addStatement(currentIfStmt);
			if (outParam.length == 1) {
//				stmt.add(new AssignmentStatement(loc,
//						new LeftHandSide[] { new VariableLHS(loc, outParam[0].getIdentifiers()[0]) },
//						new Expression[] { funcCallResult }));
				final VariableLHS dispatchingFunctionResultLhs = //new VariableLHS(loc, outParam[0].getIdentifiers()[0]);
						ExpressionFactory.constructVariableLHS(loc,
								mBoogieTypeHelper.getBoogieTypeForBoogieASTType(outParam[0].getType()),
								outParam[0].getIdentifiers()[0],
								new DeclarationInformation(StorageClass.IMPLEMENTATION_OUTPARAM,
										dispatchingProcedureName));
				builder.addStatement(new AssignmentStatement(loc,
						new LeftHandSide[] { dispatchingFunctionResultLhs },
						new Expression[] { funcCallResult }));
			}
//			stmt.addAll(CHandler.createHavocsForAuxVars(auxVars));
//			stmt.add(new ReturnStatement(loc));
//			return new Body(loc, decl.toArray(new VariableDeclaration[decl.size()]),
//					stmt.toArray(new Statement[stmt.size()]));
			builder.addStatements(CHandler.createHavocsForAuxVars(builder.getAuxVars()));
			builder.addStatement(new ReturnStatement(loc));
			return new Body(loc,
					builder.getDeclarations().toArray(new VariableDeclaration[builder.getDeclarations().size()]),
					builder.getStatements().toArray(new Statement[builder.getStatements().size()]));
		}
	}

	class UltimateInitProcedure {

		private Declaration mUltimateInitImplementation;
//		private final List<VariableLHS> mModifiesClauseContents;

		UltimateInitProcedure(final ILocation translationUnitLoc, final Dispatcher main) {//,
//				final LinkedHashMap<Declaration, CDeclaration> declarationsGlobalInBoogie) {
//			mModifiesClauseContents = new ArrayList<>();
			createInit(translationUnitLoc, main);//, declarationsGlobalInBoogie);
		}

		void createInit(final ILocation translationUnitLoc, final Dispatcher main) {
//			final LinkedHashMap<Declaration, CDeclaration> declarationsGlobalInBoogie) {

			final MemoryHandler memoryHandler = main.mCHandler.getMemoryHandler();
			final ExpressionTranslation expressionTranslation = main.mCHandler.getExpressionTranslation();

			main.mCHandler.getFunctionHandler().beginUltimateInitOrStart(main, translationUnitLoc, SFO.INIT);
			final ArrayList<Statement> initStatements = new ArrayList<>();
			final Collection<String> proceduresCalledByUltimateInit = new HashSet<>();

//			final ArrayList<Declaration> decl = new ArrayList<>();
			final ArrayList<VariableDeclaration> initDecl = new ArrayList<>();

			if (main.mCHandler.getMemoryHandler().getRequiredMemoryModelFeatures()
					.isMemoryModelInfrastructureRequired()) {

				// set #valid[0] = 0 (i.e., the memory at the NULL-pointer is not allocated)
				final Expression zero = mExpressionTranslation.constructLiteralForIntegerType(translationUnitLoc,
						mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO);
//				final String lhsId = SFO.VALID;
				final Expression literalThatRepresentsFalse = memoryHandler.getBooleanArrayHelper().constructFalse();
				final AssignmentStatement assignment = MemoryHandler.constructOneDimensionalArrayUpdate(
						translationUnitLoc, zero, memoryHandler.getValidArrayLhs(translationUnitLoc),
						literalThatRepresentsFalse);
				initStatements.add(0, assignment);
//				mInitializedGlobals.add(SFO.VALID);

				// set the value of the NULL-constant to NULL = { base : 0, offset : 0 }
				final VariableLHS slhs = //new VariableLHS(translationUnitLoc, SFO.NULL);
						ExpressionFactory.constructVariableLHS(translationUnitLoc,
								mBoogieTypeHelper.getBoogieTypeForPointerType(),
								SFO.NULL,
								DeclarationInformation.DECLARATIONINFO_GLOBAL);
				initStatements.add(0, new AssignmentStatement(translationUnitLoc, new LeftHandSide[] { slhs },
						new Expression[] { new StructConstructor(translationUnitLoc, new String[] { "base", "offset" },
								new Expression[] {
										expressionTranslation.constructLiteralForIntegerType(translationUnitLoc,
												expressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO),
										expressionTranslation.constructLiteralForIntegerType(translationUnitLoc,
												expressionTranslation.getCTypeOfPointerComponents(),
												BigInteger.ZERO) }) }));
//				mInitializedGlobals.add(SFO.NULL);
			}
//			assert assertInitializedGlobalsTracksAllInitializedVariables(initStatements);

			// initialization for statics and other globals
//			for (final Entry<Declaration, CDeclaration> en : declarationsGlobalInBoogie.entrySet()) {
			for (final Entry<VariableDeclaration, CDeclaration> en :
					main.mCHandler.getStaticObjectsHandler().getGlobalVariableDeclsWithAssociatedCDecls().entrySet()) {
//				if (en.getKey() instanceof TypeDeclaration || en.getKey() instanceof ConstDeclaration) {
//					continue;
//				}
				final ILocation currentDeclsLoc = en.getKey().getLocation();
				final InitializerResult initializer = en.getValue().getInitializer();

				/*
				 * global variables with external linkage are not implicitly initialized. (They are initialized by the
				 * module that provides them..)
				 */
				if (en.getValue().isExtern()) {
					continue;
				}

				for (final VarList vl : en.getKey().getVariables()) {
					for (final String id : vl.getIdentifiers()) {

						final VariableLHS lhs = //new VariableLHS(currentDeclsLoc, id);
								ExpressionFactory.constructVariableLHS(currentDeclsLoc,
										main.mCHandler.getBoogieTypeHelper()
											.getBoogieTypeForBoogieASTType(vl.getType()),
										id,
										DeclarationInformation.DECLARATIONINFO_GLOBAL);

						if (main.mCHandler.isHeapVar(id)) {
							final LocalLValue llVal =
									new LocalLValue(lhs, en.getValue().getType(), null);
							initStatements.add(memoryHandler.getMallocCall(llVal, currentDeclsLoc));
							proceduresCalledByUltimateInit.add(MemoryModelDeclarations.Ultimate_Alloc.name());
						}

						final ExpressionResult initRex = main.mCHandler.getInitHandler().initialize(currentDeclsLoc,
								main, lhs, en.getValue().getType(), initializer);
						for (final Statement stmt : initRex.getStatements()) {
							if (stmt instanceof CallStatement) {
								proceduresCalledByUltimateInit.add(((CallStatement) stmt).getMethodName());
							}
							initStatements.add(stmt);
						}
						initStatements.addAll(CHandler.createHavocsForAuxVars(initRex.mAuxVars));
						for (final Declaration d : initRex.mDecl) {
							initDecl.add((VariableDeclaration) d);
						}
					}
				}
				for (final VarList vl : en.getKey().getVariables()) {
//					mInitializedGlobals.addAll(Arrays.asList(vl.getIdentifiers()));
				}
			}


			/*
			 * perhaps move more functionality into the following section, once StaticObjectsHandler is used more widely
			 */
			main.mCHandler.getStaticObjectsHandler().freeze();
			initStatements.addAll(main.mCHandler.getStaticObjectsHandler().getStatementsForUltimateInit());
//			mInitializedGlobals.addAll(main.mCHandler.getStaticObjectsHandler().getVariablesModifiedByUltimateInit());

			// should not be necessary:
//			mInitializedGlobals.addAll(functionHandler.getModifiedGlobals().get(SFO.INIT));

//			final Specification[] specsInit = new Specification[1];
//
//
//			for (final String varName : mInitializedGlobals) {
//				mModifiesClauseContents.add(new VariableLHS(translationUnitLoc, varName));
//			}
//			specsInit[0] = new ModifiesSpecification(translationUnitLoc, false,
//					mModifiesClauseContents.toArray(new VariableLHS[mModifiesClauseContents.size()]));

			/*
			 * note that we only have to deal with the implementation part of the procedure, the declaration is managed
			 * by the FunctionHandler
			 */
			final Body initBody = new Body(translationUnitLoc,
					initDecl.toArray(new VariableDeclaration[initDecl.size()]),
					initStatements.toArray(new Statement[initStatements.size()]));
			final Procedure initProcedureImplementation = new Procedure(translationUnitLoc, new Attribute[0],
					SFO.INIT, new String[0], new VarList[0], new VarList[0], null, initBody);


//			final Procedure initProcedureDecl = new Procedure(translationUnitLoc, new Attribute[0], SFO.INIT,
//					new String[0], new VarList[0], new VarList[0], specsInit, null);

//			proceduresCalledByUltimateInit.addAll(
//					main.mCHandler.getStaticObjectsHandler().getProceduresCalledByUltimateInit());

//			functionHandler.endUltimateInitOrStart(main, initProcedureDecl, SFO.INIT, proceduresCalledByUltimateInit);
//			functionHandler.endUltimateInitOrStart(main, initProcedureDecl, SFO.INIT);
			main.mCHandler.getFunctionHandler().endUltimateInitOrStart(main, SFO.INIT);

			mUltimateInitImplementation = initProcedureImplementation;
		}

		public Declaration getUltimateInitImplementation() {
			return mUltimateInitImplementation;
		}

//		public List<VariableLHS> getUltimateInitModifiesClauseContents() {
//			return  mModifiesClauseContents;
//		}

	}


	class UltimateStartProcedure {

		private Procedure mStartProcedure;

		UltimateStartProcedure(final Dispatcher main, final ILocation loc) {
			createStartProc(main, loc);
		}

		void createStartProc(final Dispatcher main, final ILocation loc) {

			final FunctionHandler functionHandler = main.mCHandler.getFunctionHandler();

//			final Map<String, Procedure> procedures = functionHandler.getProcedures();
			final String checkedMethod = main.getCheckedMethod();

			Procedure startProcedure = null;

			if (!checkedMethod.equals(SFO.EMPTY) && functionHandler.hasProcedure(checkedMethod)) {
				mLogger.info("Settings: Checked method=" + checkedMethod);

				functionHandler.beginUltimateInitOrStart(main, loc, SFO.START);

//				Procedure startDeclaration = null;
//				Specification[] specsStart = new Specification[0];

//				functionHandler.addCallGraphEdge(SFO.START, SFO.INIT);
//				functionHandler.addCallGraphEdge(SFO.START, checkedMethod);

				final ArrayList<Statement> startStmt = new ArrayList<>();
				final ArrayList<VariableDeclaration> startDecl = new ArrayList<>();
//				specsStart = new Specification[1];
				startStmt.add(new CallStatement(loc, false, new VariableLHS[0], SFO.INIT, new Expression[0]));
				final VarList[] checkedMethodOutParams =
						functionHandler.getProcedureDeclaration(checkedMethod).getOutParams();
				final VarList[] checkedMethodInParams =
						functionHandler.getProcedureDeclaration(checkedMethod).getInParams();
				final Specification[] checkedMethodSpec =
						functionHandler.getProcedureDeclaration(checkedMethod).getSpecification();

				// find out the requires specs of the checked method and assume it before its start
				final ArrayList<Statement> reqSpecsAssumes = new ArrayList<>();
				for (final Specification spec : checkedMethodSpec) {
					if (spec instanceof RequiresSpecification) {
						reqSpecsAssumes.add(new AssumeStatement(loc, ((RequiresSpecification) spec).getFormula()));
					}
				}
				startStmt.addAll(reqSpecsAssumes);

				final ArrayList<Expression> args = new ArrayList<>();
				if (checkedMethodInParams.length > 0) {
					startDecl.add(new VariableDeclaration(loc, new Attribute[0], checkedMethodInParams));
					for (final VarList arg : checkedMethodInParams) {
						assert arg.getIdentifiers().length == 1; // by construction
						final String id = arg.getIdentifiers()[0];
						final IdentifierExpression idEx = //new IdentifierExpression(loc, id);
								mBoogieTypeHelper.constructIdentifierExpression(loc,
										arg.getType(), id, StorageClass.LOCAL, SFO.START);
						args.add(idEx);
					}
				}
				if (checkedMethodOutParams.length != 0) {
					assert checkedMethodOutParams.length == 1;
					// there is 1(!) return value
//					final String checkMethodRet = main.mNameHandler.getTempVarUID(SFO.AUXVAR.RETURNED, null);
//					final VarList tempVar =
//							new VarList(loc, new String[] { checkMethodRet }, checkedMethodOutParams[0].getType());
//					final VariableDeclaration tmpVar =
//							new VariableDeclaration(loc, new Attribute[0], new VarList[] { tempVar });
					final CType checkedMethodResultCType =
							functionHandler.getCFunctionType(checkedMethod).getResultType();
					final AuxVarInfo checkedMethodReturnAuxVar = CTranslationUtil.constructAuxVarInfo(loc, main,
							checkedMethodResultCType, SFO.AUXVAR.RETURNED);
					main.mCHandler.getSymbolTable().addToReverseMap(
							checkedMethodReturnAuxVar.getExp().getIdentifier(),
							SFO.NO_REAL_C_VAR + checkedMethodReturnAuxVar.getExp().getIdentifier(),
//							checkMethodRet,
//							SFO.NO_REAL_C_VAR + checkMethodRet,
							loc);
					startDecl.add(checkedMethodReturnAuxVar.getVarDec());
					startStmt.add(new CallStatement(loc, false,
							new VariableLHS[] { checkedMethodReturnAuxVar.getLhs() },
							checkedMethod, args.toArray(new Expression[args.size()])));
				} else { // void
					startStmt.add(new CallStatement(loc, false, new VariableLHS[0], checkedMethod,
							args.toArray(new Expression[args.size()])));
				}

//				final LinkedHashSet<VariableLHS> startModifiesClause = new LinkedHashSet<>();
//				for (final String id : mInitializedGlobals) {
//					startModifiesClause.add(new VariableLHS(loc, id));
//				}

				// should not be necessary if we treat start and init as normal procedures
//				for (final String id : functionHandler.getModifiedGlobals().get(checkedMethod)) {
//					startModifiesClause.add(new VariableLHS(loc, id));
//				}

//				specsStart[0] = new ModifiesSpecification(loc, false,
//						startModifiesClause.toArray(new VariableLHS[startModifiesClause.size()]));

				final Body startBody = new Body(loc, startDecl.toArray(new VariableDeclaration[startDecl.size()]),
						startStmt.toArray(new Statement[startStmt.size()]));

				startProcedure = new Procedure(loc, new Attribute[0], SFO.START, new String[0], new VarList[0],
						new VarList[0], null, startBody);

				/* note that we only deal with the implementation of the procedure here, the declaration is managed
				 * by the FucntionHandler
				 */
//				final Procedure startDeclaration = new Procedure(loc, new Attribute[0], SFO.START, new String[0],
//						new VarList[0], new VarList[0], specsStart, null);

//				final List<String> proceduresCalledByStart = Arrays.asList(new String[] { SFO.INIT, checkedMethod });

//				functionHandler.endUltimateInitOrStart(main, startDeclaration, SFO.START, proceduresCalledByStart);
//				functionHandler.endUltimateInitOrStart(main, startDeclaration, SFO.START);
				functionHandler.endUltimateInitOrStart(main, SFO.START);
			} else {
				mLogger.info("Settings: Library mode!");
				if (functionHandler.hasProcedure(SFO.MAIN)) {
					final String msg =
							"You selected the library mode (i.e., each procedure can be starting procedure and global "
							+ "variables are not initialized). This program contains a \"main\" procedure. Maybe you "
							+ "wanted to select the \"main\" procedure as starting procedure.";
					mDispatcher.warn(loc, msg);
				}
			}

			mStartProcedure = startProcedure;
		}

		public Declaration getUltimateStartDeclaration() {
			return mStartProcedure;
		}
	}
}
