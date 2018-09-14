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
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RequiresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CTranslationResultReporter;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CTranslationUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.FunctionDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler.MemoryModelDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.BitvectorTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
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
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Class caring for some post processing steps, like creating an initializer procedure and the start procedure.
 *
 * @author Markus Lindenmann
 * @date 12.10.2012
 */
public class PostProcessor {

	private final ILogger mLogger;

	private final ExpressionTranslation mExpressionTranslation;
	private final CTranslationResultReporter mReporter;

	/*
	 * Decides if the PostProcessor declares the special function that we use for converting Boogie-Real to a
	 * Boogie-Int. This is needed when we do a cast from float to int in C.
	 */
	private final boolean mDeclareToIntFunction = false;

	private final ITypeHandler mTypeHandler;

	private final AuxVarInfoBuilder mAuxVarInfoBuilder;

	private final FlatSymbolTable mSymboltable;

	private final MemoryHandler mMemoryHandler;

	private final ProcedureManager mProcedureManager;

	private final CHandler mCHandler;

	private final TypeSizes mTypeSize;

	private final StaticObjectsHandler mStaticObjectsHandler;

	private final InitializationHandler mInitHandler;

	private final TranslationSettings mSettings;

	private final FunctionHandler mFunctionhandler;

	private final Map<String, Integer> mFunctionToIndex;

	/**
	 * Constructor.
	 *
	 * @param overapproximateFloatingPointOperations
	 * @param services
	 * @param typeHandler
	 * @param reporter
	 * @param checkedMethod
	 * @param auxVarInfoBuilder
	 * @param functionToIndex
	 * @param typeSizes
	 * @param symbolTable
	 * @param staticObjectsHandler
	 * @param settings
	 * @param procedureManager
	 * @param memoryHandler
	 * @param initHandler
	 * @param functionhandler
	 * @param chandler
	 */
	public PostProcessor(final ILogger logger, final ExpressionTranslation expressionTranslation,
			final ITypeHandler typeHandler, final CTranslationResultReporter reporter,
			final AuxVarInfoBuilder auxVarInfoBuilder, final Map<String, Integer> functionToIndex,
			final TypeSizes typeSizes, final FlatSymbolTable symbolTable,
			final StaticObjectsHandler staticObjectsHandler, final TranslationSettings settings,
			final ProcedureManager procedureManager, final MemoryHandler memoryHandler,
			final InitializationHandler initHandler, final FunctionHandler functionhandler, final CHandler chandler) {
		mLogger = logger;
		mExpressionTranslation = expressionTranslation;
		mReporter = reporter;
		mTypeHandler = typeHandler;
		mAuxVarInfoBuilder = auxVarInfoBuilder;
		mFunctionToIndex = functionToIndex;
		mTypeSize = typeSizes;
		mSymboltable = symbolTable;
		mStaticObjectsHandler = staticObjectsHandler;
		mSettings = settings;
		mProcedureManager = procedureManager;
		mMemoryHandler = memoryHandler;
		mInitHandler = initHandler;
		mFunctionhandler = functionhandler;
		mCHandler = chandler;
	}

	/**
	 * Start method for the post processing.
	 *
	 * @return a declaration list holding the init() and start() procedure.
	 */
	public ArrayList<Declaration> postProcess(final ILocation loc, final IASTNode hook) {
		final ArrayList<Declaration> decl = new ArrayList<>();

		final Set<String> undefinedTypes = mTypeHandler.getUndefinedTypes();
		decl.addAll(declareUndefinedTypes(loc, undefinedTypes));

		final String checkedMethod = mSettings.getCheckedMethod();

		if (!checkedMethod.equals(SFO.EMPTY) && mProcedureManager.hasProcedure(checkedMethod)) {
			mLogger.info("Settings: Checked method=" + checkedMethod);

			final UltimateInitProcedure initProcedure = createUltimateInitProcedure(loc, hook);
			decl.add(initProcedure.getUltimateInitImplementation());

			final UltimateStartProcedure startProcedure = createUltimateStartProcedure(loc, hook);
			decl.add(startProcedure.getUltimateStartImplementation());

		} else {
			// this would be done during createInit otherwise
			mStaticObjectsHandler.freeze();

			mLogger.info("Settings: Library mode!");
			if (mProcedureManager.hasProcedure(SFO.MAIN)) {
				final String msg =
						"You selected the library mode (i.e., each procedure can be starting procedure and global "
								+ "variables are not initialized). This program contains a \"main\" procedure. Maybe you "
								+ "wanted to select the \"main\" procedure as starting procedure.";
				mReporter.warn(loc, msg);
			}
		}

		decl.addAll(declareFunctionPointerProcedures());

		decl.addAll(declareConversionFunctions());

		if (mSettings.isBitvectorTranslation()) {
			decl.addAll(declarePrimitiveDataTypeSynonyms(loc));

			if ((mTypeHandler).areFloatingTypesNeeded()) {
				decl.addAll(declareFloatDataTypes(loc));
			}

			final String[] importantFunctions = new String[] { "bvadd" };
			mExpressionTranslation.declareBinaryBitvectorFunctionsForAllIntegerDatatypes(loc, importantFunctions);
		}
		assert decl.stream().allMatch(Objects::nonNull);
		return decl;
	}

	private ArrayList<Declaration> declareConversionFunctions() {
		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();

		final ArrayList<Declaration> decls = new ArrayList<>();

		final String outInt = "outInt";
		final VarList realParam =
				new VarList(ignoreLoc, new String[] {}, new PrimitiveType(ignoreLoc, BoogieType.TYPE_REAL, SFO.REAL));
		final VarList[] oneRealParam = new VarList[] { realParam };
		final VarList intParam = new VarList(ignoreLoc, new String[] { outInt },
				new PrimitiveType(ignoreLoc, BoogieType.TYPE_INT, SFO.INT));

		if (mDeclareToIntFunction) {
			decls.add(new FunctionDeclaration(ignoreLoc, new Attribute[0], SFO.TO_INT, new String[0], oneRealParam,
					intParam));
		}

		return decls;
	}

	private ArrayList<Declaration> declareFunctionPointerProcedures() {
		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		final ArrayList<Declaration> result = new ArrayList<>();
		for (final ProcedureSignature cFunc : mFunctionhandler.getFunctionsSignaturesWithFunctionPointers()) {
			final String procName = cFunc.toString();

			final VarList[] inParams = mProcedureManager.getProcedureDeclaration(procName).getInParams();
			final VarList[] outParams = mProcedureManager.getProcedureDeclaration(procName).getOutParams();
			assert outParams.length <= 1;

			final Body body = getFunctionPointerFunctionBody(ignoreLoc, procName, cFunc, inParams, outParams);
			final Procedure functionPointerMuxProc = new Procedure(ignoreLoc, new Attribute[0], procName, new String[0],
					inParams, outParams, null, body);
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

	/**
	 * Generate type declarations like, e.g., the following. type { :isUnsigned true } { :bitsize 16 } C_USHORT = bv16;
	 * This allow us to use type synonyms like C_USHORT during the translation. This is yet not consequently
	 * implemented. This is desired not only for bitvectors: it makes our translation more modular and can ease
	 * debugging. However, that this located in this class and fixed to bitvectors is a workaround.
	 *
	 */
	public ArrayList<Declaration> declarePrimitiveDataTypeSynonyms(final ILocation loc) {
		final ArrayList<Declaration> decls = new ArrayList<>();
		for (final CPrimitive.CPrimitives cPrimitive : CPrimitive.CPrimitives.values()) {
			final CPrimitive cPrimitiveO = new CPrimitive(cPrimitive);
			if (cPrimitiveO.getGeneralType() == CPrimitiveCategory.INTTYPE) {
				final Attribute[] attributes = new Attribute[2];
				attributes[0] = new NamedAttribute(loc, "isUnsigned", new Expression[] {
						ExpressionFactory.createBooleanLiteral(loc, mTypeSize.isUnsigned(cPrimitiveO)) });
				final int bytesize = mTypeSize.getSize(cPrimitive);
				final int bitsize = bytesize * 8;
				attributes[1] = new NamedAttribute(loc, "bitsize",
						new Expression[] { ExpressionFactory.createIntegerLiteral(loc, String.valueOf(bitsize)) });
				final String identifier = "C_" + cPrimitive.name();
				final String[] typeParams = new String[0];
				final ASTType astType = mTypeHandler.bytesize2asttype(loc, CPrimitiveCategory.INTTYPE, bytesize);
				decls.add(new TypeDeclaration(loc, attributes, false, identifier, typeParams, astType));
			}
		}
		return decls;
	}

	/**
	 * Generate FloatingPoint types
	 *
	 */
	public ArrayList<Declaration> declareFloatDataTypes(final ILocation loc) {
		final ArrayList<Declaration> decls = new ArrayList<>();

		// Roundingmodes, for now RNE hardcoded
		final Attribute[] attributesRM;
		if (mSettings.overapproximateFloatingPointOperations()) {
			attributesRM = new Attribute[0];
		} else {
			final String smtlibRmIdentifier = "RoundingMode";
			attributesRM = new Attribute[1];
			attributesRM[0] = new NamedAttribute(loc, FunctionDeclarations.BUILTIN_IDENTIFIER,
					new Expression[] { ExpressionFactory.createStringLiteral(loc, smtlibRmIdentifier) });
		}
		final String[] typeParamsRM = new String[0];
		decls.add(new TypeDeclaration(loc, attributesRM, false, BitvectorTranslation.BOOGIE_ROUNDING_MODE_IDENTIFIER,
				typeParamsRM));

		final Attribute[] attributesRNE;
		final Attribute[] attributesRTZ;
		if (mSettings.overapproximateFloatingPointOperations()) {
			attributesRNE = new Attribute[0];
			attributesRTZ = new Attribute[0];
		} else {
			final Attribute attributeRNE = new NamedAttribute(loc, FunctionDeclarations.BUILTIN_IDENTIFIER,
					new Expression[] { ExpressionFactory.createStringLiteral(loc, "RNE") });
			final Attribute attributeRTZ = new NamedAttribute(loc, FunctionDeclarations.BUILTIN_IDENTIFIER,
					new Expression[] { ExpressionFactory.createStringLiteral(loc, "RTZ") });
			attributesRNE = new Attribute[] { attributeRNE };
			attributesRTZ = new Attribute[] { attributeRTZ };
		}
		decls.add(
				new ConstDeclaration(loc, attributesRNE, false,
						new VarList(loc, new String[] { BitvectorTranslation.BOOGIE_ROUNDING_MODE_RNE },
								new NamedType(loc, BitvectorTranslation.TYPE_OF_BOOGIE_ROUNDING_MODES,
										BitvectorTranslation.BOOGIE_ROUNDING_MODE_IDENTIFIER, new ASTType[0])),
						null, false));
		decls.add(
				new ConstDeclaration(loc, attributesRTZ, false,
						new VarList(loc, new String[] { BitvectorTranslation.BOOGIE_ROUNDING_MODE_RTZ },
								new NamedType(loc, BitvectorTranslation.TYPE_OF_BOOGIE_ROUNDING_MODES,
										BitvectorTranslation.BOOGIE_ROUNDING_MODE_IDENTIFIER, new ASTType[0])),
						null, false));

		for (final CPrimitive.CPrimitives cPrimitive : CPrimitive.CPrimitives.values()) {

			final CPrimitive cPrimitive0 = new CPrimitive(cPrimitive);

			if (cPrimitive0.getGeneralType() == CPrimitiveCategory.FLOATTYPE && !cPrimitive0.isComplexType()) {

				if (!mSettings.overapproximateFloatingPointOperations()) {
					// declare floating point constructors here because we might
					// always need them for our backtranslation
					(mExpressionTranslation).declareFloatingPointConstructors(loc, new CPrimitive(cPrimitive));
					mExpressionTranslation.declareFloatConstant(loc, BitvectorTranslation.SMT_LIB_MINUS_INF,
							new CPrimitive(cPrimitive));
					(mExpressionTranslation).declareFloatConstant(loc, BitvectorTranslation.SMT_LIB_PLUS_INF,
							new CPrimitive(cPrimitive));
					(mExpressionTranslation).declareFloatConstant(loc, BitvectorTranslation.SMT_LIB_NAN,
							new CPrimitive(cPrimitive));
					(mExpressionTranslation).declareFloatConstant(loc, BitvectorTranslation.SMT_LIB_MINUS_ZERO,
							new CPrimitive(cPrimitive));
					(mExpressionTranslation).declareFloatConstant(loc, BitvectorTranslation.SMT_LIB_PLUS_ZERO,
							new CPrimitive(cPrimitive));
				}

				final Attribute[] attributes;
				if (mSettings.overapproximateFloatingPointOperations()) {
					attributes = new Attribute[0];
				} else {
					attributes = new Attribute[2];
					attributes[0] = new NamedAttribute(loc, FunctionDeclarations.BUILTIN_IDENTIFIER,
							new Expression[] { ExpressionFactory.createStringLiteral(loc, "FloatingPoint") });
					final int bytesize = mTypeSize.getSize(cPrimitive);
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
							new Expression[] { ExpressionFactory.createIntegerLiteral(loc, String.valueOf(indices[0])),
									ExpressionFactory.createIntegerLiteral(loc, String.valueOf(indices[1])) });
				}
				final String identifier = "C_" + cPrimitive.name();
				final String[] typeParams = new String[0];
				decls.add(new TypeDeclaration(loc, attributes, false, identifier, typeParams));
			}
		}
		return decls;
	}

	/**
	 * Generate the body for one of our internal function pointer dispatching procedures. See also
	 * {@link FunctionHandler.handleFunctionPointerCall} on how we treat function pointers.
	 *
	 *
	 * @param loc
	 * @param main
	 * @param procedureManager
	 * @param memoryHandler
	 * @param structHandler
	 * @param dispatchingProcedureName
	 *            name of the dispatching procedure
	 * @param funcSignature
	 *            signature of the dispatching procedure
	 * @param inParams
	 *            in parameters of the dispatching procedure as it has been registered in FunctionHandler
	 * @param outParam
	 *            out parameters of the dispatching procedure as it has been registered in FunctionHandler
	 * @return
	 */
	private Body getFunctionPointerFunctionBody(final ILocation loc, final String dispatchingProcedureName,
			final ProcedureSignature funcSignature, final VarList[] inParams, final VarList[] outParam) {

		mProcedureManager.beginProcedureScope(mCHandler, mProcedureManager.getProcedureInfo(dispatchingProcedureName));

		final boolean resultTypeIsVoid = (funcSignature.getReturnType() == null);

		final ExpressionResultBuilder builder = new ExpressionResultBuilder();

		/*
		 * Setup the input parameters for the dispatched procedures. The last inParam of the dispatching procedure is
		 * the function pointer in this case, which is not given to the dispatched procedures. --> therefore we iterate
		 * to inParams.lenth - 1 only..
		 */
		final ArrayList<Expression> args = new ArrayList<>();
		for (int i = 0; i < inParams.length - 1; i++) {
			final VarList vl = inParams[i];
			assert vl.getIdentifiers().length == 1;
			final String oldId = vl.getIdentifiers()[0];
			final String newId = oldId.replaceFirst("in", "");
			builder.addDeclaration(new VariableDeclaration(loc, new Attribute[0],
					new VarList[] { new VarList(loc, new String[] { newId }, vl.getType()) }));
			final IdentifierExpression oldIdExpr = ExpressionFactory.constructIdentifierExpression(loc,
					mTypeHandler.getBoogieTypeForBoogieASTType(vl.getType()), oldId,
					new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, dispatchingProcedureName));
			final VariableLHS newIdLhs = ExpressionFactory.constructVariableLHS(loc,
					mTypeHandler.getBoogieTypeForBoogieASTType(vl.getType()), newId,
					new DeclarationInformation(StorageClass.LOCAL, dispatchingProcedureName));
			builder.addStatement(StatementFactory.constructAssignmentStatement(loc, new LeftHandSide[] { newIdLhs },
					new Expression[] { oldIdExpr }));
			final IdentifierExpression newIdIdExpr = ExpressionFactory.constructIdentifierExpression(loc,
					mTypeHandler.getBoogieTypeForBoogieASTType(vl.getType()), newId,
					new DeclarationInformation(StorageClass.LOCAL, dispatchingProcedureName));
			args.add(newIdIdExpr);
		}

		// collect all functions that are addressoffed in the program and that match the signature
		final ArrayList<String> fittingFunctions = new ArrayList<>();
		for (final Entry<String, Integer> en : mFunctionToIndex.entrySet()) {
			final CFunction ptdToFuncType = mProcedureManager.getCFunctionType(en.getKey());
			if (new ProcedureSignature(mTypeHandler, ptdToFuncType).equals(funcSignature)) {
				fittingFunctions.add(en.getKey());
			}
		}

		// generate the actual body
		IdentifierExpression funcCallResult = null;
		if (fittingFunctions.isEmpty()) {
			return mProcedureManager.constructBody(loc,
					builder.getDeclarations().toArray(new VariableDeclaration[builder.getDeclarations().size()]),
					builder.getStatements().toArray(new Statement[builder.getStatements().size()]),
					dispatchingProcedureName);
		} else if (fittingFunctions.size() == 1) {
			final ExpressionResult rex = (ExpressionResult) mFunctionhandler.makeTheFunctionCallItself(loc,
					fittingFunctions.get(0), new ExpressionResultBuilder(), args);

			final boolean voidReturnType = outParam.length == 0;

			if (!voidReturnType) {
				funcCallResult = (IdentifierExpression) rex.getLrValue().getValue();
			}
			builder.addAllExceptLrValue(rex);

			assert outParam.length <= 1;
			if (outParam.length == 1) {
				final String id = outParam[0].getIdentifiers()[0];
				final ASTType astType = outParam[0].getType();
				final VariableLHS lhs = // new VariableLHS(loc, outParam[0].getIdentifiers()[0]);
						ExpressionFactory.constructVariableLHS(loc, mTypeHandler.getBoogieTypeForBoogieASTType(astType),
								id, new DeclarationInformation(StorageClass.IMPLEMENTATION_OUTPARAM,
										dispatchingProcedureName));
				if (!voidReturnType) {
					builder.addStatement(StatementFactory.constructAssignmentStatement(loc, new LeftHandSide[] { lhs },
							new Expression[] { funcCallResult }));
				}
			}
			builder.addStatements(CTranslationUtil.createHavocsForAuxVars(rex.getAuxVars()));
			builder.addStatement(new ReturnStatement(loc));

			final Body result = mProcedureManager.constructBody(loc,
					builder.getDeclarations().toArray(new VariableDeclaration[builder.getDeclarations().size()]),
					builder.getStatements().toArray(new Statement[builder.getStatements().size()]),
					dispatchingProcedureName);
			mProcedureManager.endProcedureScope(mCHandler);
			return result;
		} else {
			AuxVarInfo auxvar = null;
			if (!resultTypeIsVoid) {
				auxvar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, funcSignature.getReturnType(),
						SFO.AUXVAR.FUNCPTRRES);
				builder.addDeclaration(auxvar.getVarDec());
				builder.addAuxVar(auxvar);
				funcCallResult = auxvar.getExp();
			}

			final ExpressionResult firstElseRex = (ExpressionResult) mFunctionhandler.makeTheFunctionCallItself(loc,
					fittingFunctions.get(0), new ExpressionResultBuilder(), args);
			for (final Declaration dec : firstElseRex.getDeclarations()) {
				builder.addDeclaration(dec);
			}
			builder.addAuxVars(firstElseRex.getAuxVars());

			final ArrayList<Statement> firstElseStmt = new ArrayList<>();
			firstElseStmt.addAll(firstElseRex.getStatements());
			if (!resultTypeIsVoid) {
				final AssignmentStatement assignment =
						StatementFactory.constructAssignmentStatement(loc, new VariableLHS[] { auxvar.getLhs() },
								new Expression[] { firstElseRex.getLrValue().getValue() });
				firstElseStmt.add(assignment);
			}
			IfStatement currentIfStmt = null;

			for (int i = 1; i < fittingFunctions.size(); i++) {
				final ExpressionResult currentRex = (ExpressionResult) mFunctionhandler.makeTheFunctionCallItself(loc,
						fittingFunctions.get(i), new ExpressionResultBuilder(), args);
				for (final Declaration dec : currentRex.getDeclarations()) {
					builder.addDeclaration(dec);
				}
				builder.addAuxVars(currentRex.getAuxVars());

				final ArrayList<Statement> newStmts = new ArrayList<>();
				newStmts.addAll(currentRex.getStatements());
				if (!resultTypeIsVoid) {
					final AssignmentStatement assignment =
							StatementFactory.constructAssignmentStatement(loc, new VariableLHS[] { auxvar.getLhs() },
									new Expression[] { currentRex.getLrValue().getValue() });
					newStmts.add(assignment);
				}

				final IdentifierExpression functionPointerIdex = mTypeHandler.constructIdentifierExpression(loc,
						inParams[inParams.length - 1].getType(), inParams[inParams.length - 1].getIdentifiers()[0],
						StorageClass.IMPLEMENTATION_INPARAM, dispatchingProcedureName);
				final IdentifierExpression functionPointerValueOfCurrentFittingFunctionIdex =
						mTypeHandler.constructIdentifierExpression(loc, mTypeHandler.getBoogiePointerType(),
								SFO.FUNCTION_ADDRESS + fittingFunctions.get(i), StorageClass.GLOBAL, null);
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

			builder.addStatement(currentIfStmt);
			if (outParam.length == 1) {
				final VariableLHS dispatchingFunctionResultLhs = ExpressionFactory.constructVariableLHS(loc,
						mTypeHandler.getBoogieTypeForBoogieASTType(outParam[0].getType()),
						outParam[0].getIdentifiers()[0],
						new DeclarationInformation(StorageClass.IMPLEMENTATION_OUTPARAM, dispatchingProcedureName));
				builder.addStatement(StatementFactory.constructAssignmentStatement(loc,
						new LeftHandSide[] { dispatchingFunctionResultLhs }, new Expression[] { funcCallResult }));
			}
			builder.addStatements(CTranslationUtil.createHavocsForAuxVars(builder.getAuxVars()));
			builder.addStatement(new ReturnStatement(loc));
			final Body result = mProcedureManager.constructBody(loc,
					builder.getDeclarations().toArray(new VariableDeclaration[builder.getDeclarations().size()]),
					builder.getStatements().toArray(new Statement[builder.getStatements().size()]),
					dispatchingProcedureName);
			mProcedureManager.endProcedureScope(mCHandler);
			return result;
		}
	}

	private UltimateInitProcedure createUltimateInitProcedure(final ILocation translationUnitLoc, final IASTNode hook) {

		{
			final Procedure initProcedureDecl = new Procedure(translationUnitLoc, new Attribute[0], SFO.INIT,
					new String[0], new VarList[0], new VarList[0], new Specification[0], null);
			mProcedureManager.beginCustomProcedure(mCHandler, translationUnitLoc, SFO.INIT, initProcedureDecl);
		}
		final ArrayList<Statement> initStatements = new ArrayList<>();
		final Collection<String> proceduresCalledByUltimateInit = new HashSet<>();

		final ArrayList<VariableDeclaration> initDecl = new ArrayList<>();

		if (mMemoryHandler.getRequiredMemoryModelFeatures().isMemoryModelInfrastructureRequired()) {

			// set #valid[0] = 0 (i.e., the memory at the NULL-pointer is not allocated)
			final Expression zero = mTypeSize.constructLiteralForIntegerType(translationUnitLoc,
					mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO);
			final Expression literalThatRepresentsFalse = mMemoryHandler.getBooleanArrayHelper().constructFalse();
			final AssignmentStatement assignment = MemoryHandler.constructOneDimensionalArrayUpdate(translationUnitLoc,
					zero, mMemoryHandler.getValidArrayLhs(translationUnitLoc), literalThatRepresentsFalse);
			initStatements.add(0, assignment);

			// set the value of the NULL-constant to NULL = { base : 0, offset : 0 }
			final VariableLHS slhs = ExpressionFactory.constructVariableLHS(translationUnitLoc,
					mTypeHandler.getBoogiePointerType(), SFO.NULL,
					DeclarationInformation.DECLARATIONINFO_GLOBAL);
			initStatements.add(0,
					StatementFactory.constructAssignmentStatement(translationUnitLoc, new LeftHandSide[] { slhs },
							new Expression[] { ExpressionFactory.constructStructConstructor(translationUnitLoc,
									new String[] { "base", "offset" },
									new Expression[] { mTypeSize.constructLiteralForIntegerType(translationUnitLoc,
											mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO),
											mTypeSize.constructLiteralForIntegerType(translationUnitLoc,
													mExpressionTranslation.getCTypeOfPointerComponents(),
													BigInteger.ZERO) }) }));
		}

		/*
		 * We need to follow some order when addin the statements to init. Current strategy: <li> First come all the
		 * statements that have been added via {@link StaticObjectsHandler.addStatementsForUltimateInit} manually. <li>
		 * After that we add the statements for the initialization of objects with static storage duration. <li> Each of
		 * those lists is added in the order that we added those to the {@link StaticObjectsHandler}. It is unclear how
		 * generally feasible this strategy is, we know however that exchanging bullets 1 and 2 breaks
		 * regression/ctrans-bug-min-TE-static-const-uint8_t.c )
		 */
		final List<Statement> staticObjectInitStatements = new ArrayList<>();

		// initialization for statics and other globals
		for (final Entry<VariableDeclaration, CDeclaration> en : mStaticObjectsHandler
				.getGlobalVariableDeclsWithAssociatedCDecls().entrySet()) {
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

					final VariableLHS lhs = ExpressionFactory.constructVariableLHS(currentDeclsLoc,
							mTypeHandler.getBoogieTypeForBoogieASTType(vl.getType()), id,
							DeclarationInformation.DECLARATIONINFO_GLOBAL);

					if (mCHandler.isHeapVar(id)) {
						final LocalLValue llVal = new LocalLValue(lhs, en.getValue().getType(), null);
						staticObjectInitStatements.add(mMemoryHandler.getMallocCall(llVal, currentDeclsLoc, hook));
						proceduresCalledByUltimateInit.add(MemoryModelDeclarations.Ultimate_Alloc.name());
					}

					final ExpressionResult initRex =
							mInitHandler.initialize(currentDeclsLoc, lhs, en.getValue().getType(), initializer, hook);
					for (final Statement stmt : initRex.getStatements()) {
						if (stmt instanceof CallStatement) {
							proceduresCalledByUltimateInit.add(((CallStatement) stmt).getMethodName());
						}
						staticObjectInitStatements.add(stmt);
					}
					staticObjectInitStatements.addAll(CTranslationUtil.createHavocsForAuxVars(initRex.getAuxVars()));
					for (final Declaration d : initRex.getDeclarations()) {
						initDecl.add((VariableDeclaration) d);
					}
				}
			}
		}

		mStaticObjectsHandler.freeze();
		initStatements.addAll(mStaticObjectsHandler.getStatementsForUltimateInit());
		initStatements.addAll(staticObjectInitStatements);

		/*
		 * note that we only have to deal with the implementation part of the procedure, the declaration is managed by
		 * the FunctionHandler
		 */
		final Body initBody = mProcedureManager.constructBody(translationUnitLoc,
				initDecl.toArray(new VariableDeclaration[initDecl.size()]),
				initStatements.toArray(new Statement[initStatements.size()]), SFO.INIT);
		final Procedure initProcedureImplementation = new Procedure(translationUnitLoc, new Attribute[0], SFO.INIT,
				new String[0], new VarList[0], new VarList[0], null, initBody);

		mProcedureManager.endCustomProcedure(mCHandler, SFO.INIT);

		return new UltimateInitProcedure(initProcedureImplementation);
	}

	private UltimateStartProcedure createUltimateStartProcedure(final ILocation loc, final IASTNode hook) {

		Procedure startProcedure = null;
		{
			final Procedure startDeclaration = new Procedure(loc, new Attribute[0], SFO.START, new String[0],
					new VarList[0], new VarList[0], new Specification[0], null);
			mProcedureManager.beginCustomProcedure(mCHandler, loc, SFO.START, startDeclaration);
		}

		final ArrayList<Statement> startStmt = new ArrayList<>();
		final ArrayList<VariableDeclaration> startDecl = new ArrayList<>();
		startStmt.add(
				StatementFactory.constructCallStatement(loc, false, new VariableLHS[0], SFO.INIT, new Expression[0]));
		final String checkedMethod = mSettings.getCheckedMethod();
		final VarList[] checkedMethodOutParams =
				mProcedureManager.getProcedureDeclaration(checkedMethod).getOutParams();
		final VarList[] checkedMethodInParams = mProcedureManager.getProcedureDeclaration(checkedMethod).getInParams();
		final Specification[] checkedMethodSpec =
				mProcedureManager.getProcedureDeclaration(checkedMethod).getSpecification();

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
				assert arg.getIdentifiers().length == 1;
				final String id = arg.getIdentifiers()[0];
				final IdentifierExpression idEx = mTypeHandler.constructIdentifierExpression(loc, arg.getType(), id,
						StorageClass.LOCAL, SFO.START);
				args.add(idEx);
			}
		}
		if (checkedMethodOutParams.length != 0) {
			assert checkedMethodOutParams.length == 1;
			// there is 1(!) return value
			final CType checkedMethodResultCType = mProcedureManager.getCFunctionType(checkedMethod).getResultType();
			final AuxVarInfo checkedMethodReturnAuxVar =
					mAuxVarInfoBuilder.constructAuxVarInfo(loc, checkedMethodResultCType, SFO.AUXVAR.RETURNED);
			mSymboltable.addBoogieCIdPair(checkedMethodReturnAuxVar.getExp().getIdentifier(),
					SFO.NO_REAL_C_VAR + checkedMethodReturnAuxVar.getExp().getIdentifier(), loc);
			startDecl.add(checkedMethodReturnAuxVar.getVarDec());
			startStmt.add(StatementFactory.constructCallStatement(loc, false,
					new VariableLHS[] { checkedMethodReturnAuxVar.getLhs() }, checkedMethod,
					args.toArray(new Expression[args.size()])));
		} else {
			startStmt.add(StatementFactory.constructCallStatement(loc, false, new VariableLHS[0], checkedMethod,
					args.toArray(new Expression[args.size()])));
		}

		final Body startBody =
				mProcedureManager.constructBody(loc, startDecl.toArray(new VariableDeclaration[startDecl.size()]),
						startStmt.toArray(new Statement[startStmt.size()]), SFO.START);
		startProcedure = new Procedure(loc, new Attribute[0], SFO.START, new String[0], new VarList[0], new VarList[0],
				null, startBody);

		/*
		 * note that we only deal with the implementation of the procedure here, the declaration is managed by the
		 * FucntionHandler
		 */
		mProcedureManager.endCustomProcedure(mCHandler, SFO.START);
		return new UltimateStartProcedure(startProcedure);
	}

	private static final class UltimateInitProcedure {

		private final Declaration mUltimateInitImplementation;

		private UltimateInitProcedure(final Declaration decl) {
			mUltimateInitImplementation = decl;
		}

		public Declaration getUltimateInitImplementation() {
			assert mUltimateInitImplementation != null;
			return mUltimateInitImplementation;
		}

	}

	private static final class UltimateStartProcedure {

		private final Procedure mStartProcedure;

		private UltimateStartProcedure(final Procedure startProcedure) {
			mStartProcedure = startProcedure;
		}

		public Declaration getUltimateStartImplementation() {
			assert mStartProcedure != null;
			return mStartProcedure;
		}
	}
}
