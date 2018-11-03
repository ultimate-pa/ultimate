/*
 * Copyright (C) 2013-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Stefan Wissert
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
/**
 * The base C handler implementation.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.text.ParseException;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import org.eclipse.cdt.core.dom.ast.IASTASMDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTArrayDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTArrayModifier;
import org.eclipse.cdt.core.dom.ast.IASTArraySubscriptExpression;
import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTBreakStatement;
import org.eclipse.cdt.core.dom.ast.IASTCaseStatement;
import org.eclipse.cdt.core.dom.ast.IASTCastExpression;
import org.eclipse.cdt.core.dom.ast.IASTCompoundStatement;
import org.eclipse.cdt.core.dom.ast.IASTConditionalExpression;
import org.eclipse.cdt.core.dom.ast.IASTContinueStatement;
import org.eclipse.cdt.core.dom.ast.IASTDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTDeclarationStatement;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTDefaultStatement;
import org.eclipse.cdt.core.dom.ast.IASTDoStatement;
import org.eclipse.cdt.core.dom.ast.IASTElaboratedTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTEqualsInitializer;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTExpressionList;
import org.eclipse.cdt.core.dom.ast.IASTExpressionStatement;
import org.eclipse.cdt.core.dom.ast.IASTFieldDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTFieldReference;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTGotoStatement;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTIfStatement;
import org.eclipse.cdt.core.dom.ast.IASTInitializer;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTInitializerList;
import org.eclipse.cdt.core.dom.ast.IASTLabelStatement;
import org.eclipse.cdt.core.dom.ast.IASTLiteralExpression;
import org.eclipse.cdt.core.dom.ast.IASTName;
import org.eclipse.cdt.core.dom.ast.IASTNamedTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTNullStatement;
import org.eclipse.cdt.core.dom.ast.IASTParameterDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTPointer;
import org.eclipse.cdt.core.dom.ast.IASTPointerOperator;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorStatement;
import org.eclipse.cdt.core.dom.ast.IASTProblem;
import org.eclipse.cdt.core.dom.ast.IASTProblemDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTProblemExpression;
import org.eclipse.cdt.core.dom.ast.IASTProblemStatement;
import org.eclipse.cdt.core.dom.ast.IASTProblemTypeId;
import org.eclipse.cdt.core.dom.ast.IASTReturnStatement;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTStandardFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTStatement;
import org.eclipse.cdt.core.dom.ast.IASTSwitchStatement;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.dom.ast.IASTTypeIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTWhileStatement;
import org.eclipse.cdt.core.dom.ast.IArrayType;
import org.eclipse.cdt.core.dom.ast.IBinding;
import org.eclipse.cdt.core.dom.ast.IFunction;
import org.eclipse.cdt.core.dom.ast.IFunctionType;
import org.eclipse.cdt.core.dom.ast.IPointerType;
import org.eclipse.cdt.core.dom.ast.IProblemBinding;
import org.eclipse.cdt.core.dom.ast.IType;
import org.eclipse.cdt.core.dom.ast.ITypedef;
import org.eclipse.cdt.core.dom.ast.IVariable;
import org.eclipse.cdt.core.dom.ast.c.ICASTCompositeTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.gnu.IGNUASTCompoundStatementExpression;
import org.eclipse.cdt.core.dom.ast.gnu.c.ICASTKnRFunctionDeclarator;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTDesignatedInitializer;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTFunctionDeclarator;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTLiteralExpression;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieIdExtractor;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.annotation.LTLPropertyCheck;
import de.uni_freiburg.informatik.ultimate.boogie.annotation.LTLPropertyCheck.CheckableExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BreakStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.decorator.DecoratedUnit;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.ArrayHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.CCharacterConstant;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.CStringLiteral;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.FunctionHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.InitializationHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.LocalLValueILocationPair;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.PostProcessor;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.ProcedureManager;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.StaticObjectsHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.StructHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizeAndOffsetComputer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.SymbolTableValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitiveCategory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStructOrUnion;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CHandlerTranslationResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CStorageClass;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ContractResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.DeclarationResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.DeclaratorResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionListResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultTransformer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.InitializerResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.InitializerResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValueFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValueForArrays;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.SkipResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.StringLiteralResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.TypesResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.INameHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check.Spec;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.CodeAnnot;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Contract;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.GlobalLTLInvariant;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.ICACSL2BoogieBacktranslatorMapping;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.LTLExpressionExtractor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.PointerCheckMode;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Class that handles translation of C nodes to Boogie nodes.
 *
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @author Matthias Heizmann
 * @author Alexander Nutz
 */
public class CHandler {

	/**
	 * If set to true we say Unsupported Syntax if there is some cast of pointers. Right now we are unable to handle
	 * casts of pointers soundly. However these soundness errors occur seldom.
	 */
	private static final boolean POINTER_CAST_IS_UNSUPPORTED_SYNTAX = false;

	private final MemoryHandler mMemoryHandler;

	private final ArrayHandler mArrayHandler;

	private final StaticObjectsHandler mStaticObjectsHandler;

	private final FunctionHandler mFunctionHandler;

	private final PostProcessor mPostProcessor;

	private final INameHandler mNameHandler;

	private final InitializationHandler mInitHandler;
	private final LinkedHashSet<String> mBoogieIdsOfHeapVars;

	/**
	 * Stores the labels of the loops we are currently inside. (For translation of a possible continue statement)
	 */
	private final Deque<String> mInnerMostLoopLabel;

	private final ILogger mLogger;

	private final List<LTLExpressionExtractor> mGlobAcslExtractors;
	private final StandardFunctionHandler mStandardFunctionHandler;

	private final ITypeHandler mTypeHandler;

	private final StructHandler mStructHandler;

	/**
	 * Contract for next procedure
	 */
	private final List<ACSLNode> mContract;

	/**
	 * The symbol table for the translation.
	 */
	private final FlatSymbolTable mSymbolTable;

	/**
	 * Translation from Boogie to C for traces and expressions.
	 */
	private final ICACSL2BoogieBacktranslatorMapping mBacktranslator;

	private final ExpressionTranslation mExpressionTranslation;

	private final TypeSizeAndOffsetComputer mTypeSizeComputer;

	/**
	 * Holds the next ACSL node in the decorator tree.
	 */
	private NextACSL mAcsl;

	/**
	 * This is a stack containing the types of the things declared IASTDeclarator nodes. The last element on the stack
	 * corresponds to the type of the current (inner) declarator node. There may be several types on this stack if the
	 * declarators are nested, as in
	 *
	 * <pre>
	 * int *(*a(int))[3]
	 * </pre>
	 *
	 * which declares a function returning a pointer to an array of length three containing int pointers. There are
	 * three nested declarators: A PointerDeclarator contains an ArrayDeclarator contains a Pointer contains a function.
	 */
	private final ArrayDeque<TypesResult> mCurrentDeclaredTypes;

	private final ProcedureManager mProcedureManager;

	/**
	 * The boogie declarations that are the result of the translation process.
	 */
	private final ArrayList<Declaration> mDeclarations;

	private final CTranslationResultReporter mReporter;

	private final TypeSizes mTypeSizes;

	private final LocationFactory mLocationFactory;

	private final AuxVarInfoBuilder mAuxVarInfoBuilder;

	private final TranslationSettings mSettings;

	private final ExpressionResultTransformer mExprResultTransformer;

	private final Map<String, Integer> mFunctionToIndex;

	private final Set<IASTNode> mVariablesOnHeap;

	private final Set<IASTDeclaration> mReachableDeclarations;

	/**
	 * Our translation is done in two passes. In the first pass (the prerun pass) we construct only a mock Boogie AST
	 * but determine e.g., which values we store in local variables of the Boogie program and which variables we store
	 * in the "memory array" of the Boogie program. Only the main pass we construct the AST of the Boogie program that
	 * is the result of this plugin.
	 */
	private final boolean mIsPrerun;

	private Map<String, IASTNode> mFunctionTable;

	/**
	 * Constructor for CHandler in pre-run mode.
	 *
	 * @param staticObjectsHandler
	 * @param functionToIndex
	 * @param set
	 *
	 */
	public CHandler(final IUltimateServiceProvider services, final ILogger logger,
			final ICACSL2BoogieBacktranslatorMapping backtranslator, final TranslationSettings settings,
			final FlatSymbolTable symbolTable, final Map<String, IASTNode> functionTable,
			final ExpressionTranslation exprTrans, final LocationFactory locationFactory, final TypeSizes typeSizes,
			final Set<IASTDeclaration> reachableDeclarations, final ITypeHandler typeHandler,
			final CTranslationResultReporter reporter, final INameHandler nameHandler,
			final StaticObjectsHandler staticObjectsHandler, final Map<String, Integer> functionToIndex,
			final Set<IASTNode> variablesOnHeap) {
		mExpressionTranslation = exprTrans;
		mIsPrerun = true;

		mLogger = logger;
		mBacktranslator = backtranslator;
		mLocationFactory = locationFactory;
		mSymbolTable = symbolTable;
		mTypeSizes = typeSizes;
		mSettings = settings;
		mReachableDeclarations = reachableDeclarations;
		mTypeHandler = typeHandler;
		mReporter = reporter;
		mNameHandler = nameHandler;
		mStaticObjectsHandler = staticObjectsHandler;
		mFunctionTable = functionTable;

		mFunctionToIndex = new LinkedHashMap<>(functionToIndex);
		mVariablesOnHeap = new LinkedHashSet<>(variablesOnHeap);

		mContract = new ArrayList<>();
		mInnerMostLoopLabel = new ArrayDeque<>();
		mBoogieIdsOfHeapVars = new LinkedHashSet<>();
		mCurrentDeclaredTypes = new ArrayDeque<>();
		mGlobAcslExtractors = new ArrayList<>();
		mDeclarations = new ArrayList<>();

		mTypeSizeComputer = new TypeSizeAndOffsetComputer(mTypeSizes, mExpressionTranslation, mTypeHandler);

		// the procedure manager has to be replaced between pre-run and main run
		// the following fields form the transitive dependency hull on the procedure manager
		mProcedureManager = new ProcedureManager(mLogger, settings);

		mAuxVarInfoBuilder = new AuxVarInfoBuilder(mNameHandler, mTypeHandler, mProcedureManager);
		mMemoryHandler = new MemoryHandler(mTypeSizes, mNameHandler, settings.useSmtBoolArrayWorkaround(), mTypeHandler,
				mExpressionTranslation, mProcedureManager, mTypeSizeComputer, mAuxVarInfoBuilder, mSettings);

		mStructHandler = new StructHandler(mMemoryHandler, mTypeSizeComputer, mExpressionTranslation, mTypeHandler,
				mLocationFactory);
		mExprResultTransformer = new ExpressionResultTransformer(this, mMemoryHandler, mStructHandler,
				mExpressionTranslation, mTypeSizes, mAuxVarInfoBuilder, mTypeHandler, mTypeSizeComputer);
		mFunctionHandler = new FunctionHandler(mLogger, mNameHandler, mExpressionTranslation, mProcedureManager,
				mTypeHandler, mReporter, mAuxVarInfoBuilder, this, mLocationFactory, mSymbolTable,
				mExprResultTransformer, mVariablesOnHeap);
		mArrayHandler = new ArrayHandler(mSettings, mExpressionTranslation, mTypeHandler, mTypeSizes,
				mExprResultTransformer, mMemoryHandler, mLocationFactory);
		mInitHandler = new InitializationHandler(mMemoryHandler, mExpressionTranslation, mProcedureManager,
				mTypeHandler, mAuxVarInfoBuilder, mTypeSizeComputer, mTypeSizes, this, mExprResultTransformer);
		mStandardFunctionHandler = new StandardFunctionHandler(functionTable, mAuxVarInfoBuilder, mNameHandler,
				mExpressionTranslation, mMemoryHandler, mTypeSizeComputer, mProcedureManager, this, mReporter,
				mTypeSizes, mSymbolTable, mSettings, mExprResultTransformer, mLocationFactory, mTypeHandler);

		mPostProcessor = new PostProcessor(mLogger, mExpressionTranslation, mTypeHandler, mReporter, mAuxVarInfoBuilder,
				mFunctionToIndex, mTypeSizes, mSymbolTable, mStaticObjectsHandler, mSettings, mProcedureManager,
				mMemoryHandler, mInitHandler, mFunctionHandler, this);
	}

	/**
	 * Constructor for CHandler in main run mode. You need a CHandler that was in prerun mode.
	 *
	 * @param prerunCHandler
	 * @param procedureManager
	 *            the procedureManager is an argument because the {@link ACSLHandler} depends on having the same
	 *            instance than the {@link CHandler}
	 * @param expressionTranslation
	 * @param typeHandler
	 * @param staticObjectsHandler
	 * @param typeSizeAndOffsetComputer
	 * @param symbolTable
	 * @param typeSizes
	 */
	public CHandler(final CHandler prerunCHandler, final ProcedureManager procedureManager,
			final StaticObjectsHandler staticObjectsHandler, final TypeHandler typeHandler,
			final ExpressionTranslation expressionTranslation,
			final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer, final INameHandler nameHandler,
			final FlatSymbolTable symbolTable, final TypeSizes typeSizes) {
		assert prerunCHandler.mIsPrerun : "CHandler not in prerun mode";
		mIsPrerun = false;

		mContract = new ArrayList<>();
		mInnerMostLoopLabel = new ArrayDeque<>();
		mBoogieIdsOfHeapVars = new LinkedHashSet<>();
		mCurrentDeclaredTypes = new ArrayDeque<>();
		mGlobAcslExtractors = new ArrayList<>();
		mDeclarations = new ArrayList<>();

		// reuse these parts of the old CHandler that have state that was created during the prerun
		mVariablesOnHeap = prerunCHandler.mVariablesOnHeap;
		mFunctionToIndex = prerunCHandler.mFunctionToIndex;
		mBacktranslator = prerunCHandler.mBacktranslator;
		mLocationFactory = prerunCHandler.mLocationFactory;

		// reuse these parts of the old CHandler that do not have state that was created during the prerun
		mLogger = prerunCHandler.mLogger;
		mSettings = prerunCHandler.mSettings;
		mReachableDeclarations = prerunCHandler.mReachableDeclarations;
		mReporter = prerunCHandler.mReporter;

		// we need to replace the name handler and all instances that depend on it
		mNameHandler = nameHandler;
		mSymbolTable = symbolTable;
		mTypeSizes = typeSizes;

		// we need to replace the static objects handler and all instances that depend on it
		mStaticObjectsHandler = staticObjectsHandler;
		mTypeHandler = typeHandler;
		mExpressionTranslation = expressionTranslation;
		mTypeSizeComputer = typeSizeAndOffsetComputer;

		// we need to replace the procedure manager and all instances that depend on it
		mProcedureManager = procedureManager;

		mAuxVarInfoBuilder = new AuxVarInfoBuilder(nameHandler, typeHandler, procedureManager);

		// the memory handler also retains information from the prerun
		mMemoryHandler = new MemoryHandler(prerunCHandler.mMemoryHandler, typeSizes, nameHandler, typeHandler,
				expressionTranslation, procedureManager, typeSizeAndOffsetComputer, mAuxVarInfoBuilder, mSettings);
		mStructHandler = new StructHandler(mMemoryHandler, mTypeSizeComputer, mExpressionTranslation, mTypeHandler,
				mLocationFactory);
		mExprResultTransformer = new ExpressionResultTransformer(this, mMemoryHandler, mStructHandler,
				mExpressionTranslation, mTypeSizes, mAuxVarInfoBuilder, mTypeHandler, mTypeSizeComputer);
		mFunctionHandler = new FunctionHandler(mLogger, mNameHandler, mExpressionTranslation, procedureManager,
				mTypeHandler, mReporter, mAuxVarInfoBuilder, this, mLocationFactory, mSymbolTable,
				mExprResultTransformer, mVariablesOnHeap);
		mArrayHandler = new ArrayHandler(mSettings, mExpressionTranslation, mTypeHandler, mTypeSizes,
				mExprResultTransformer, mMemoryHandler, mLocationFactory);
		mInitHandler = new InitializationHandler(mMemoryHandler, mExpressionTranslation, procedureManager, mTypeHandler,
				mAuxVarInfoBuilder, mTypeSizeComputer, mTypeSizes, this, mExprResultTransformer);
		mStandardFunctionHandler = new StandardFunctionHandler(prerunCHandler.mFunctionTable, mAuxVarInfoBuilder,
				mNameHandler, mExpressionTranslation, mMemoryHandler, mTypeSizeComputer, procedureManager, this,
				mReporter, mTypeSizes, mSymbolTable, mSettings, mExprResultTransformer, mLocationFactory, mTypeHandler);
		mPostProcessor = new PostProcessor(mLogger, mExpressionTranslation, mTypeHandler, mReporter, mAuxVarInfoBuilder,
				mFunctionToIndex, mTypeSizes, mSymbolTable, mStaticObjectsHandler, mSettings, procedureManager,
				mMemoryHandler, mInitHandler, mFunctionHandler, this);
	}

	/**
	 *
	 * @return An {@link ExpressionResultTransformer} that is bound to this {@link CHandler} instance.
	 */
	public ExpressionResultTransformer getExpressionResultTransformer() {
		return mExprResultTransformer;
	}

	/**
	 * Translates multiple DecoratorNodes, wrapped in DecoratedUnits. This is the main starting point for the CHandler.
	 *
	 * @param main
	 *            a reference to the main IDispatcher
	 * @param units
	 *            the decorator units to visit
	 * @return a result object
	 */

	public CHandlerTranslationResult visit(final IDispatcher main, final List<DecoratedUnit> units) {
		IASTNode globalHook = null;
		for (final DecoratedUnit du : units) {
			if (du.getRootNode().getCNode() != null) {
				if (main instanceof MainDispatcher) {
					((MainDispatcher) main).updateDecoratorTreeAndIterator(du.getRootNode());
				}
				visit(main, (IASTTranslationUnit) du.getRootNode().getCNode());
				globalHook = du.getRootNode().getCNode();
			}
			// ACSL?
		}

		// Generate additional boogie translation that is collected for all files.
		final ILocation loc = LocationFactory.createIgnoreCLocation();

		// (alex:) new function pointers
		final BigInteger functionPointerPointerBaseValue = BigInteger.valueOf(-1);
		for (final Entry<String, Integer> en : mFunctionToIndex.entrySet()) {
			final String funcId = SFO.FUNCTION_ADDRESS + en.getKey();
			final VarList varList = new VarList(loc, new String[] { funcId }, mTypeHandler.constructPointerType(loc));
			// would unique make sense here?? -- would potentially add lots of axioms
			mDeclarations.add(new ConstDeclaration(loc, new Attribute[0], false, varList, null, false));

			final Expression funcIdExpr = ExpressionFactory.constructIdentifierExpression(loc,
					mTypeHandler.getBoogiePointerType(), funcId, DeclarationInformation.DECLARATIONINFO_GLOBAL);

			final BigInteger offsetValue = BigInteger.valueOf(en.getValue());
			mDeclarations.add(new Axiom(loc, new Attribute[0],
					ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, funcIdExpr,
							mExpressionTranslation.constructPointerForIntegerValues(loc,
									functionPointerPointerBaseValue, offsetValue))));
		}

		mDeclarations.addAll(0, mPostProcessor.postProcess(loc, globalHook));

		/*
		 * this must come after the post processor because the post processor might add declarations when dispatching
		 * initializers of static variables
		 */
		mDeclarations.addAll(mStaticObjectsHandler.getGlobalDeclarations());

		// this has to happen after postprocessing as pping may add sizeof
		// constants for initializations
		mDeclarations.addAll(mTypeSizeComputer.getConstants());
		mDeclarations.addAll(mTypeSizeComputer.getAxioms());
		mDeclarations.addAll(mMemoryHandler.declareMemoryModelInfrastructure(this, loc, globalHook));
		mDeclarations.addAll(mInitHandler.declareInitializationInfrastructure(main, loc));

		// add type declarations introduced by the translation, e.g., $Pointer$
		mDeclarations.addAll(
				((TypeHandler) mTypeHandler).constructTranslationDefinedDeclarations(loc, mExpressionTranslation));

		/**
		 * For Notes on our handling of procedures see {@link FunctionHandler.handleFunctionDefinition(..)}. Short
		 * version:
		 * <li>procedure implementations have already been inserted into the Boogie program by code above
		 * <li>procedure declarations have been collected in the ProcedureManager
		 * <li>now we recompute the declarations, in order to give them correct modifies clauses and insert them into
		 * the Boogie program
		 *
		 * have to block this in prerun, because there, memory model is not declared which may cause problems with the
		 * call graph computation
		 */
		if (!mIsPrerun) {
			// handle proc. declaration & resolve their transitive modified globals
			mDeclarations.addAll(mProcedureManager.computeFinalProcedureDeclarations(mMemoryHandler));
		}

		/**
		 * Add declarations of Boogie functions (as opposed to Boogie procedures) to the Boogie program that have been
		 * collected by the ExpressionTranslation
		 */
		final Collection<FunctionDeclaration> declaredFunctions =
				mExpressionTranslation.getFunctionDeclarations().getDeclaredFunctions().values();
		mExpressionTranslation.getFunctionDeclarations().finish();
		mDeclarations.addAll(declaredFunctions);

		// TODO Need to get a CLocation from somewhere
		// the overall translation result:
		final Unit boogieUnit = new Unit(
				mLocationFactory.createRootCLocation(
						units.stream().map(a -> a.getSourceTranslationUnit()).collect(Collectors.toSet())),
				mDeclarations.toArray(new Declaration[mDeclarations.size()]));
		final IASTTranslationUnit hook = units.get(0).getSourceTranslationUnit();

		// annotate the Unit with LTLPropertyChecks if applicable
		for (final LTLExpressionExtractor ex : mGlobAcslExtractors) {
			final Map<String, LTLPropertyCheck.CheckableExpression> checkableAtomicPropositions = new LinkedHashMap<>();

			for (final Entry<String, de.uni_freiburg.informatik.ultimate.model.acsl.ast.Expression> en : ex
					.getAP2SubExpressionMap().entrySet()) {
				final ExpressionResult r = (ExpressionResult) main.dispatch(en.getValue(), hook);
				// TODO: some switchToRValue and handling of sideeffects?
				checkableAtomicPropositions.put(en.getKey(), new CheckableExpression(r.getLrValue().getValue(), null));
			}
			final LTLPropertyCheck propCheck =
					new LTLPropertyCheck(ex.getLTLFormatString(), checkableAtomicPropositions, null);
			propCheck.annotate(boogieUnit);
		}

		return new CHandlerTranslationResult(boogieUnit, mSymbolTable.getBoogieCIdentifierMapping());
	}

	/**
	 * @deprecated is not supported in this handler! Do not use!
	 */
	@Deprecated

	public Result visit(final IDispatcher main, final ACSLNode node) {
		throw new UnsupportedOperationException("Implementation Error: Use ACSLHandler for: " + node.getClass());
	}

	public Result visit(final IDispatcher main, final CASTDesignatedInitializer node) {
		return mStructHandler.handleDesignatedInitializer(main, mMemoryHandler, mStructHandler, node);
	}

	public Result visit(final IDispatcher main, final IASTArraySubscriptExpression node) {
		return mArrayHandler.handleArraySubscriptExpression(main, mMemoryHandler, mStructHandler, node);
	}

	public Result visit(final IDispatcher main, final IASTASMDeclaration node) {
		if (mSettings.isSvcompMode()) {
			// workaround for now: ignore inline assembler instructions
			return new SkipResult();
		}
		final String msg = "CHandler: Not yet implemented: \"" + node.getRawSignature() + "\" (Type: "
				+ node.getClass().getName() + ")";
		throw new UnsupportedSyntaxException(mLocationFactory.createCLocation(node), msg);
	}

	public Result visit(final IDispatcher main, final IASTBinaryExpression node) {
		final ILocation loc = mLocationFactory.createCLocation(node);
		final ExpressionResult leftOperand = (ExpressionResult) main.dispatch(node.getOperand1());
		final ExpressionResult rightOperand = (ExpressionResult) main.dispatch(node.getOperand2());

		switch (node.getOperator()) {
		case IASTBinaryExpression.op_assign: {
			final ExpressionResultBuilder builder = new ExpressionResultBuilder();
			builder.addAllExceptLrValue(leftOperand);
			final CType lType = leftOperand.getLrValue().getCType().getUnderlyingType();
			final ExpressionResult rightOperandSwitched =
					mExprResultTransformer.makeRepresentationReadyForConversionAndRexBoolToIntIfNecessary(rightOperand,
							this, loc, lType, node);
			builder.addAllIncludingLrValue(rightOperandSwitched);
			return makeAssignment(loc, leftOperand.getLrValue(), leftOperand.getNeighbourUnionFields(), builder.build(),
					node);
		}
		case IASTBinaryExpression.op_equals:
		case IASTBinaryExpression.op_notequals: {
			final ExpressionResult rl =
					mExprResultTransformer.switchToRValueAndRexBoolToIntIfNecessary(leftOperand, loc, node);
			final ExpressionResult rr =
					mExprResultTransformer.switchToRValueAndRexBoolToIntIfNecessary(rightOperand, loc, node);
			return handleEqualityOperators(loc, node.getOperator(), rl, rr);
		}
		case IASTBinaryExpression.op_greaterEqual:
		case IASTBinaryExpression.op_greaterThan:
		case IASTBinaryExpression.op_lessEqual:
		case IASTBinaryExpression.op_lessThan: {
			final ExpressionResult rl = mExprResultTransformer.switchToRValueIfNecessary(leftOperand, loc, node);
			final ExpressionResult rr = mExprResultTransformer.switchToRValueIfNecessary(rightOperand, loc, node);
			return handleRelationalOperators(loc, node.getOperator(), rl, rr);
		}

		case IASTBinaryExpression.op_logicalAnd: {
			final ExpressionResult rl =
					mExprResultTransformer.switchToRValueAndRexIntToBoolIfNecessary(leftOperand, loc, node);
			final ExpressionResult rr =
					mExprResultTransformer.switchToRValueAndRexIntToBoolIfNecessary(rightOperand, loc, node);

			final ExpressionResultBuilder builder = new ExpressionResultBuilder();
			// // NOTE: no rr.stmt
			builder.addAllExceptLrValue(rl);
			// NOTE: do not unconditionally add rr.stmt as it may be short-circuited
			builder.addDeclarations(rr.getDeclarations());
			builder.addAuxVars(rr.getAuxVars());
			builder.addOverapprox(rr.getOverapprs());

			if (rr.getStatements().isEmpty()) {
				// no statements in right operands, hence no side effects in
				// operand
				// we can directly combine operands with LOGICAND
				final RValue newRVal = new RValue(
						ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND,
								rl.getLrValue().getValue(), rr.getLrValue().getValue()),
						new CPrimitive(CPrimitive.CPrimitives.INT), true);

				builder.setLrValue(newRVal);
				return builder.build();
			}
			// create and add tmp var #t~AND~UID
			final CPrimitive intType = new CPrimitive(CPrimitives.INT);
			final AuxVarInfo resNameAuxvar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, intType,
					new PrimitiveType(loc, BoogieType.TYPE_BOOL, SFO.BOOL), SFO.AUXVAR.SHORTCIRCUIT);
			builder.addDeclaration(resNameAuxvar.getVarDec());
			builder.addAuxVar(resNameAuxvar);
			final RValue tmpRval = new RValue(resNameAuxvar.getExp(), intType, true);
			final RValue resRval = tmpRval;
			// #t~AND~UID = left

			final AssignmentStatement aStat = StatementFactory.constructAssignmentStatement(loc,
					new LeftHandSide[] { resNameAuxvar.getLhs() }, new Expression[] { rl.getLrValue().getValue() });
			for (final Overapprox overapprItem : builder.getOverappr()) {
				overapprItem.annotate(aStat);
			}
			builder.addStatement(aStat);
			// if (#t~AND~UID) {#t~AND~UID = right;}
			final ArrayList<Statement> outerThenPart = new ArrayList<>();
			outerThenPart.addAll(rr.getStatements());

			outerThenPart.add(StatementFactory.constructAssignmentStatement(loc,
					new LeftHandSide[] { resNameAuxvar.getLhs() }, new Expression[] { rr.getLrValue().getValue() }));
			final IfStatement ifStatement = new IfStatement(loc, tmpRval.getValue(),
					outerThenPart.toArray(new Statement[outerThenPart.size()]), new Statement[0]);
			// stmt.add(ifStatement);
			builder.addStatement(ifStatement);
			builder.setLrValue(resRval);
			return builder.build();
			// return new ExpressionResult(stmt, resRval, decl, auxVars, overappr);
		}
		case IASTBinaryExpression.op_logicalOr: {
			final ExpressionResult rl =
					mExprResultTransformer.switchToRValueAndRexIntToBoolIfNecessary(leftOperand, loc, node);
			final ExpressionResult rr =
					mExprResultTransformer.switchToRValueAndRexIntToBoolIfNecessary(rightOperand, loc, node);

			final ExpressionResultBuilder builder = new ExpressionResultBuilder();

			// // NOTE: no rr.stmt
			builder.addAllExceptLrValue(rl);
			// NOTE: do not unconditionally add rr.stmt as it may be short-circuited
			builder.addDeclarations(rr.getDeclarations());
			builder.addAuxVars(rr.getAuxVars());
			builder.addOverapprox(rr.getOverapprs());

			if (rr.getStatements().isEmpty()) {
				// no auxVar in operands, hence no side effects in operands
				// we can directly combine operands with LOGICOR
				final RValue resultValue = new RValue(
						ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICOR,
								rl.getLrValue().getValue(), rr.getLrValue().getValue()),
						new CPrimitive(CPrimitive.CPrimitives.INT), true);
				builder.setLrValue(resultValue);
				return builder.build();

			}
			// create and add tmp var #t~OR~UID
			final CPrimitive intType = new CPrimitive(CPrimitives.INT);
			final AuxVarInfo resNameAuxvar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, intType,
					new PrimitiveType(loc, BoogieType.TYPE_BOOL, SFO.BOOL), SFO.AUXVAR.SHORTCIRCUIT);
			builder.addDeclaration(resNameAuxvar.getVarDec());
			builder.addAuxVar(resNameAuxvar);

			final RValue tmpRval = new RValue(resNameAuxvar.getExp(), intType, true);
			final RValue resRval = tmpRval;
			// #t~OR~UID = left
			final AssignmentStatement aStat = StatementFactory.constructAssignmentStatement(loc,
					new LeftHandSide[] { resNameAuxvar.getLhs() }, new Expression[] { rl.getLrValue().getValue() });
			for (final Overapprox overapproxItem : builder.getOverappr()) {
				overapproxItem.annotate(aStat);
			}
			builder.addStatement(aStat);
			// if (#t~OR~UID) {} else {#t~OR~UID = right;}
			final ArrayList<Statement> outerElsePart = new ArrayList<>();
			outerElsePart.addAll(rr.getStatements());

			outerElsePart.add(StatementFactory.constructAssignmentStatement(loc,
					new LeftHandSide[] { resNameAuxvar.getLhs() }, new Expression[] { rr.getLrValue().getValue() }));
			final IfStatement ifStatement = new IfStatement(loc, tmpRval.getValue(), new Statement[0],
					outerElsePart.toArray(new Statement[outerElsePart.size()]));
			for (final Overapprox overapprItem : builder.getOverappr()) {
				overapprItem.annotate(ifStatement);
			}
			builder.addStatement(ifStatement);
			builder.setLrValue(resRval);
			return builder.build();
		}
		case IASTBinaryExpression.op_modulo:
		case IASTBinaryExpression.op_multiply:
		case IASTBinaryExpression.op_divide: {
			final ExpressionResult rl =
					mExprResultTransformer.switchToRValueAndRexBoolToIntIfNecessary(leftOperand, loc, node);
			final ExpressionResult rr =
					mExprResultTransformer.switchToRValueAndRexBoolToIntIfNecessary(rightOperand, loc, node);
			return handleMultiplicativeOperation(loc, null, node.getOperator(), rl, rr, node);
		}
		case IASTBinaryExpression.op_moduloAssign:
		case IASTBinaryExpression.op_multiplyAssign:
		case IASTBinaryExpression.op_divideAssign: {
			final ExpressionResult rl =
					mExprResultTransformer.switchToRValueAndRexBoolToIntIfNecessary(leftOperand, loc, node);
			final ExpressionResult rr =
					mExprResultTransformer.switchToRValueAndRexBoolToIntIfNecessary(rightOperand, loc, node);
			return handleMultiplicativeOperation(loc, leftOperand.getLrValue(), node.getOperator(), rl, rr, node);
		}
		case IASTBinaryExpression.op_plus:
		case IASTBinaryExpression.op_minus: {
			// if we are "adding" arrays, they must be treated as pointers
			final ExpressionResult lDecayed = decayArrayToPointer(leftOperand, loc, node);
			final ExpressionResult rDecayed = decayArrayToPointer(rightOperand, loc, node);
			assert !(leftOperand.getLrValue().getCType() instanceof CArray) || node
					.getOperator() == IASTBinaryExpression.op_plus : "subtraction is not allowed in pointer arithmetic, right?";
			assert !(rightOperand.getLrValue().getCType() instanceof CArray) || node
					.getOperator() == IASTBinaryExpression.op_plus : "subtraction is not allowed in pointer arithmetic, right?";

			final ExpressionResult rl =
					mExprResultTransformer.switchToRValueAndRexBoolToIntIfNecessary(lDecayed, loc, node);
			final ExpressionResult rr =
					mExprResultTransformer.switchToRValueAndRexBoolToIntIfNecessary(rDecayed, loc, node);

			return handleAdditiveOperation(loc, null, node.getOperator(), rl, rr, node);
		}
		case IASTBinaryExpression.op_plusAssign:
		case IASTBinaryExpression.op_minusAssign: {
			// if we are "adding" arrays, they must be treated as pointers
			final ExpressionResult lDecayed = decayArrayToPointer(leftOperand, loc, node);
			final ExpressionResult rDecayed = decayArrayToPointer(rightOperand, loc, node);
			assert !(leftOperand.getLrValue().getCType() instanceof CArray) || node
					.getOperator() == IASTBinaryExpression.op_plus : "subtraction is not allowed in pointer arithmetic, right?";
			assert !(rightOperand.getLrValue().getCType() instanceof CArray) || node
					.getOperator() == IASTBinaryExpression.op_plus : "subtraction is not allowed in pointer arithmetic, right?";

			final ExpressionResult rl =
					mExprResultTransformer.switchToRValueAndRexBoolToIntIfNecessary(lDecayed, loc, node);
			final ExpressionResult rr =
					mExprResultTransformer.switchToRValueAndRexBoolToIntIfNecessary(rDecayed, loc, node);
			return handleAdditiveOperation(loc, leftOperand.getLrValue(), node.getOperator(), rl, rr, node);
		}
		case IASTBinaryExpression.op_binaryAnd:
		case IASTBinaryExpression.op_binaryOr:
		case IASTBinaryExpression.op_binaryXor: {
			final ExpressionResult rl =
					mExprResultTransformer.switchToRValueAndRexBoolToIntIfNecessary(leftOperand, loc, node);
			final ExpressionResult rr =
					mExprResultTransformer.switchToRValueAndRexBoolToIntIfNecessary(rightOperand, loc, node);
			return handleBitwiseArithmeticOperation(loc, null, node.getOperator(), rl, rr, node);
		}
		case IASTBinaryExpression.op_binaryAndAssign:
		case IASTBinaryExpression.op_binaryOrAssign:
		case IASTBinaryExpression.op_binaryXorAssign: {
			final ExpressionResult rl =
					mExprResultTransformer.switchToRValueAndRexBoolToIntIfNecessary(leftOperand, loc, node);
			final ExpressionResult rr =
					mExprResultTransformer.switchToRValueAndRexBoolToIntIfNecessary(rightOperand, loc, node);
			return handleBitwiseArithmeticOperation(loc, leftOperand.getLrValue(), node.getOperator(), rl, rr, node);
		}
		case IASTBinaryExpression.op_shiftLeft:
		case IASTBinaryExpression.op_shiftRight: {
			final ExpressionResult rl =
					mExprResultTransformer.switchToRValueAndRexBoolToIntIfNecessary(leftOperand, loc, node);
			final ExpressionResult rr =
					mExprResultTransformer.switchToRValueAndRexBoolToIntIfNecessary(rightOperand, loc, node);
			return handleBitshiftOperation(loc, null, node.getOperator(), rl, rr, node);

		}
		case IASTBinaryExpression.op_shiftLeftAssign:
		case IASTBinaryExpression.op_shiftRightAssign: {
			final ExpressionResult rl =
					mExprResultTransformer.switchToRValueAndRexBoolToIntIfNecessary(leftOperand, loc, node);
			final ExpressionResult rr =
					mExprResultTransformer.switchToRValueAndRexBoolToIntIfNecessary(rightOperand, loc, node);
			return handleBitshiftOperation(loc, leftOperand.getLrValue(), node.getOperator(), rl, rr, node);
		}
		default:
			final String msg = "Unknown or unsupported unary operation";
			throw new UnsupportedSyntaxException(loc, msg);
		}
	}

	public Result visit(final IDispatcher main, final IASTBreakStatement node) {
		final ArrayList<Statement> stmt = new ArrayList<>();
		stmt.add(new BreakStatement(mLocationFactory.createCLocation(node)));
		return new ExpressionResult(stmt, null);
	}

	/**
	 * Translate a case statement for use inside a switch statement. C99:6.8.4.2-3: "The expression of each case label
	 * shall be an integer constant expression and no two of the case constant expressions in the same switch statement
	 * shall have the same value after conversion."
	 *
	 */

	public Result visit(final IDispatcher main, final IASTCaseStatement node) {
		final ILocation loc = mLocationFactory.createCLocation(node);
		final ExpressionResult dispatched = (ExpressionResult) main.dispatch(node.getExpression());
		final ExpressionResult switched = mExprResultTransformer.switchToRValueIfNecessary(dispatched,
				mLocationFactory.createCLocation(node), node);
		return mExpressionTranslation.convertIntToInt(loc, switched, new CPrimitive(CPrimitives.INT));
	}

	public Result visit(final IDispatcher main, final IASTCastExpression node) {
		final ILocation loc = mLocationFactory.createCLocation(node);

		// TODO: check validity of cast?

		final TypesResult resTypes = (TypesResult) main.dispatch(node.getTypeId().getDeclSpecifier());

		mCurrentDeclaredTypes.push(resTypes);
		final DeclaratorResult declResult = (DeclaratorResult) main.dispatch(node.getTypeId().getAbstractDeclarator());
		final CType newCType = declResult.getDeclaration().getType();
		mCurrentDeclaredTypes.pop();

		ExpressionResult expr = (ExpressionResult) main.dispatch(node.getOperand());

		if (!expr.hasLRValue()) {
			// creates a void expression for null RValues
			final Expression newExpression = ExpressionFactory.createVoidDummyExpression(loc);
			final RValue rVal = new RValue(newExpression, new CPrimitive(CPrimitives.VOID));
			expr = new ExpressionResultBuilder().addAllExceptLrValue(expr).setLrValue(rVal).build();
		}
		expr = mExprResultTransformer.makeRepresentationReadyForConversion(expr, this, loc, newCType, node);

		checkUnsupportedPointerCast(loc, newCType, expr);

		expr = mExprResultTransformer.rexBoolToIntIfNecessary(expr, loc);
		expr = mExprResultTransformer.convert(loc, expr, newCType);
		return expr;
	}

	public Result visit(final IDispatcher main, final IASTCompoundStatement node) {
		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();
		LRValue expr = null;
		final IASTNode parent = node.getParent();

		if (isNewScopeRequired(parent)) {
			beginScope();
		}

		for (final IASTNode child : node.getChildren()) {
			checkForACSL(main, resultBuilder, child, null, true);
			final Result r = main.dispatch(child);
			if (r instanceof ExpressionResult) {
				final ExpressionResult res = (ExpressionResult) r;
				resultBuilder.addDeclarations(res.getDeclarations());
				resultBuilder.addStatements(res.getStatements());
				expr = res.getLrValue();
			} else if (r.getNode() != null && r.getNode() instanceof Body) {
				assert false : "should not happen, as CompoundStatement now yields an "
						+ "ExpressionResult or a CompoundStatementExpressionResult";
				// already have a unique naming for variables! --> unfold
				final Body b = (Body) r.getNode();
				resultBuilder.addDeclarations(Arrays.asList(b.getLocalVars()));
				resultBuilder.addStatements(Arrays.asList(b.getBlock()));
			} else if (r instanceof SkipResult) {
				// skip
			} else {
				assert false : "should not happen, as CompoundStatement now yields an "
						+ "ExpressionResult or a CompoundStatementExpressionResult, but was " + r.getClass();
			}
		}
		checkForACSL(main, resultBuilder, null, node, true);
		if (isNewScopeRequired(parent)) {
			updateStmtsAndDeclsAtScopeEnd(resultBuilder, node);

			endScope();
		}
		resultBuilder.setLrValue(expr);
		return resultBuilder.build();
	}

	public Result visit(final IDispatcher main, final IASTConditionalExpression node) {
		final ILocation loc = mLocationFactory.createCLocation(node);
		assert node.getChildren().length == 3;
		ExpressionResult opCondition = (ExpressionResult) main.dispatch(node.getLogicalConditionExpression());
		opCondition = mExprResultTransformer.switchToRValueIfNecessary(opCondition, loc, node);
		ExpressionResult opPositive = (ExpressionResult) main.dispatch(node.getPositiveResultExpression());
		opPositive = mExprResultTransformer.switchToRValueIfNecessary(opPositive, loc, node);
		ExpressionResult opNegative = (ExpressionResult) main.dispatch(node.getNegativeResultExpression());
		opNegative = mExprResultTransformer.switchToRValueIfNecessary(opNegative, loc, node);
		return handleConditionalOperator(loc, opCondition, opPositive, opNegative, node);
	}

	public Result visit(final IDispatcher main, final IASTContinueStatement cs) {
		final ILocation loc = mLocationFactory.createCLocation(cs);
		final ArrayList<Statement> stmt = new ArrayList<>();
		stmt.add(new GotoStatement(loc, new String[] { mInnerMostLoopLabel.peek() }));
		final ExpressionResult contResult = new ExpressionResult(stmt, null);
		return contResult;
	}

	public Result visit(final IDispatcher main, final IASTDeclarationStatement node) {
		return main.dispatch(node.getDeclaration());
	}

	public Result visit(final IDispatcher main, final IASTDeclarator node) {
		final ILocation loc = mLocationFactory.createCLocation(node);
		final TypesResult pendingResType = mCurrentDeclaredTypes.peek();

		// are we running the PRDispatcher (PR stands for PreRun)?
		// --> in that case "isOnHeap" has not yet been determined, we set it to false
		final boolean isOnHeap = (mIsPrerun ? false : mVariablesOnHeap.contains(node));

		final IASTPointerOperator[] pointerOps = node.getPointerOperators();
		final CType nestedPointerType = getPointerType(pointerOps.length, pendingResType.getCType());
		final TypesResult resType = TypesResult.create(pendingResType, nestedPointerType);

		// Adapt the name for multiparse input
		final String declName;
		final CType cType;
		if (node instanceof IASTArrayDeclarator) {
			final IASTArrayDeclarator arrDecl = (IASTArrayDeclarator) node;

			// the innermost type is the value type..
			CType arrayType = resType.getCType();

			// expression results of from array modifiers
			final ArrayList<ExpressionResult> expressionResults = new ArrayList<>();

			final ListIterator<IASTArrayModifier> it =
					Arrays.asList(arrDecl.getArrayModifiers()).listIterator(arrDecl.getArrayModifiers().length);
			while (it.hasPrevious()) {
				final IASTArrayModifier am = it.previous();
				final RValue sizeFactor;
				if (am.getConstantExpression() != null) {
					// case where we have a number between the brackets,
					// e.g., a[23] or a[n+1]
					final ExpressionResult dispatched = (ExpressionResult) main.dispatch(am.getConstantExpression());
					final ExpressionResult switched =
							mExprResultTransformer.switchToRValueIfNecessary(dispatched, loc, node);
					final ExpressionResult converted = mExpressionTranslation.convertIntToInt(loc, switched,
							mExpressionTranslation.getCTypeOfPointerComponents());
					expressionResults.add(converted);
					sizeFactor = (RValue) converted.getLrValue();
				} else if (am.getConstantExpression() == null
						&& arrDecl.getArrayModifiers()[arrDecl.getArrayModifiers().length - 1] == am) {
					// the innermost array modifier may be empty, if there is an initializer; like
					// int a[1][2][] = {...}
					final int intSizeFactor;
					if (arrDecl.getInitializer() != null) {
						if (arrDecl.getInitializer() instanceof IASTEqualsInitializer) {
							intSizeFactor = computeSizeOfInitializer((IASTEqualsInitializer) arrDecl.getInitializer());
						} else {
							throw new UnsupportedOperationException("expected IASTEqualsInitializer");
						}
					} else if (resType.getCType() instanceof CFunction) {
						// if we have an array of function pointers,
						// the initializer is stored in the parent node
						// 2016-12-31 Matthias: I think this is only a workaround.
						// What if we do not have an array of function pointers
						// but an arrray of pointers to function pointers? Then
						// we probably have to check the parent of the parent
						final IASTFunctionDeclarator fundecl = (IASTFunctionDeclarator) arrDecl.getParent();
						if (fundecl.getInitializer() != null) {
							intSizeFactor = computeSizeOfInitializer((IASTEqualsInitializer) fundecl.getInitializer());
						} else {
							throw new UnsupportedOperationException("expected initializer");
						}
					} else {
						// we have an incomplete array type without an initializer --
						// this may happen in a function parameter..
						intSizeFactor = CArray.INCOMPLETE_ARRY_MAGIC_NUMBER;
					}
					final CPrimitive ctype = mExpressionTranslation.getCTypeOfPointerComponents();
					final Expression sizeExpression =
							mTypeSizes.constructLiteralForIntegerType(loc, ctype, BigInteger.valueOf(intSizeFactor));
					sizeFactor = new RValue(sizeExpression, ctype, false, false);

				} else {
					throw new IncorrectSyntaxException(loc, "wrong array type in declaration");
				}
				arrayType = new CArray(sizeFactor, arrayType);
			}
			final ExpressionResult allResults = new ExpressionResultBuilder()
					.addAllExceptLrValue(expressionResults.toArray(new ExpressionResult[expressionResults.size()]))
					.build();
			if (!allResults.getDeclarations().isEmpty() || !allResults.getStatements().isEmpty()
					|| !allResults.getAuxVars().isEmpty()) {
				throw new AssertionError("passing these results is not yet implemented");
			}
			cType = arrayType;
			declName = getNonFunctionDeclaratorName(node);
		} else if (node instanceof IASTStandardFunctionDeclarator) {
			// functions as well as function pointers can have IASTStandardFunctionDeclarator
			final IASTStandardFunctionDeclarator funcDecl = (IASTStandardFunctionDeclarator) node;
			final IASTParameterDeclaration[] paramDecls = funcDecl.getParameters();
			CDeclaration[] paramsParsed = new CDeclaration[paramDecls.length];
			for (int i = 0; i < paramDecls.length; i++) {
				final DeclaratorResult decl = (DeclaratorResult) main.dispatch(paramDecls[i]);
				if (decl.getDeclaration().getName() == "" && decl.getDeclaration().getType() instanceof CPrimitive
						&& ((CPrimitive) decl.getDeclaration().getType()).getType().equals(CPrimitives.VOID)) {
					assert paramDecls.length == 1;
					paramsParsed = new CDeclaration[0];
					break;
				}
				paramsParsed[i] = decl.getDeclaration();
			}
			final IASTName name = funcDecl.getName();
			final IBinding binding = name.resolveBinding();
			final CFunction funcType;

			if (binding == null) {
				// this happens if the parent is actually a cast
				funcType =
						CFunction.createEmptyCFunction().newReturnType(resType.getCType()).newParameter(paramsParsed);
			} else if (binding instanceof IProblemBinding) {
				// this happens if CDT detects a parse issue at this position
				mLogger.warn("Detected problem " + ((IProblemBinding) binding).getMessage() + " at " + loc);
				funcType =
						CFunction.createEmptyCFunction().newReturnType(resType.getCType()).newParameter(paramsParsed);
			} else if (binding instanceof IFunction) {
				final IFunction funBinding = (IFunction) binding;
				funcType = new CFunction(false, funBinding.isInline(), false, false, funBinding.isExtern(),
						resType.getCType(), paramsParsed, funBinding.takesVarArgs());
			} else if (binding instanceof IVariable) {
				// it is a function pointer
				funcType = extractFunctionType(resType, paramsParsed, (IVariable) binding);
			} else if (binding instanceof ITypedef) {
				// it is a typedef of a function pointer or a function
				funcType = extractFunctionType(resType, paramsParsed, (ITypedef) binding);
			} else {
				throw new UnsupportedOperationException(
						"Cannot extract function type from binding " + binding.getClass());
			}
			cType = funcType;
			declName = mSymbolTable.applyMultiparseRenaming(node.getContainingFilename(), node.getName().toString());
		} else if (node instanceof ICASTKnRFunctionDeclarator) {
			final ICASTKnRFunctionDeclarator funcDecl = (ICASTKnRFunctionDeclarator) node;

			assert funcDecl.getParameterDeclarations().length == funcDecl
					.getParameterNames().length : "implicit int declarations are forbidden from C99 on, this is one, right?";

			final CDeclaration[] paramsParsed = new CDeclaration[funcDecl.getParameterDeclarations().length];
			for (int i = 0; i < funcDecl.getParameterDeclarations().length; i++) {
				final DeclarationResult paramDeclRes =
						(DeclarationResult) main.dispatch(funcDecl.getParameterDeclarations()[i]);
				assert paramDeclRes.getDeclarations().size() == 1;
				paramsParsed[i] = paramDeclRes.getDeclarations().get(0);
			}
			final IFunction binding = (IFunction) funcDecl.getName().getBinding();
			final CFunction funcType = new CFunction(false, binding.isInline(), false, false, binding.isExtern(),
					resType.getCType(), paramsParsed, binding.takesVarArgs());
			cType = funcType;
			declName = mSymbolTable.applyMultiparseRenaming(node.getContainingFilename(), node.getName().toString());
		} else {
			cType = resType.getCType();
			declName = getNonFunctionDeclaratorName(node);
		}
		final int bitfieldSize;
		if (node instanceof IASTFieldDeclarator) {
			final IASTExpression expr = ((IASTFieldDeclarator) node).getBitFieldSize();
			bitfieldSize = Integer.parseInt(expr.getRawSignature());
		} else {
			// we use -1 to indicate that this is no bitfield
			bitfieldSize = -1;
		}

		if (node.getNestedDeclarator() != null) {
			mCurrentDeclaredTypes.push(TypesResult.create(resType, cType));
			DeclaratorResult result = (DeclaratorResult) main.dispatch(node.getNestedDeclarator());
			mCurrentDeclaredTypes.pop();
			if (node.getInitializer() != null) {
				final CDeclaration cdec = result.getDeclaration();
				result = new DeclaratorResult(new CDeclaration(cdec.getType(), cdec.getName(), node.getInitializer(),
						null, cdec.isOnHeap(), CStorageClass.UNSPECIFIED, bitfieldSize));
			}
			return result;
		}
		final DeclaratorResult result = new DeclaratorResult(new CDeclaration(cType, declName, node.getInitializer(),
				null, isOnHeap, CStorageClass.UNSPECIFIED, bitfieldSize));
		return result;
	}

	private static CFunction extractFunctionType(final TypesResult resType, final CDeclaration[] paramsParsed,
			final ITypedef binding) {
		IType typedefType = binding.getType();
		if (typedefType instanceof IFunctionType) {
			return new CFunction(false, false, false, false, false, resType.getCType(), paramsParsed,
					((IFunctionType) typedefType).takesVarArgs());
		}
		final IPointerType initialPointer;
		if (typedefType instanceof IPointerType) {
			initialPointer = (IPointerType) typedefType;
		} else {
			throw new UnsupportedOperationException("Cannot extract function type from typedef " + typedefType);
		}
		while (typedefType instanceof IPointerType) {
			typedefType = ((IPointerType) typedefType).getType();
		}
		if (typedefType instanceof IFunctionType) {
			return new CFunction(initialPointer.isConst(), false, initialPointer.isRestrict(),
					initialPointer.isVolatile(), false, resType.getCType(), paramsParsed,
					((IFunctionType) typedefType).takesVarArgs());
		}
		throw new UnsupportedOperationException("Cannot extract function type from pointer to " + typedefType);
	}

	private static CFunction extractFunctionType(final TypesResult resType, final CDeclaration[] paramsParsed,
			final IVariable varBinding) {
		IType varType = varBinding.getType();
		if (varType instanceof IPointerType) {
			// the initial type is already the pointer type
		} else if (varType instanceof IArrayType) {
			// its an array of function pointers -- find the value type
			while (varType instanceof IArrayType) {
				varType = ((IArrayType) varType).getType();
			}
			if (!(varType instanceof IPointerType)) {
				throw new UnsupportedOperationException(
						"Cannot extract function type from array of non-pointers " + varType);
			}
		} else {
			throw new UnsupportedOperationException("Cannot extract function type from variable " + varType);
		}
		final IPointerType initialPointer = (IPointerType) varType;
		while (varType instanceof IPointerType) {
			varType = ((IPointerType) varType).getType();
		}
		if (varType instanceof IFunctionType) {
			// it was indeed a function pointer
			return new CFunction(initialPointer.isConst(), false, initialPointer.isRestrict(),
					initialPointer.isVolatile(), varBinding.isExtern(), resType.getCType(), paramsParsed,
					((IFunctionType) varType).takesVarArgs());
		}
		throw new UnsupportedOperationException("Cannot extract function type from pointer to " + varType);
	}

	/**
	 * Create a nested {@link CPointer} type that ultimately points to the supplied type. If length is smaller or equal
	 * zero, the supplied type is returned.
	 *
	 * @param length
	 *            The nesting depth
	 * @param cType
	 *            The underlying type
	 * @return The new CPointer.
	 */
	private static CType getPointerType(int length, final CType cType) {
		CType type = cType;
		for (; length > 0; --length) {
			type = new CPointer(type);
		}
		return type;
	}

	public Result visit(final IDispatcher main, final IASTDefaultStatement node) {
		final ArrayList<Statement> stmt = new ArrayList<>();
		final ArrayList<Declaration> decl = new ArrayList<>();
		// final Map<VariableDeclaration, ILocation> emptyAuxVars = new
		// LinkedHashMap<>(0);
		final Set<AuxVarInfo> emptyAuxVars = new LinkedHashSet<>(0);
		final List<Overapprox> overappr = new ArrayList<>();
		return new ExpressionResult(stmt,
				new RValue(ExpressionFactory.createBooleanLiteral(mLocationFactory.createCLocation(node), true),
						new CPrimitive(CPrimitives.INT)),
				decl, emptyAuxVars, overappr);
	}

	public Result visit(final IDispatcher main, final IASTDoStatement node) {
		final ExpressionResult condResult = (ExpressionResult) main.dispatch(node.getCondition());
		final String loopLabel = mNameHandler.getGloballyUniqueIdentifier(SFO.LOOPLABEL);
		mInnerMostLoopLabel.push(loopLabel);
		final Result bodyResult = main.dispatch(node.getBody());
		mInnerMostLoopLabel.pop();
		final LoopInvariantSpecification witnessInvariant = main.fetchInvariantAtLoop(node);
		return handleLoops(main, node, bodyResult, condResult, loopLabel, witnessInvariant);
	}

	public Result visit(final IDispatcher main, final IASTEqualsInitializer node) {
		return main.dispatch(node.getInitializerClause());
	}

	public Result visit(final IDispatcher main, final IASTExpressionList node) {
		final List<ExpressionResult> results = new ArrayList<>();
		for (final IASTExpression expr : node.getExpressions()) {
			results.add((ExpressionResult) main.dispatch(expr));
		}
		return new ExpressionListResult(results);
	}

	public Result visit(final IDispatcher main, final IASTExpressionStatement node) {
		final Result r = main.dispatch(node.getExpression());
		if (r instanceof ExpressionResult) {
			final ExpressionResult rExp = (ExpressionResult) r;

			final ArrayList<Statement> stmt = new ArrayList<>(rExp.getStatements());
			final ArrayList<Declaration> decl = new ArrayList<>(rExp.getDeclarations());
			final List<Overapprox> overappr = new ArrayList<>();

			stmt.addAll(CTranslationUtil.createHavocsForAuxVars(rExp.getAuxVars()));
			overappr.addAll(rExp.getOverapprs());
			return new ExpressionResult(stmt, rExp.getLrValue(), decl, Collections.emptySet(), overappr);
		} else if (r instanceof ExpressionListResult) {
			final ArrayList<Statement> stmt = new ArrayList<>();
			final ArrayList<Declaration> decl = new ArrayList<>();
			final List<Overapprox> overappr = new ArrayList<>();
			// final Map<VariableDeclaration, ILocation> emptyAuxVars = new
			// LinkedHashMap<>(0);
			for (final ExpressionResult res : ((ExpressionListResult) r).getList()) {
				if (!res.getStatements().isEmpty()) {
					stmt.addAll(res.getStatements());
					decl.addAll(res.getDeclarations());
					stmt.addAll(CTranslationUtil.createHavocsForAuxVars(res.getAuxVars()));
					overappr.addAll(res.getOverapprs());
				}
			}

			return new ExpressionResult(stmt, null, decl, Collections.emptySet(), overappr);
		} else if (r instanceof SkipResult) {
			return r;
		}
		final String msg = "We always convert to AssignmentStatement, other options raise this error!";
		final ILocation loc = mLocationFactory.createCLocation(node);
		throw new UnsupportedSyntaxException(loc, msg);
	}

	public Result visit(final IDispatcher main, final IASTFieldReference node) {
		return mStructHandler.handleFieldReference(main, mExprResultTransformer, node);
	}

	public Result visit(final IDispatcher main, final IASTForStatement node) {
		final String loopLabel = mNameHandler.getGloballyUniqueIdentifier(SFO.LOOPLABEL);
		final LoopInvariantSpecification witnessInvariant = main.fetchInvariantAtLoop(node);
		return handleLoops(main, node, null, null, loopLabel, witnessInvariant);
	}

	public Result visit(final IDispatcher main, final IASTFunctionCallExpression node) {
		final IASTExpression functionName = node.getFunctionNameExpression();
		if (functionName instanceof IASTIdExpression) {
			final Result standardFunction =
					mStandardFunctionHandler.translateStandardFunction(main, node, (IASTIdExpression) functionName);
			if (standardFunction != null) {
				return standardFunction;
			}
		}
		final Check check = new Check(Check.Spec.PRE_CONDITION);
		final ILocation loc = mLocationFactory.createCLocation(node, check);
		return mFunctionHandler.handleFunctionCallExpression(main, loc, functionName, node.getArguments());
	}

	public Result visit(final IDispatcher main, final IASTFunctionDefinition node) {
		if (!isReachable(node)) {
			// Unreachable function declaration. Test for parent=TU skipped: Not necessary, right?
			return new SkipResult();
		}

		final TypesResult resType = (TypesResult) main.dispatch(node.getDeclSpecifier());

		mCurrentDeclaredTypes.push(resType);
		final DeclaratorResult declResult = (DeclaratorResult) main.dispatch(node.getDeclarator());
		mCurrentDeclaredTypes.pop();
		assert declResult.getDeclaration().getType() instanceof CFunction;
		return mFunctionHandler.handleFunctionDefinition(main, mMemoryHandler, node, declResult.getDeclaration(),
				mContract);
	}

	public Result visit(final IDispatcher main, final IASTGotoStatement node) {
		final ArrayList<Statement> stmt = new ArrayList<>();
		if (!mIsPrerun) {
			final AssertStatement assertWitnessInvariant = ((MainDispatcher) main).fetchInvariantAtGoto(node);
			if (assertWitnessInvariant != null) {
				stmt.add(assertWitnessInvariant);
			}
		}
		final String[] name = new String[] { node.getName().toString() };
		stmt.add(new GotoStatement(mLocationFactory.createCLocation(node), name));
		return new ExpressionResult(stmt, null);
	}

	public Result visit(final IDispatcher main, final IASTIdExpression node) {
		final ILocation loc = mLocationFactory.createCLocation(node);

		// Apply multifile input prefixing transformations to the ID
		final String cId = node.getName().toString();
		// cIdMp is only relevant for procedures and global variables
		final String cIdMp = mSymbolTable.applyMultiparseRenaming(node.getContainingFilename(), cId);

		// deal with builtin constants
		if ("NULL".equals(cId)) {
			return new ExpressionResult(new RValue(mExpressionTranslation.constructNullPointer(loc),
					new CPointer(new CPrimitive(CPrimitives.VOID))));

		} else if ("__PRETTY_FUNCTION__".equals(cId) || "__FUNCTION__".equals(cId)) {
			// TODO: Was only in SvComp14Handler, but seems useful anywhere
			final CType returnType = new CPointer(new CPrimitive(CPrimitives.CHAR));
			// final String tId = main.mNameHandler.getTempVarUID(SFO.AUXVAR.NONDET,
			// returnType);
			// final VariableDeclaration tVarDecl = new VariableDeclaration(loc, new
			// Attribute[0], new VarList[] {
			// new VarList(loc, new String[] { tId },
			// main.mTypeHandler.constructPointerType(loc)) });
			final AuxVarInfo auxvar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, returnType, SFO.AUXVAR.NONDET);
			final RValue rvalue = new RValue(auxvar.getExp(), returnType);
			final ArrayList<Declaration> decls = new ArrayList<>();
			decls.add(auxvar.getVarDec());
			// final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();
			// auxVars.put(auxvar.getVarDec(), loc);
			return new ExpressionResult(new ArrayList<Statement>(), rvalue, decls, Collections.singleton(auxvar));
		} else if (!mSymbolTable.containsCSymbol(node, cIdMp)
				&& ("NAN".equals(cId) || "INFINITY".equals(cId) || "inf".equals(cId))) {
			final ExpressionResult result = mExpressionTranslation.createNanOrInfinity(loc, cId);
			return result;
		} else if (mExpressionTranslation.isNumberClassificationMacro(cId)) {
			final RValue rvalue = mExpressionTranslation.handleNumberClassificationMacro(loc, cId);
			return new ExpressionResult(rvalue);
		} else if ("__func__".equals(cId)) {
			final CType cType = new CPointer(new CPrimitive(CPrimitives.CHAR));
			// final String tId = mNameHandler.getTempVarUID(SFO.AUXVAR.NONDET, cType);
			// final VariableDeclaration tVarDecl = new VariableDeclaration(loc, new
			// Attribute[0],
			// new VarList[] { new VarList(loc, new String[] { tId },
			// mTypeHandler.constructPointerType(loc)) });
			final AuxVarInfo auxvar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, cType, SFO.AUXVAR.NONDET);
			final RValue rvalue = new RValue(auxvar.getExp(), cType);
			final ArrayList<Declaration> decls = new ArrayList<>();
			decls.add(auxvar.getVarDec());
			// final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();
			// auxVars.put(auxvar.getVarDec(), loc);
			return new ExpressionResult(new ArrayList<Statement>(), rvalue, decls, Collections.singleton(auxvar));
		}

		final String bId;
		final CType cType;
		final boolean useHeap;
		final boolean intFromPtr;
		DeclarationInformation declarationInformation;

		if (mSymbolTable.containsCSymbol(node, cId) && !mProcedureManager.hasProcedure(cIdMp)) {
			// a local variable
			final SymbolTableValue stv = mSymbolTable.findCSymbol(node, cId);
			bId = stv.getBoogieName();
			cType = stv.getCType();
			useHeap = isHeapVar(bId);
			intFromPtr = stv.isIntFromPointer();
			declarationInformation = stv.getDeclarationInformation();
		} else if (mSymbolTable.containsCSymbol(node, cIdMp) && !mProcedureManager.hasProcedure(cIdMp)) {
			// we have a normal variable
			final SymbolTableValue stv = mSymbolTable.findCSymbol(node, cIdMp);
			bId = stv.getBoogieName();
			cType = stv.getCType();
			useHeap = isHeapVar(bId);
			intFromPtr = stv.isIntFromPointer();
			declarationInformation = stv.getDeclarationInformation();
			// } else if (mFunctionHandler.getProcedures().keySet().contains(cId)) {
		} else if (mProcedureManager.hasProcedure(cIdMp)) {
			// C11 6.3.2.1.4 says: A function designator is an expression that
			// has function type.
			final CFunction cFunction = mProcedureManager.getCFunctionType(cIdMp);
			cType = cFunction;
			bId = SFO.FUNCTION_ADDRESS + cIdMp;
			useHeap = true;
			intFromPtr = false;
			declarationInformation = DeclarationInformation.DECLARATIONINFO_GLOBAL;
		} else if (mFunctionToIndex.containsKey(cIdMp)) {
			throw new AssertionError("function not known to function handler");
		} else {
			throw new UnsupportedSyntaxException(loc,
					"identifier is not declared (neither a variable nor a function name): " + cId + " in file "
							+ node.getContainingFilename());
		}

		BoogieType boogieType;
		{
			final ASTType astType = mTypeHandler.cType2AstType(loc, cType);
			boogieType = mTypeHandler.getBoogieTypeForBoogieASTType(astType);
		}

		LRValue lrVal = null;
		if (useHeap) {
			final IdentifierExpression idExp = // new IdentifierExpression(loc, bId);
					ExpressionFactory.constructIdentifierExpression(loc, mTypeHandler.getBoogiePointerType(), bId,
							declarationInformation);
			// convention: the ctype in the symbol table of something that we put on the
			// heap
			// is the same as it would be if we did not put it on heap
			lrVal = LRValueFactory.constructHeapLValue(mTypeHandler, idExp, cType, intFromPtr, null);
		} else {
			final VariableLHS idLhs = // new VariableLHS(loc, bId);
					ExpressionFactory.constructVariableLHS(loc, boogieType, bId, declarationInformation);
			lrVal = new LocalLValue(idLhs, cType, false, intFromPtr, null);
		}
		return new ExpressionResult(lrVal);
	}

	public Result visit(final IDispatcher main, final IASTIfStatement node) {
		final ILocation loc = mLocationFactory.createCLocation(node);
		final ArrayList<Declaration> decl = new ArrayList<>();
		final ArrayList<Statement> stmt = new ArrayList<>();
		final List<Overapprox> overappr = new ArrayList<>();
		// final Map<VariableDeclaration, ILocation> emptyAuxVars = new
		// LinkedHashMap<>();

		ExpressionResult condResult = (ExpressionResult) main.dispatch(node.getConditionExpression());
		condResult = mExprResultTransformer.switchToRValueAndRexIntToBoolIfNecessary(condResult, loc, node);
		final RValue cond = (RValue) condResult.getLrValue();
		decl.addAll(condResult.getDeclarations());
		stmt.addAll(condResult.getStatements());
		overappr.addAll(condResult.getOverapprs());
		final List<HavocStatement> havocs = CTranslationUtil.createHavocsForAuxVars(condResult.getAuxVars());

		final Result thenResult = main.dispatch(node.getThenClause());
		final List<Statement> thenStmt = new ArrayList<>();
		thenStmt.addAll(havocs);
		if (thenResult instanceof ExpressionResult) {
			final ExpressionResult re = (ExpressionResult) thenResult;
			decl.addAll(re.getDeclarations());
			thenStmt.addAll(re.getStatements());
		} else if (thenResult != null) {
			if (thenResult.getNode() instanceof Body) {
				final Body thenPart = (Body) thenResult.getNode();
				thenStmt.addAll(Arrays.asList(thenPart.getBlock()));
				decl.addAll(Arrays.asList(thenPart.getLocalVars()));
			} else if (thenResult instanceof SkipResult) {
				// add no statements or declarations
			} else {
				final String msg = "Error: unexpected dispatch result";
				throw new IncorrectSyntaxException(loc, msg);
			}
		}

		final List<Statement> elseStmt = new ArrayList<>();
		elseStmt.addAll(havocs);
		if (node.getElseClause() != null) {
			final Result elseResult = main.dispatch(node.getElseClause());
			if (elseResult instanceof ExpressionResult) {
				final ExpressionResult re = (ExpressionResult) elseResult;
				decl.addAll(re.getDeclarations());
				elseStmt.addAll(re.getStatements());
			} else if (elseResult != null) {
				if (elseResult.getNode() instanceof Body) {
					final Body elsePart = (Body) elseResult.getNode();
					elseStmt.addAll(Arrays.asList(elsePart.getBlock()));
					decl.addAll(Arrays.asList(elsePart.getLocalVars()));
				}
			} else {
				final String msg = "Error: unexpected dispatch result";
				throw new IncorrectSyntaxException(loc, msg);
			}
		}
		assert thenStmt != null;
		assert elseStmt != null;
		// TODO : handle if(pointer), if(pointer==NULL) and if(pointer==0)
		final IfStatement ifStmt = new IfStatement(loc, cond.getValue(),
				thenStmt.toArray(new Statement[thenStmt.size()]), elseStmt.toArray(new Statement[elseStmt.size()]));
		for (final Overapprox overapprItem : overappr) {
			overapprItem.annotate(ifStmt);
		}
		stmt.add(ifStmt);
		return new ExpressionResult(stmt, null, decl, Collections.emptySet(), overappr);
	}

	public Result visit(final IDispatcher main, final IASTInitializerClause node) {
		if (node.getChildren().length == 1) {
			final Result r = main.dispatch(node.getChildren()[0]);
			assert r instanceof ExpressionResult;
			final ExpressionResult rex = (ExpressionResult) r;
			return mExprResultTransformer.switchToRValueIfNecessary(rex, mLocationFactory.createCLocation(node), node);
		} else {
			// TODO 2018-11-03 Matthias:
			// added this Exception, fix soon only if this occurs often
			throw new UnsupportedOperationException(
					"Cannot understand initializer with more than two children. Is this a struct initialization? "
							+ node.getRawSignature());
		}
	}

	public Result visit(final IDispatcher main, final IASTInitializerList node) {
		final ILocation loc = mLocationFactory.createCLocation(node);
		if (node.getClauses().length != node.getSize()) {
			throw new IllegalArgumentException("You might have parsed your code with "
					+ "ITranslationUnit.AST_SKIP_TRIVIAL_EXPRESSIONS_IN_AGGREGATE_INITIALIZERS!");
		}
		final InitializerResultBuilder result = new InitializerResultBuilder();
		for (final IASTInitializerClause i : node.getClauses()) {
			final Result r = main.dispatch(i);
			if (r instanceof InitializerResult) {
				result.addChild((InitializerResult) r);
			} else if (r instanceof ExpressionResult) {
				ExpressionResult rex = (ExpressionResult) r;
				// TODO: (alex, feb 2018) quite unsure about always doing this array to pointer conversion..
				rex = decayArrayToPointer(rex, loc, node);
				rex = mExprResultTransformer.switchToRValueIfNecessary(rex, loc, node);
				result.addChild(new InitializerResultBuilder().setRootExpressionResult(rex).build());

			} else {
				final String msg = "Unexpected result";
				throw new UnsupportedSyntaxException(loc, msg);
			}
		}
		return result.build();
	}

	public Result visit(final IDispatcher main, final IASTLabelStatement node) {
		final ILocation loc = mLocationFactory.createCLocation(node);
		final ArrayList<Statement> stmt = new ArrayList<>();
		final ArrayList<Declaration> decl = new ArrayList<>();
		// final Map<VariableDeclaration, ILocation> emptyAuxVars = new
		// LinkedHashMap<>(0);
		final List<Overapprox> overappr = new ArrayList<>();
		final String label = node.getName().toString();
		if ("ERROR".equals(label)) {
			final String longDescription =
					"The label \"ERROR\" does not have a special meaning in the translation mode you selected. You might want to change your settings and use the SV-COMP translation mode.";
			mReporter.warn(loc, longDescription);
		}
		stmt.add(new Label(loc, label));
		final Result r = main.dispatch(node.getNestedStatement());
		if (r instanceof ExpressionResult) {
			final ExpressionResult res = (ExpressionResult) r;
			decl.addAll(res.getDeclarations());
			stmt.addAll(res.getStatements());
			overappr.addAll(res.getOverapprs());
			return new ExpressionResult(stmt, res.getLrValue(), decl, Collections.emptySet(), overappr);
		} else if (r instanceof SkipResult) {
			return new ExpressionResult(stmt, null, decl, Collections.emptySet());
		} else { // r instanceof Result ...
			RValue expr = null;
			if (r.getNode() instanceof Statement) {
				stmt.add((Statement) r.getNode());
			} else if (r.getNode() instanceof Declaration) {
				decl.add((Declaration) r.getNode());
			} else if (r.getNode() instanceof Expression) {
				expr = new RValue((Expression) r.getNode(), null);// FIXME ??
			} else if (r.getNode() instanceof Body) {
				// we already have a unique naming for variables! --> unfold
				final Body b = (Body) r.getNode();
				decl.addAll(Arrays.asList(b.getLocalVars()));
				stmt.addAll(Arrays.asList(b.getBlock()));
			} else {
				final String msg = "Unexpected boogie AST node type: " + r.getNode().getClass();
				throw new UnsupportedSyntaxException(loc, msg);
			}
			return new ExpressionResult(stmt, expr, decl, Collections.emptySet());
		}
	}

	public Result visit(final IDispatcher main, final IASTLiteralExpression node) {
		final ILocation loc = mLocationFactory.createCLocation(node);

		switch (node.getKind()) {
		case IASTLiteralExpression.lk_float_constant: {
			final String val = new String(node.getValue());
			final RValue rVal = mExpressionTranslation.translateFloatingLiteral(loc, val);
			assert rVal != null : "result must not be null";
			return new ExpressionResult(rVal);
		}
		case IASTLiteralExpression.lk_char_constant: {

			final CCharacterConstant characterConstant =
					new CCharacterConstant(new String(node.getValue()), mTypeSizes.getSignednessOfChar());
			final Expression literal = mTypeSizes.constructLiteralForIntegerType(loc, characterConstant.getType(),
					characterConstant.getRepresentingValue());
			return new ExpressionResult(new RValue(literal, characterConstant.getType()));
		}
		case IASTLiteralExpression.lk_integer_constant: {
			final String val = new String(node.getValue());
			final RValue rVal = mExpressionTranslation.translateIntegerLiteral(loc, val);
			return new ExpressionResult(rVal);
		}
		case IASTLiteralExpression.lk_string_literal: {
			final CStringLiteral stringLiteral = new CStringLiteral(node.getValue(), mTypeSizes.getSignednessOfChar());
			final RValue rvalue;
			final AuxVarInfo auxvar;
			{
				// subtract two from length for quotes at beginning and end
				final int arrayLength = stringLiteral.getByteValues().size();
				final RValue dimension = new RValue(
						mTypeSizes.constructLiteralForIntegerType(loc,
								mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.valueOf(arrayLength)),
						mExpressionTranslation.getCTypeOfPointerComponents());
				final CArray arrayType = new CArray(dimension, new CPrimitive(CPrimitives.CHAR));
				final CPointer pointerType = new CPointer(new CPrimitive(CPrimitives.CHAR));
				auxvar = mAuxVarInfoBuilder.constructGlobalAuxVarInfo(loc, pointerType, SFO.AUXVAR.STRINGLITERAL);
				rvalue = new RValueForArrays(auxvar.getExp(), arrayType);
			}
			// the declaration of the variable that corresponds to a string literal has to be made globally
			mStaticObjectsHandler.addGlobalVarDeclarationWithoutCDeclaration(auxvar.getVarDec());

			// overapproximate string literals of length STRING_OVERAPPROXIMATION_THRESHOLD or longer
			final boolean writeValues =
					stringLiteral.getByteValues().size() < ExpressionTranslation.STRING_OVERAPPROXIMATION_THRESHOLD;

			final List<Statement> statements =
					mMemoryHandler.writeStringToHeap(main, loc, auxvar.getLhs(), stringLiteral, writeValues, node);
			mStaticObjectsHandler.addStatementsForUltimateInit(statements);

			final List<Overapprox> overapproxList;
			if (writeValues) {
				overapproxList = Collections.emptyList();
			} else {
				final Overapprox overapprox = new Overapprox("large string literal", loc);
				overapproxList = new ArrayList<>();
				overapproxList.add(overapprox);
			}
			return new StringLiteralResult(rvalue, overapproxList, auxvar, stringLiteral, !writeValues);
		}
		case IASTLiteralExpression.lk_false:
			return new ExpressionResult(
					new RValue(ExpressionFactory.createBooleanLiteral(loc, false), new CPrimitive(CPrimitives.INT)));
		case IASTLiteralExpression.lk_true:
			return new ExpressionResult(
					new RValue(ExpressionFactory.createBooleanLiteral(loc, true), new CPrimitive(CPrimitives.INT)));
		default:
			final String msg = "Unknown or unsupported kind of IASTLiteralExpression";
			throw new UnsupportedSyntaxException(loc, msg);
		}
	}

	public Result visit(final IDispatcher main, final IASTNode node) {
		final String msg = "CHandler: Not yet implemented: \"" + node.getRawSignature() + "\" (Type: "
				+ node.getClass().getName() + ")";
		final ILocation loc = mLocationFactory.createCLocation(node);
		throw new UnsupportedSyntaxException(loc, msg);
	}

	public Result visit(final IDispatcher main, final IASTNullStatement node) {
		return new SkipResult();
	}

	public Result visit(final IDispatcher main, final IASTParameterDeclaration node) {
		final TypesResult resType = (TypesResult) main.dispatch(node.getDeclSpecifier());

		mCurrentDeclaredTypes.push(resType);
		final DeclaratorResult declResult = (DeclaratorResult) main.dispatch(node.getDeclarator());
		mCurrentDeclaredTypes.pop();
		return declResult;
	}

	public Result visit(final IDispatcher main, final IASTPointer node) {
		// TODO : implement pointer IASTPointer? When is this required?!
		throw new UnsupportedOperationException("This should have been handled before ...");
	}

	public Result visit(final IDispatcher main, final IASTProblem node) {
		final String msg = "Syntax error in C program: " + node.getMessage();
		final ILocation loc = mLocationFactory.createCLocation(node);
		throw new IncorrectSyntaxException(loc, msg);
	}

	public Result visit(final IDispatcher main, final IASTProblemDeclaration node) {
		final String msg = "Syntax error (declaration problem) in C program: " + node.getProblem().getMessage();
		final ILocation loc = mLocationFactory.createCLocation(node);
		throw new IncorrectSyntaxException(loc, msg);
	}

	public Result visit(final IDispatcher main, final IASTProblemExpression node) {
		final String msg = "Syntax error (expression problem) in C program: " + node.getProblem().getMessage();
		final ILocation loc = mLocationFactory.createCLocation(node);
		throw new IncorrectSyntaxException(loc, msg);
	}

	public Result visit(final IDispatcher main, final IASTProblemStatement node) {
		final String msg = "Syntax error (statement problem) in C program: " + node.getProblem().getMessage();
		final ILocation loc = mLocationFactory.createCLocation(node);
		throw new IncorrectSyntaxException(loc, msg);
	}

	public Result visit(final IDispatcher main, final IASTProblemTypeId node) {
		final String msg = "Syntax error (type ID problem) in C program: " + node.getProblem().getMessage();
		final ILocation loc = mLocationFactory.createCLocation(node);
		throw new IncorrectSyntaxException(loc, msg);
	}

	public Result visit(final IDispatcher main, final IASTReturnStatement node) {
		return mFunctionHandler.handleReturnStatement(main, mMemoryHandler, node);
	}

	/**
	 * Visit the SimpleDeclaration (which may be quite complex in fact..). The return value here may have different
	 * uses:
	 * <li>for global variables and declarations inside of struct definitions, it is a ResultDeclaration (containing the
	 * Boogie Declaration of the variable)
	 * <li>for local variables that have an initializer, a ResultExpression is returned which contains (Boogie)
	 * statements and declarations that make the initialization according to the initializer
	 * <li>for local variables without an initializer, a havoc statement is inserted into the ResultExpression instead
	 * The declarations themselves of the local variables (and f.i. typedefs) are stored in the symbolTable and inserted
	 * into the Boogie code at the next endScope()
	 * <p>
	 * Declarations of static variables are added to mDeclarationsGlobalInBoogie such that they can be declared and
	 * initialized globally.
	 * <p>
	 * Variables/types that are global in Boogie but not in C are stored in the Symboltable to keep the association of
	 * BoogieId and CId.
	 */

	public Result visit(final IDispatcher main, final IASTSimpleDeclaration node) {
		final ILocation loc = mLocationFactory.createCLocation(node);
		if (node.getParent() instanceof IASTTranslationUnit && !isReachable(node)) {
			// Unreachable global declaration.
			return new SkipResult();
		}

		// not sure what it means when the declspecifier is null ..
		if (node.getDeclSpecifier() == null) {
			final String msg = "This statement can be removed!";
			mReporter.warn(loc, msg);
			return new SkipResult();
		}

		// we have an enum declaration

		// if (node.getDeclSpecifier() instanceof IASTEnumerationSpecifier) {
		// TODO 2018-09-02 Matthias: In the past we called here a void method
		// handleEnumDeclaration(main, node) which itself dispatched the
		// IASTEnumerationSpecifier and then added the enumeration constants
		// to the symbol table and the declarations of the enumeration
		// constants to our StaticObjectsHandler. As consequence was that
		// we could not process files in which a just defined enumeration
		// constant is used as a value in the very same declaration.
		// I moved the adding to symbol table and StaticObjectsHandler
		// to the code that handles the IASTEnumerationSpecifier and now
		// the handleEnumDeclaration seems obsolete.
		// I did not carefully check if the new code works with incomplete
		// enum declarations.
		// }

		/*
		 * obtain type information from the DeclSpecifier
		 */
		final Result declSpecifierResult = main.dispatch(node.getDeclSpecifier());
		assert declSpecifierResult instanceof SkipResult || declSpecifierResult instanceof TypesResult;

		if (declSpecifierResult instanceof SkipResult) {
			return declSpecifierResult;
		}

		if (!(declSpecifierResult instanceof TypesResult)) {
			final String msg = "Unknown result type: " + declSpecifierResult.getClass();
			throw new UnsupportedSyntaxException(loc, msg);
		}

		final TypesResult typeResult = (TypesResult) declSpecifierResult;
		// Skip will be overwritten in
		// case of a global or a local
		// initialized variable

		final CStorageClass storageClass = scConstant2StorageClass(node.getDeclSpecifier().getStorageClass());

		mCurrentDeclaredTypes.push(typeResult);
		/**
		 * Christian: C allows several declarations of "similar" types in one go. For instance:
		 * <code>int a, b[2];</code> Here <code>a</code> has type <code>int</code> and <code>b</code> has type
		 * <code>int[]</code>. To solve this, the declaration items are visited one after another.
		 */
		final List<Result> intermediateResults = new ArrayList<>();
		for (final IASTDeclarator d : node.getDeclarators()) {
			final DeclaratorResult declResult = (DeclaratorResult) main.dispatch(d);
			final CDeclaration cDec = declResult.getDeclaration();
			cDec.setStorageClass(storageClass);

			// are we in prerun mode?
			if (mIsPrerun) {
				// all unions should be on heap
				if (CStructOrUnion.isUnion(cDec.getType().getUnderlyingType()) && storageClass != CStorageClass.TYPEDEF) {
					addToVariablesOnHeap(d);
				}
			}

			if (cDec.getType() instanceof CFunction && storageClass != CStorageClass.TYPEDEF) {
				// update functionHandler.procedures instead of symbol table
				mFunctionHandler.handleFunctionDeclarator(main, mLocationFactory.createCLocation(d), mContract, cDec,
						d);
				continue;
			}
			intermediateResults.add(handleIASTDeclarator(main, loc, node, declResult, d, cDec, storageClass));
		}
		mCurrentDeclaredTypes.pop();

		final List<Result> noSkipIntermediateResult =
				intermediateResults.stream().filter(a -> !(a instanceof SkipResult)).collect(Collectors.toList());
		if (noSkipIntermediateResult.isEmpty()) {
			return new SkipResult();
		}
		final Result first = noSkipIntermediateResult.get(0);
		if (noSkipIntermediateResult.size() == 1) {
			return first;
		}
		if (first instanceof ExpressionResult) {
			final ExpressionResultBuilder erb = new ExpressionResultBuilder();
			for (final Result result : noSkipIntermediateResult) {
				final ExpressionResult exprResult = (ExpressionResult) result;
				erb.addAllExceptLrValue(exprResult);
				assert exprResult.getLrValue() == null;
			}
			return erb.build();
		}
		if (first instanceof DeclarationResult) {
			return new DeclarationResult(noSkipIntermediateResult.stream()
					.flatMap(a -> ((DeclarationResult) a).getDeclarations().stream()).collect(Collectors.toList()));
		}
		throw new AssertionError("Unexpected result type: " + first.getClass().getSimpleName());
	}

	/**
	 * Translate a switch statement as described in C99: 6.8.4.2
	 */
	public Result visit(final IDispatcher main, final IASTSwitchStatement node) {
		final ILocation loc = mLocationFactory.createCLocation(node);
		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();

		// dispatch the controlling expression, convert it to int
		final Result switchParam = main.dispatch(node.getControllerExpression());
		ExpressionResult expr = mExprResultTransformer.switchToRValueIfNecessary((ExpressionResult) switchParam, loc,
				node.getControllerExpression());
		// 6.8.4.2-1: "The controlling expression of a switch statement shall have integer type."
		// note that this does not mean that it has "int" type, it may be long or char, for instance
		assert expr.getLrValue().getCType().isIntegerType();
		// 6.8.4.2-5: "The integer promotions are performed on the controlling
		// expression."
		expr = mExpressionTranslation.doIntegerPromotion(loc, expr);

		resultBuilder.addAllExceptLrValue(expr);

		final Expression switchArg = expr.getLrValue().getValue();

		final CPrimitive intType = new CPrimitive(CPrimitives.INT);
		final String breakLabelName = mNameHandler.getGloballyUniqueIdentifier("SWITCH~BREAK~");

		final AuxVarInfo switchAuxvar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, intType,
				new PrimitiveType(loc, BoogieType.TYPE_BOOL, SFO.BOOL), SFO.AUXVAR.SWITCH);

		resultBuilder.addDeclaration(switchAuxvar.getVarDec());
		resultBuilder.addAuxVar(switchAuxvar);

		boolean isFirst = true;
		boolean firstCond = true;
		Expression cond = null;
		ILocation locC = null;

		ArrayList<Statement> ifBlock = new ArrayList<>();
		beginScope();
		for (final IASTNode child : node.getBody().getChildren()) {
			if (isFirst && !(child instanceof IASTCaseStatement || child instanceof IASTDefaultStatement)) {
				// declarations in the beginning of a switch body (i.e. before the first
				// case/default) are used,
				// statements are dropped
				// see example 6.8.4.2-7

				// we need to dispatch the child in order to fill the symbol table with
				// declarations accordingly
				// the result can only contain statements, which we drop.
				main.dispatch(child);

				continue;
			}
			isFirst = false;
			{
				final ExpressionResultBuilder acslResultBuilder = new ExpressionResultBuilder();
				checkForACSL(main, acslResultBuilder, child, null, true);
				ifBlock.addAll(acslResultBuilder.getStatements());
				resultBuilder.addDeclarations(acslResultBuilder.getDeclarations());
			}

			if (child instanceof IASTCaseStatement || child instanceof IASTDefaultStatement) {
				ExpressionResult caseExpression = (ExpressionResult) main.dispatch(child);
				if (locC != null) {
					final IfStatement ifStmt = new IfStatement(locC, switchAuxvar.getExp(),
							ifBlock.toArray(new Statement[ifBlock.size()]), new Statement[0]);
					for (final Overapprox overapprItem : caseExpression.getOverapprs()) {
						overapprItem.annotate(ifStmt);
					}

					if (firstCond) {
						final AssignmentStatement assign = StatementFactory.constructAssignmentStatement(locC,
								new LeftHandSide[] { switchAuxvar.getLhs() }, new Expression[] { cond });
						resultBuilder.addStatement(assign);
						firstCond = false;
					} else {
						final AssignmentStatement assign = StatementFactory.constructAssignmentStatement(locC,
								new LeftHandSide[] { switchAuxvar.getLhs() }, new Expression[] { ExpressionFactory
										.newBinaryExpression(locC, Operator.LOGICOR, switchAuxvar.getExp(), cond) });
						resultBuilder.addStatement(assign);
					}
					resultBuilder.addStatement(ifStmt);
				}

				ifBlock = new ArrayList<>();
				locC = mLocationFactory.createCLocation(child);

				if (child instanceof IASTCaseStatement) {
					// 6.8.4.2-5: "The constant expression in each case label is converted to the
					// promoted type of the controlling expression"
					caseExpression = mExpressionTranslation.convertIntToInt(locC, caseExpression,
							(CPrimitive) expr.getLrValue().getCType());
					cond = ExpressionFactory.newBinaryExpression(locC, Operator.COMPEQ, switchArg,
							caseExpression.getLrValue().getValue());
					resultBuilder.addAllExceptLrValue(caseExpression);
				} else {
					// default statement
					cond = caseExpression.getLrValue().getValue();
				}
			} else {
				final Result r = main.dispatch(child);

				if (r instanceof ExpressionResult) {
					final ExpressionResult res = (ExpressionResult) r;
					resultBuilder.addDeclarations(res.getDeclarations());
					resultBuilder.addAuxVars(res.getAuxVars());
					resultBuilder.addOverapprox(res.getOverapprs());
					for (final Statement s : res.getStatements()) {
						if (s instanceof BreakStatement) {
							ifBlock.add(new GotoStatement(locC, new String[] { breakLabelName }));
						} else {
							ifBlock.add(s);
						}
					}
				}
				if (r.getNode() != null && r.getNode() instanceof Body) {
					// we already have a unique naming for variables! -> unfold
					final Body b = (Body) r.getNode();
					resultBuilder.addDeclarations(Arrays.asList(b.getLocalVars()));
					for (final Statement s : b.getBlock()) {
						if (s instanceof BreakStatement) {
							ifBlock.add(new GotoStatement(locC, new String[] { breakLabelName }));
						} else {
							ifBlock.add(s);
						}
					}
				}
			}
		}
		if (locC != null) {
			assert cond != null;
			final IfStatement ifStmt = new IfStatement(locC, switchAuxvar.getExp(),
					ifBlock.toArray(new Statement[ifBlock.size()]), new Statement[0]);
			for (final Overapprox overapprItem : resultBuilder.getOverappr()) {
				overapprItem.annotate(ifStmt);
			}

			if (firstCond) {
				final AssignmentStatement assign = StatementFactory.constructAssignmentStatement(locC,
						new LeftHandSide[] { switchAuxvar.getLhs() }, new Expression[] { cond });
				resultBuilder.addStatement(assign);
				firstCond = false;
			} else {
				final AssignmentStatement assign = StatementFactory.constructAssignmentStatement(locC,
						new LeftHandSide[] { switchAuxvar.getLhs() }, new Expression[] { ExpressionFactory
								.newBinaryExpression(locC, Operator.LOGICOR, switchAuxvar.getExp(), cond) });
				resultBuilder.addStatement(assign);
			}
			resultBuilder.addStatement(ifStmt);
		}
		checkForACSL(main, resultBuilder, null, node, true);

		resultBuilder.addStatement(new Label(loc, breakLabelName));
		resultBuilder.addStatements(CTranslationUtil.createHavocsForAuxVars(resultBuilder.getAuxVars()));

		// Use body as hook: This is the scope holder for switch statements! (as controller expression is child of the
		// switch itself and may not have scope access.)
		updateStmtsAndDeclsAtScopeEnd(resultBuilder, node.getBody());
		endScope();

		assert resultBuilder.getLrValue() == null;
		return resultBuilder.build();
	}

	public Result visit(final IDispatcher main, final IASTTranslationUnit node) {
		for (final IASTPreprocessorStatement preS : node.getAllPreprocessorStatements()) {
			final Result r = main.dispatch(preS);
			if (!(r instanceof SkipResult)) {
				throw new UnsupportedOperationException("Not yet implemented " + preS.toString());
			}
		}
		final ILocation loc = mLocationFactory.createCLocation(node);
		if (!mIsPrerun) {
			try {
				mAcsl = main.nextACSLStatement();
			} catch (final ParseException e1) {
				final String msg = "Skipped a ACSL node due to: " + e1.getMessage();
				mReporter.unsupportedSyntax(loc, msg);
			}

			final ExpressionResultBuilder acslResultBuilder = new ExpressionResultBuilder();
			// TODO(thrax): Check if decl should be passed as null or not.
			checkForACSL(main, acslResultBuilder, node, null, false);
			mDeclarations.addAll(acslResultBuilder.getDeclarations());
		}

		// delayed processing of IASTFunctionDefinitions and structs
		// This is a workaround. Invariants my use global variables that
		// are not yet declared.
		// Better solution: obtain function signature in a first pass
		// process function body in a second pass
		final List<IASTNode> complexNodes = new ArrayList<>();
		for (final IASTNode child : node.getChildren()) {
			// Ignore included declarations which might cause problems
			if (!child.isPartOfTranslationUnitFile()) {
				continue;
			}
			if (child instanceof IASTSimpleDeclaration) {
				final IASTSimpleDeclaration simpleDecl = (IASTSimpleDeclaration) child;
				if (simpleDecl.getDeclSpecifier() instanceof IASTElaboratedTypeSpecifier
						|| simpleDecl.getDeclSpecifier() instanceof ICASTCompositeTypeSpecifier
						|| simpleDecl.getDeclarators().length > 0
								&& simpleDecl.getDeclarators()[0] instanceof CASTFunctionDeclarator
						|| simpleDecl.getDeclSpecifier() instanceof IASTNamedTypeSpecifier) {
					complexNodes.add(child);
				} else {
					processTUchild(main, mDeclarations, child);
				}
			} else if (child instanceof IASTFunctionDefinition) {
				complexNodes.add(child);
			} else {
				processTUchild(main, mDeclarations, child);
			}
		}
		for (final IASTNode funcDef : complexNodes) {
			processTUchild(main, mDeclarations, funcDef);
		}

		// TODO(thrax): Check if decl should be passed as null.
		final ExpressionResultBuilder acslResultBuilder = new ExpressionResultBuilder();
		// checkForACSL(main, null, decl, node, null, false);
		checkForACSL(main, acslResultBuilder, node, null, false);
		mDeclarations.addAll(acslResultBuilder.getDeclarations());

		// The declarations (which are needed for the caller) are handled as a member as they
		// do not consist of a Boogie node.
		// So as a workaround null is returned here
		return null;
	}

	public Result visit(final IDispatcher main, final IASTTypeIdExpression node) {
		final ILocation loc = mLocationFactory.createCLocation(node);
		switch (node.getOperator()) {
		case IASTTypeIdExpression.op_sizeof: {
			final TypesResult rt = (TypesResult) main.dispatch(node.getTypeId().getDeclSpecifier());
			mCurrentDeclaredTypes.push(rt);
			// main.dispatch(node.getTypeId().getAbstractDeclarator());
			final DeclaratorResult dr = (DeclaratorResult) main.dispatch(node.getTypeId().getAbstractDeclarator());
			mCurrentDeclaredTypes.pop();
			// TypesResult checked = checkForPointer(main,
			// node.getTypeId().getAbstractDeclarator().getPointerOperators(),
			// rt, false);

			return new ExpressionResult(
					new RValue(mMemoryHandler.calculateSizeOf(loc, dr.getDeclaration().getType(), node),
							new CPrimitive(CPrimitives.INT)));
		}
		case IASTTypeIdExpression.op_typeof: {
			final TypesResult rt = (TypesResult) main.dispatch(node.getTypeId().getDeclSpecifier());

			mCurrentDeclaredTypes.push(rt);
			final DeclaratorResult dr = (DeclaratorResult) main.dispatch(node.getTypeId().getAbstractDeclarator());
			mCurrentDeclaredTypes.pop();

			return dr;
		}
		default:
			break;
		}
		final String msg = "Unsupported boogie AST node type: " + node.getClass();
		throw new UnsupportedSyntaxException(loc, msg);
	}

	public Result visit(final IDispatcher main, final IASTUnaryExpression node) {
		final ILocation loc = mLocationFactory.createCLocation(node);
		final Result result = main.dispatch(node.getOperand());
		final ExpressionResult operand = CTranslationUtil
				.convertExpressionListToExpressionResultIfNecessary(mExprResultTransformer, loc, result, node);

		switch (node.getOperator()) {
		case IASTUnaryExpression.op_minus:
		case IASTUnaryExpression.op_not:
		case IASTUnaryExpression.op_plus:
		case IASTUnaryExpression.op_tilde: {
			final ExpressionResult rop = mExprResultTransformer.switchToRValueIfNecessary(operand, loc, node);
			return handleUnaryArithmeticOperators(loc, node.getOperator(), rop, node);
		}
		case IASTUnaryExpression.op_postFixIncr:
		case IASTUnaryExpression.op_postFixDecr: {
			return handlePostfixIncrementAndDecrement(loc, node.getOperator(), operand, node);
		}
		case IASTUnaryExpression.op_prefixDecr:
		case IASTUnaryExpression.op_prefixIncr: {
			return handlePrefixIncrementAndDecrement(node.getOperator(), loc, operand, node);
		}
		case IASTUnaryExpression.op_bracketedPrimary:
			return operand;
		case IASTUnaryExpression.op_sizeof:
			final CType operandType = operand.getLrValue().getCType().getUnderlyingType();
			return new ExpressionResult(
					new RValue(mMemoryHandler.calculateSizeOf(loc, operandType, node), new CPrimitive(CPrimitives.INT)),
					Collections.emptySet());
		case IASTUnaryExpression.op_star: {
			return handleIndirectionOperator(operand, loc, node);
		}
		case IASTUnaryExpression.op_amper: {
			return handleAddressOfOperator(operand, loc, node);
		}
		case IASTUnaryExpression.op_alignOf:
		default:
			final String msg = "Unknown or unsupported unary operation: " + node.getOperator();
			throw new UnsupportedSyntaxException(loc, msg);
		}
	}

	public Result visit(final IDispatcher main, final IASTWhileStatement node) {
		final ExpressionResult condResult = (ExpressionResult) main.dispatch(node.getCondition());
		final String loopLabel = mNameHandler.getGloballyUniqueIdentifier(SFO.LOOPLABEL);
		mInnerMostLoopLabel.push(loopLabel);
		final Result bodyResult = main.dispatch(node.getBody());
		mInnerMostLoopLabel.pop();
		final LoopInvariantSpecification witnessInvariant = main.fetchInvariantAtLoop(node);
		return handleLoops(main, node, bodyResult, condResult, loopLabel, witnessInvariant);
	}

	public Result visit(final IDispatcher main, final IGNUASTCompoundStatementExpression node) {
		return main.dispatch(node.getCompoundStatement());
	}

	/**
	 * central methods for beginning a scope in all necessary ScopedThings (f.i. symbolTable,..)
	 */

	public void beginScope() {
		mTypeHandler.beginScope();
		mMemoryHandler.beginScope();
	}

	/**
	 * central methods for ending a scope in all necessary ScopedThings (f.i. symbolTable,..)
	 */

	public void endScope() {
		mTypeHandler.endScope();
		mMemoryHandler.endScope();
	}

	public void clearContract() {
		mContract.clear();
	}

	public boolean isHeapVar(final String boogieId) {
		return mBoogieIdsOfHeapVars.contains(boogieId);
	}

	/**
	 * @param bId
	 *            Boogie ID
	 */
	public void addBoogieIdsOfHeapVars(final String bId) {
		mBoogieIdsOfHeapVars.add(bId);
	}

	/**
	 * Checks resType, whether it needs some special treatment for pointers, according the value in pointerOps. Also in
	 * case the flag putOnHeap is set -- which is the case for our special HeapVariables.
	 *
	 * @param pointerOps
	 *            the pointer operator array.
	 * @param resType
	 *            the type to check.
	 * @param putOnHeap
	 *            indicates whether we are dealing with a HeapVar
	 * @return the checked ResultTypes object.
	 */
	public TypesResult checkForPointer(final IASTPointerOperator[] pointerOps, final TypesResult resType,
			final boolean putOnHeap) {
		if (putOnHeap || pointerOps.length != 0) {
			// TODO : not sure, if this is enough!
			// There could be multiple PointerOperators (i.e.
			// IASTPointer) - what does that mean for the translation?
			final ASTType t = mTypeHandler.constructPointerType(null);
			final CType cvar = new CPointer(resType.getCType());
			return new TypesResult(t, resType.isConst(), resType.isVoid(), cvar);
		}
		return resType;
	}

	/**
	 * Convert an LrValue of array type to an (otherwise equivalent) RValue of pointer type.
	 * <p>
	 * Background: Array expressions can be used in place of pointer expressions in C. (An array may "decay" to a
	 * pointer in C standard terminology.) E.g. when an array is assigned to a pointer variable.
	 *
	 *
	 *
	 * @param rightLrVal
	 * @return
	 */
	public RValue decayArrayLrValToPointer(final ILocation loc, final LRValue rightLrVal, final IASTNode hook) {
		assert rightLrVal.getCType().getUnderlyingType() instanceof CArray;

		final Expression newValue;
		if (mIsPrerun) {
			final Expression oldValue;
			if (rightLrVal instanceof HeapLValue) {
				/*
				 * Can happen for example if we have an array in a struct and now are dealing with a pointer to that
				 * struct. (see for example examples/CToBoogieTranslation/regression/pointerArithOnArrays.c)
				 */
				oldValue = ((HeapLValue) rightLrVal).getAddress();
			} else {
				oldValue = rightLrVal.getValue();
			}
			// circumvents Boogie type checking during preprocessing
			newValue = ExpressionFactory.replaceBoogieType(oldValue, mTypeHandler.getBoogiePointerType());
			moveArrayAndStructIdsOnHeap(loc, rightLrVal.getUnderlyingType(), oldValue, Collections.emptySet(), hook);
		} else {
			if (rightLrVal instanceof RValueForArrays) {
				newValue = rightLrVal.getValue();
			} else {
				newValue = ((HeapLValue) rightLrVal).getAddress();
			}
		}
		final CType newType = new CPointer(((CArray) rightLrVal.getCType().getUnderlyingType()).getValueType());
		return new RValue(newValue, newType);
	}

	public static CStorageClass scConstant2StorageClass(final int storageClass) {
		switch (storageClass) {
		case IASTDeclSpecifier.sc_auto:
			return CStorageClass.AUTO;
		case IASTDeclSpecifier.sc_extern:
			return CStorageClass.EXTERN;
		case IASTDeclSpecifier.sc_mutable:
			return CStorageClass.MUTABLE;
		case IASTDeclSpecifier.sc_register:
			return CStorageClass.REGISTER;
		case IASTDeclSpecifier.sc_static:
			return CStorageClass.STATIC;
		case IASTDeclSpecifier.sc_typedef:
			return CStorageClass.TYPEDEF;
		case IASTDeclSpecifier.sc_unspecified:
			return CStorageClass.UNSPECIFIED;
		default:
			throw new AssertionError("should not happen");
		}
	}

	/**
	 *
	 * @param loc
	 * @param leftHandSide
	 *            value of the left hand side that will be assigned to
	 * @param leftHandSideOtherUnionFields
	 *            information about union fields that need to be havocced in our struct representation of an off-heap
	 *            union
	 * @param rhsConverted
	 *            contains:
	 *            <li>the value (LRValue) of the right hand side of the assignment
	 *            <li>side effects (statements, declarations) etc. that are needed to prepare the value of the right
	 *            hand side of the assignment
	 *            <li>side effects that are needed to prepare the value of the left hand side of the assignment
	 * @return
	 */
	public ExpressionResult makeAssignment(final ILocation loc, final LRValue leftHandSide,
			final Collection<ExpressionResult> leftHandSideOtherUnionFields, final ExpressionResult rhs,
			final IASTNode hook) {

		// do implicit cast -- assume the types are compatible
		final ExpressionResult rhsConverted = mExprResultTransformer.convert(loc, rhs, leftHandSide.getCType());
		final RValue rightHandSideValueWithConversionsApplied = (RValue) rhsConverted.getLrValue();

		// for wraparound --> and avoiding it for ints that store pointers
		// updates the value in the symbol table accordingly
		// TODO: this is really ugly, do we still need this??
		if (rightHandSideValueWithConversionsApplied.isIntFromPointer()) {
			if (leftHandSide instanceof HeapLValue) {
				final Expression address = ((HeapLValue) leftHandSide).getAddress();
				if (address instanceof IdentifierExpression) {
					final String lId =
							((IdentifierExpression) ((HeapLValue) leftHandSide).getAddress()).getIdentifier();
					markAsIntFromPointer(loc, lId, hook);
				} else {
					// TODO
				}
			} else if (leftHandSide instanceof LocalLValue) {
				String lId = null;
				final LeftHandSide value = ((LocalLValue) leftHandSide).getLhs();
				if (value instanceof VariableLHS) {
					lId = ((VariableLHS) value).getIdentifier();
					markAsIntFromPointer(loc, lId, hook);
				} else {
					// TODO
				}
			}
			throw new AssertionError("Presumed that IntFromPointer workaound is not used any more.");
		}

		// add the assignment statement
		if (leftHandSide instanceof HeapLValue) {
			// left hand side of assignment is on heap

			final ExpressionResultBuilder builder = new ExpressionResultBuilder().addAllExceptLrValue(rhsConverted);

			// construct and add a statement that
			final HeapLValue hlv = (HeapLValue) leftHandSide;

			Expression rhsWithBitfieldTreatment;
			if (hlv.getBitfieldInformation() != null) {
				final int bitfieldWidth = hlv.getBitfieldInformation().getNumberOfBits();
				rhsWithBitfieldTreatment =
						mExpressionTranslation.eraseBits(loc, rightHandSideValueWithConversionsApplied.getValue(),
								(CPrimitive) hlv.getCType().getUnderlyingType(), bitfieldWidth, hook);
			} else {
				rhsWithBitfieldTreatment = rightHandSideValueWithConversionsApplied.getValue();
			}
			builder.addStatements(mMemoryHandler.getWriteCall(loc, hlv, rhsWithBitfieldTreatment,
					rightHandSideValueWithConversionsApplied.getCType(), false, hook));

			// the value of an assignment statement expression is the right hand side of the assignment
			builder.setLrValue(rightHandSideValueWithConversionsApplied);

			return builder.build();
		} else if (leftHandSide instanceof LocalLValue) {
			// left hand side of assignment is off heap

			final ExpressionResultBuilder builder = new ExpressionResultBuilder();
			/*
			 * take over everything but neighbour union fields -- those will be given to assignorHavocUnionNeighbours as
			 * an extra parameter
			 */
			builder.addStatements(rhsConverted.getStatements());
			builder.addDeclarations(rhsConverted.getDeclarations());
			builder.addOverapprox(rhsConverted.getOverapprs());
			builder.addAuxVars(rhsConverted.getAuxVars());

			final LocalLValue lValue = (LocalLValue) leftHandSide;
			builder.setLrValue(lValue);

			Expression rhsWithBitfieldTreatment;
			if (lValue.getBitfieldInformation() != null) {
				final int bitfieldWidth = lValue.getBitfieldInformation().getNumberOfBits();
				rhsWithBitfieldTreatment =
						mExpressionTranslation.eraseBits(loc, rightHandSideValueWithConversionsApplied.getValue(),
								(CPrimitive) lValue.getCType().getUnderlyingType(), bitfieldWidth, hook);
			} else {
				rhsWithBitfieldTreatment = rightHandSideValueWithConversionsApplied.getValue();
			}
			final AssignmentStatement assignStmt = StatementFactory.constructAssignmentStatement(loc,
					new LeftHandSide[] { lValue.getLhs() }, new Expression[] { rhsWithBitfieldTreatment });

			builder.addStatement(assignStmt);

			for (final Overapprox oa : rhsConverted.getOverapprs()) {
				for (final Statement stm : builder.getStatements()) {
					oa.annotate(stm);
				}
			}

			final ExpressionResultBuilder builderWithUnionFieldAndNeighboursUpdated = assignOrHavocUnionNeighbours(loc,
					(RValue) rhsConverted.getLrValue(), rhsConverted.getNeighbourUnionFields(),
					rightHandSideValueWithConversionsApplied, builder, hook);
			return builderWithUnionFieldAndNeighboursUpdated.build();
		} else {
			throw new AssertionError("Type error: trying to assign to an RValue in Statement" + loc.toString());
		}
	}

	/**
	 * At the end of a scope, typically a C compound statement, we need to insert some mallocs and frees surrounding the
	 * stmt block, and we need to insert all the declarations that are needed for that block, according to the symbol
	 * table. (at the dispatch of a simple declaration, the declarations are stored in the symbol table)
	 *
	 * Updates the given ExpressionResultBuilder in place. Adds some declarations and resets the statements. Based on
	 * information in the symbol table concerning the scope that is to be closed.
	 */
	public void updateStmtsAndDeclsAtScopeEnd(final ExpressionResultBuilder exprResultBuilder, final IASTNode hook) {
		exprResultBuilder.resetStatements(mMemoryHandler.insertMallocs(exprResultBuilder.getStatements(), hook));
		for (final SymbolTableValue stv : mSymbolTable.getInnermostCScopeValues(hook)) {
			// there may be a null declaration in case of foo(void) -- therefore we need to
			// check the second conjunct
			// (case where this is called from FunctionHandler.handleFunctionDefinition)
			if (!stv.isBoogieGlobalVar() && stv.getBoogieDecl() != null) {
				exprResultBuilder.addDeclaration(stv.getBoogieDecl());
			}
		}
	}

	/**
	 * If the {@link CType} of is a {@link CArray}, we will return a new {@link ExpressionResult} in which the
	 * representation was switched from array to pointer. Otherwise this object is returned (without any modifications).
	 *
	 * Triggers that the array is moved on heap, if necessary.
	 *
	 * (this can be used for example for function parameters, when an array is passed by reference (which is the
	 * standard case).)
	 *
	 */
	public ExpressionResult decayArrayToPointer(final ExpressionResult result, final ILocation loc,
			final IASTNode hook) {
		if (result.getLrValue().getCType().getUnderlyingType() instanceof CArray) {
			final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();
			resultBuilder.addAllExceptLrValue(result);
			resultBuilder.setLrValue(decayArrayLrValToPointer(loc, result.getLrValue(), hook));
			return resultBuilder.build();
		}
		return result;
	}

	/**
	 * @return true iff this is called while in prerun mode, false otherwise
	 */
	public void moveArrayAndStructIdsOnHeap(final ILocation loc, final CType underlyingType, final Expression expr,
			final Set<AuxVarInfo> auxVars, final IASTNode hook) {
		if (!mIsPrerun) {
			if (underlyingType instanceof CArray) {
				throw new AssertionError("on-heap/off-heap bug: array has to be on-heap");
			}
			return;
		}
		final BoogieIdExtractor bie = new BoogieIdExtractor();
		bie.processExpression(expr);
		for (final String id : bie.getIds()) {
			final String cid = mSymbolTable.getCIdForBoogieId(id);
			if (cid == null) {
				// expression does not have a corresponding c identifier --> nothing to move on heap
				continue;
			}
			final SymbolTableValue value = mSymbolTable.findCSymbol(hook, cid);
			final CType type = value.getCType().getUnderlyingType();
			if (type instanceof CArray || type instanceof CStructOrUnion) {
				addToVariablesOnHeap(value.getDeclarationNode());
			}
		}
	}

	private boolean isReachable(final IASTDeclaration node) {
		return mReachableDeclarations == null || mReachableDeclarations.contains(node);
	}

	private void checkUnsupportedPointerCast(final ILocation loc, final CType newCType, final ExpressionResult expr) {
		if (!POINTER_CAST_IS_UNSUPPORTED_SYNTAX) {
			return;
		}
		if (!(newCType instanceof CPointer) || !(expr.getLrValue().getCType() instanceof CPointer)) {
			return;
		}
		final CType newPointsToType = ((CPointer) newCType).getPointsToType();
		final CType exprPointsToType = ((CPointer) expr.getLrValue().getCType()).getPointsToType();
		if (newPointsToType instanceof CPrimitive && exprPointsToType instanceof CPrimitive) {
			if (((CPrimitive) newPointsToType).getGeneralType() == CPrimitiveCategory.INTTYPE
					&& ((CPrimitive) exprPointsToType).getGeneralType() == CPrimitiveCategory.INTTYPE) {
				if (mTypeSizes.isUnsigned((CPrimitive) newPointsToType)
						&& !mTypeSizes.isUnsigned((CPrimitive) exprPointsToType)
						|| !(mTypeSizes.isUnsigned((CPrimitive) newPointsToType)
								&& mTypeSizes.isUnsigned((CPrimitive) exprPointsToType))) {
					throw new UnsupportedSyntaxException(loc,
							"unsupported cast: " + exprPointsToType + " pointer  to " + newPointsToType + " pointer");
				}

			} else if (((CPrimitive) newPointsToType).getGeneralType() == CPrimitiveCategory.VOID
					&& ((CPrimitive) exprPointsToType).getGeneralType() == CPrimitiveCategory.INTTYPE
					|| ((CPrimitive) newPointsToType).getGeneralType() == CPrimitiveCategory.INTTYPE
							&& ((CPrimitive) exprPointsToType).getGeneralType() == CPrimitiveCategory.VOID) {
				throw new UnsupportedSyntaxException(loc,
						"unsupported cast: " + exprPointsToType + " pointer  to " + newPointsToType + " pointer");
			}
		}
	}

	private Result handleIASTDeclarator(final IDispatcher main, final ILocation loc, final IASTSimpleDeclaration node,
			final DeclaratorResult declResult, final IASTDeclarator hook, final CDeclaration cDec,
			final CStorageClass storageClass) {

		// if the same variable is declared multiple times (within the same scope), we
		// only keep one declaration if one of them has an initializer, we keep that one.
		// if we are inside a struct declaration however, this does not apply, we
		// proceed as normal, as the result is needed to build the struct type

		final boolean isInsideStructDeclaration = mSymbolTable.isInsideStructDeclaration(hook);

		if (!isInsideStructDeclaration) {
			final SymbolTableValue stv = mSymbolTable.findCSymbolInInnermostScope(hook, cDec.getName());
			if (stv != null && (!stv.getCDecl().hasInitializer() || cDec.hasInitializer())
					&& mProcedureManager.isGlobalScope()) {
				// Keep the last STV with an initializer
				mStaticObjectsHandler.removeDeclaration(mSymbolTable.findCSymbol(hook, cDec.getName()).getBoogieDecl());
			}
		}

		final boolean onHeap = cDec.isOnHeap();
		final String bId = mNameHandler.getUniqueIdentifier(node, cDec.getName(), mSymbolTable.getCScopeId(hook),
				onHeap, cDec.getType());
		if (onHeap) {
			addBoogieIdsOfHeapVars(bId);
		}

		final DeclarationInformation dummyDeclInfo = DeclarationInformation.DECLARATIONINFO_GLOBAL;

		// this is only to have a minimal symbolTableEntry (containing boogieID) for translation of the initializer
		mSymbolTable.storeCSymbol(hook, cDec.getName(),
				new SymbolTableValue(bId, null, cDec, dummyDeclInfo, hook, false));
		final InitializerResult initializer = translateInitializer(main, cDec);
		cDec.setInitializerResult(initializer);

		final ASTType translatedType;
		if (onHeap) {
			translatedType = mTypeHandler.constructPointerType(loc);
		} else {
			translatedType = mTypeHandler.cType2AstType(loc, cDec.getType());
		}

		final DeclarationInformation declarationInformation;
		final Declaration boogieDec;
		final Result result;
		if (storageClass == CStorageClass.TYPEDEF) {
			boogieDec = new TypeDeclaration(loc, new Attribute[0], false, bId, new String[0], translatedType);

			final BoogieType boogieType = mTypeHandler.getBoogieTypeForCType(cDec.getType());

			mTypeHandler.addDefinedType(bId, new TypesResult(new NamedType(loc, boogieType, cDec.getName(), null),
					false, false, cDec.getType()));
			if (cDec.getType().getUnderlyingType().isIncomplete() && !cDec.getType().getUnderlyingType().isVoidType()) {
				final String identifier;
				if (cDec.getType().getUnderlyingType() instanceof CStructOrUnion) {
					identifier = ((CStructOrUnion) cDec.getType().getUnderlyingType()).getName();
				} else if (cDec.getType().getUnderlyingType() instanceof CEnum) {
					identifier = (((CEnum) cDec.getType().getUnderlyingType()).getName());
				} else {
					throw new AssertionError("missing support for global incomplete " + cDec.getType().getUnderlyingType());
				}
				mTypeHandler.registerNamedIncompleteType(identifier, cDec.getName());
			}
			// TODO: add a sizeof-constant for the type??
			declarationInformation = DeclarationInformation.DECLARATIONINFO_GLOBAL;
			mStaticObjectsHandler.addGlobalTypeDeclaration((TypeDeclaration) boogieDec, cDec);
			result = new SkipResult();
		} else if (storageClass == CStorageClass.STATIC && !mProcedureManager.isGlobalScope()) {
			// we have a local static variable -> special treatment
			// global static variables are treated like normal global variables..
			boogieDec = new VariableDeclaration(loc, new Attribute[0],
					new VarList[] { new VarList(loc, new String[] { bId }, translatedType) });
			declarationInformation = DeclarationInformation.DECLARATIONINFO_GLOBAL;
			mStaticObjectsHandler.addGlobalVariableDeclaration((VariableDeclaration) boogieDec, cDec);
			result = new SkipResult();
		} else {
			if (mProcedureManager.isGlobalScope()) {
				declarationInformation = DeclarationInformation.DECLARATIONINFO_GLOBAL;
			} else {
				declarationInformation =
						new DeclarationInformation(StorageClass.LOCAL, mProcedureManager.getCurrentProcedureID());
			}
			final BoogieType boogieType =
					mTypeHandler.getBoogieTypeForBoogieASTType(mTypeHandler.cType2AstType(loc, cDec.getType()));

			/**
			 * For Variable length arrays we have a "non-real" initializer which just initializes the aux var for the
			 * array's size. We do not want to treat this like other initializers (call initVar and so).
			 */
			final boolean hasRealInitializer =
					cDec.hasInitializer() && (!(cDec.getType() instanceof CArray) || cDec.getInitializer() != null);

			if (!hasRealInitializer && !mProcedureManager.isGlobalScope() && !isInsideStructDeclaration) {
				// in case of a local variable declaration without an
				// initializer, we need to insert a
				// havoc statement (because otherwise the variable is
				// always the same within a loop which
				// may lead to unsoundness)
				// ..except if OnHeap. Then it is malloced instead.
				// (--> this is done below this ite-branching by
				// memoryHandler.addVariableToBeMallocedAndFreed(...))

				final ExpressionResultBuilder erb = new ExpressionResultBuilder();

				final VariableLHS lhs =
						ExpressionFactory.constructVariableLHS(loc, boogieType, bId, declarationInformation);

				if (cDec.hasInitializer()) {
					// must be a non-real initializer for variable length array size
					// --> need to pass this on
					// TODO: double check this
					erb.addAllExceptLrValue(cDec.getInitializer().getRootExpressionResult());
				}

				// no initializer --> essentially needs to be havoced f.i. in each loop iteration
				if (!onHeap) {
					erb.addStatement(new HavocStatement(loc, new VariableLHS[] { lhs }));
				} else {
					final LocalLValue llVal = new LocalLValue(lhs, cDec.getType(), null);
					// old solution: havoc via an auxvar, new solution (below):
					// just malloc at the right place (much shorter for arrays and structs..)
					erb.addStatement(mMemoryHandler.getMallocCall(llVal, loc, node));
					mMemoryHandler.addVariableToBeFreed(
							new LocalLValueILocationPair(llVal, LocationFactory.createIgnoreLocation(loc)));
				}
				result = erb.build();
			} else if (hasRealInitializer && !mProcedureManager.isGlobalScope() && !isInsideStructDeclaration) {
				// in case of a local variable declaration with an initializer, the statements
				// and delcs necessary for the initialization are the result
				final VariableLHS lhs =
						ExpressionFactory.constructVariableLHS(loc, boogieType, bId, declarationInformation);
				final ExpressionResultBuilder erb = new ExpressionResultBuilder();
				final ExpressionResult initRex =
						mInitHandler.initialize(loc, lhs, cDec.getType(), cDec.getInitializer(), hook);

				if (onHeap) {
					final LocalLValue llVal = new LocalLValue(lhs, cDec.getType(), null);
					mMemoryHandler.addVariableToBeFreed(new LocalLValueILocationPair(llVal, loc));
					erb.addStatement(mMemoryHandler.getMallocCall(llVal, loc, node));
				}
				erb.addAllExceptLrValueAndHavocAux(initRex);
				result = erb.build();
			} else {
				// in case of global variables, the result is the declaration, initialization is
				// done in the postProcessor in case this simpleDeclaration is part of a struct
				// definition, we also need the Declarations as a result
				result = new DeclarationResult(cDec);
			}
			assert translatedType != null : "Variable lists need to have a type";
			boogieDec = new VariableDeclaration(loc, new Attribute[0],
					new VarList[] { new VarList(loc, new String[] { bId }, translatedType) });
		}

		// reset the symbol table value with its final contents
		// TODO: Unnamed struct fields have cDec.getName() == "" ; is this supposed to happen?
		mSymbolTable.storeCSymbol(hook, cDec.getName(),
				new SymbolTableValue(bId, boogieDec, cDec, declarationInformation, hook, false));
		return result;
	}

	/**
	 * Triggers the translation of the untranslated initializer from the CAST into a ResultDeclaration that we work
	 * with. (Earlier this was done in visit IASTDeclarator, i.e. where the declarator was dispatched, but this is too
	 * early when we have something like struct list myList = { &myList}, because we need to have some symbolTable entry
	 * for translating this initializer, see visit ISimpleDeclaraton for this, too.)
	 *
	 */
	private static InitializerResult translateInitializer(final IDispatcher main, final CDeclaration cDec) {
		final IASTInitializer init = cDec.getIASTInitializer();
		if (init == null) {
			return null;
		}
		final Result res = main.dispatch(init);

		if (res instanceof InitializerResult) {
			return (InitializerResult) res;
		} else if (res instanceof ExpressionResult) {
			return new InitializerResultBuilder().setRootExpressionResult((ExpressionResult) res).build();
		} else {
			throw new AssertionError(
					"Expected either InitializerResult or ExpressionResult, but got " + res.getClass());
		}
	}

	private static int computeSizeOfInitializer(final IASTEqualsInitializer equalsInitializer) {
		final int intSizeFactor;
		if (equalsInitializer.getInitializerClause() instanceof IASTInitializerList) {
			final IASTInitializerList initList = (IASTInitializerList) equalsInitializer.getInitializerClause();
			intSizeFactor = initList.getSize();
			return intSizeFactor;
		} else if (equalsInitializer.getInitializerClause() instanceof CASTLiteralExpression
				&& ((CASTLiteralExpression) equalsInitializer.getInitializerClause())
						.getKind() == IASTLiteralExpression.lk_string_literal) {
			final CASTLiteralExpression lit = (CASTLiteralExpression) equalsInitializer.getInitializerClause();
			/*
			 * subtracting -1 because lit.getValue includes the quotation marks (-2) and we will add a termination
			 * character (+1), for example the string literals "bla" will give us length 7, as C will store it as 'b'
			 * 'l' 'a' '\0'
			 */
			return lit.getValue().length - 1;
		} else {
			throw new AssertionError("attempting to compute size of an unforseen kind of initializer expression");
		}
	}

	private RValue convertToPointerRValue(final LRValue lrValue, final BoogieType pointerType) {
		assert mIsPrerun;
		if (lrValue instanceof HeapLValue) {
			throw new AssertionError("does this occur??");
		}
		final Expression oldValue = lrValue.getValue();
		final Expression convertedValue = ExpressionFactory.replaceBoogieType(oldValue, pointerType);

		return new RValue(convertedValue, new CPointer(lrValue.getCType()));
	}

	/**
	 * Whether or not a new Scope should be started for this compound statement.
	 *
	 * @param env
	 *            the environment in which the CompoundStatement is.
	 * @return whether to open a new scope in the symbol table or not.
	 */
	private static boolean isNewScopeRequired(final IASTNode env) {
		return !(env instanceof IASTForStatement) && !(env instanceof IASTFunctionDefinition);
	}

	private void moveIdOnHeap(final ILocation loc, final IdentifierExpression idExpr, final IASTNode hook) {
		final String id = idExpr.getIdentifier();
		final String cid = mSymbolTable.getCIdForBoogieId(id);
		final SymbolTableValue value = mSymbolTable.findCSymbol(hook, cid);
		addToVariablesOnHeap(value.getDeclarationNode());
	}

	private void addToVariablesOnHeap(final IASTNode var) {
		mVariablesOnHeap.add(var);
	}

	/**
	 * For symbols that may or may not be global (essentially variable declarations), we need to apply multiparse
	 * renaming if they are in the global scope.
	 *
	 * This method checks whether they are global and renames the variable appropriately.
	 *
	 */
	private String getNonFunctionDeclaratorName(final IASTDeclarator node) {
		if (isGlobal(node)) {
			return mSymbolTable.applyMultiparseRenaming(node.getContainingFilename(), node.getName().toString());
		}
		return node.getName().toString();
	}

	private static boolean isGlobal(final IASTDeclarator node) {
		assert node != null;
		if (node instanceof IASTFunctionDeclarator) {
			return true;
		}
		if (node instanceof IASTFieldDeclarator) {
			// fields in a struct are never global in this sense; the struct may be global
			return false;
		}
		IASTNode parent = node.getParent();
		while (parent != null) {
			if (parent instanceof IASTFunctionDeclarator) {
				// its a declarator inside of a function, it must be local
				return false;
			}
			if (parent instanceof ICASTCompositeTypeSpecifier) {
				// it is a declarator inside of another type, it must be local
				return false;
			}
			if (parent instanceof IASTTranslationUnit) {
				return true;
			}
			parent = parent.getParent();
		}
		return true;
	}

	/**
	 * Check if two pointers have the same base component (i.e. if both point to the same array object). Depending on
	 * the preferences of this plugin we
	 * <ul>
	 * <li>assert that both have the same base component,
	 * <li>assume that both have the same base component, or
	 * <li>add nothing.
	 * </ul>
	 *
	 * @param leftPtr
	 *            Boogie {@link Expression} that represents the left pointer.
	 * @param rightPtr
	 *            Boogie {@link Expression} that represents the right pointer.
	 * @param erb
	 *            {@link ExpressionResultBuilder} to which the additional statements are added.
	 */
	private ExpressionResultBuilder addBaseEqualityCheck(final ILocation loc, final Expression leftPtr,
			final Expression rightPtr, final ExpressionResultBuilder erb) {

		if (mSettings.getPointerSubtractionAndComparisonValidityCheckMode() == PointerCheckMode.IGNORE) {
			// do not check anything
			return erb;
		}
		final Expression baseEquality = constructPointerComponentRelation(loc, IASTBinaryExpression.op_equals, leftPtr,
				rightPtr, SFO.POINTER_BASE);
		switch (mSettings.getPointerSubtractionAndComparisonValidityCheckMode()) {
		case ASSERTandASSUME:
			final Statement assertStm = new AssertStatement(loc, baseEquality);
			final Check chk = new Check(Spec.ILLEGAL_POINTER_ARITHMETIC);
			chk.annotate(assertStm);
			erb.addStatement(assertStm);
			return erb;
		case ASSUME:
			final Statement assumeStm = new AssumeStatement(loc, baseEquality);
			erb.addStatement(assumeStm);
			return erb;
		case IGNORE:
			throw new AssertionError("case handled before");
		default:
			throw new AssertionError("unknown value");
		}
	}

	/**
	 * Add to divisorExpRes a check if divisior is zero.
	 */
	private ExpressionResult addDivisionByZeroCheck(final ILocation loc, final ExpressionResult divisorExpRes) {
		final Expression divisor = divisorExpRes.getLrValue().getValue();
		final CPrimitive divisorType = (CPrimitive) divisorExpRes.getLrValue().getCType();

		final PointerCheckMode checkMode;
		if (divisorType.isIntegerType()) {
			checkMode = mSettings.getDivisionByZeroOfIntegerTypes();
		} else if (divisorType.isFloatingType()) {
			checkMode = mSettings.getDivisionByZeroOfFloatingTypes();
		} else {
			throw new UnsupportedOperationException("cannot check division by zero for type " + divisorType);
		}

		if (checkMode == PointerCheckMode.IGNORE) {
			return divisorExpRes;
		}

		final Expression divisorNotZero;
		if (divisorType.isIntegerType()) {
			final Expression zero = mTypeSizes.constructLiteralForIntegerType(loc, divisorType, BigInteger.ZERO);
			divisorNotZero = mExpressionTranslation.constructBinaryEqualityExpression(loc,
					IASTBinaryExpression.op_notequals, divisor, divisorType, zero, divisorType);
		} else if (divisorType.isFloatingType()) {
			final Expression zero =
					mExpressionTranslation.constructLiteralForFloatingType(loc, divisorType, BigDecimal.ZERO);
			divisorNotZero = mExpressionTranslation.constructBinaryComparisonFloatingPointExpression(loc,
					IASTBinaryExpression.op_notequals, divisor, divisorType, zero, divisorType);
		} else {
			throw new UnsupportedOperationException("cannot check division by zero for type " + divisorType);
		}

		final Statement additionalStatement;
		if (checkMode == PointerCheckMode.ASSUME) {
			additionalStatement = new AssumeStatement(loc, divisorNotZero);
		} else if (checkMode == PointerCheckMode.ASSERTandASSUME) {
			additionalStatement = new AssertStatement(loc, divisorNotZero);
			final Check check = new Check(Check.Spec.DIVISION_BY_ZERO);
			check.annotate(additionalStatement);
		} else {
			throw new AssertionError("illegal");
		}
		return new ExpressionResultBuilder(divisorExpRes).addStatement(additionalStatement).build();
	}

	/**
	 * Add checks for integer overflows. Construct arithmetic operation and add an assert statement that checks if the
	 * result is in the range of the corresponding C data type (i.e. check for overflow wrt. max and min value). Note
	 * that we do not check if a given expression is in the range. We explicitly construct a new expression for the
	 * arithmetic operation in this check because we possibly have to adjust the data type used in boogie. E.g., if we
	 * use 32bit bitvectors in Boogie we are unable to express an overflow check for a 32bit integer addition in C.
	 * Instead, we have to use a 33bit bit bitvector in Boogie.
	 */
	private ExpressionResultBuilder addIntegerBoundsCheck(final ILocation loc, final ExpressionResultBuilder erb,
			final CPrimitive resultType, final int operation, final IASTNode hook, final Expression... operands) {

		if (!mSettings.checkSignedIntegerBounds() || !resultType.isIntegerType() || mTypeSizes.isUnsigned(resultType)) {
			// nothing to do
			return erb;
		}
		final Check check = new Check(Spec.INTEGER_OVERFLOW);
		final Expression operationResult;
		if (operation == IASTBinaryExpression.op_shiftLeft || operation == IASTBinaryExpression.op_shiftLeftAssign) {
			// 2017-11-18 Matthias: For this shift there are more possibilities of undefined
			// behavior
			// I don't know where we should check them and if we should call them
			// "signed integer overflows" (probably not)
			operationResult = mExpressionTranslation.constructBinaryBitwiseIntegerExpression(loc, operation,
					operands[0], resultType, operands[1], resultType, hook);
		} else if (operands.length == 1) {
			operationResult = mExpressionTranslation.constructUnaryExpression(loc, operation, operands[0], resultType);
		} else if (operands.length == 2) {
			operationResult = mExpressionTranslation.constructArithmeticExpression(loc, operation, operands[0],
					resultType, operands[1], resultType);
		} else {
			throw new AssertionError("no such operation");
		}

		final Expression smallerMaxInt = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPLEQ,
				operationResult, ExpressionFactory.createIntegerLiteral(loc,
						mTypeSizes.getMaxValueOfPrimitiveType(resultType).toString()));
		if (!ExpressionFactory.isTrueLiteral(smallerMaxInt)) {
			final AssertStatement smallerMaxIntStmt = new AssertStatement(loc, smallerMaxInt);
			check.annotate(smallerMaxIntStmt);
			erb.addStatement(smallerMaxIntStmt);
		}

		final Expression biggerMinInt = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPGEQ,
				operationResult, ExpressionFactory.createIntegerLiteral(loc,
						mTypeSizes.getMinValueOfPrimitiveType(resultType).toString()));
		if (!ExpressionFactory.isTrueLiteral(biggerMinInt)) {
			final AssertStatement biggerMinIntStmt = new AssertStatement(loc, biggerMinInt);
			check.annotate(biggerMinIntStmt);
			erb.addStatement(biggerMinIntStmt);
		}
		return erb;
	}

	/**
	 * Check if pointer offset is in a legal range. In case a pointer points to allocated memory, the "base" of a
	 * pointer points to some array object (in C). Now we check if the offset of this pointer does not violate the
	 * bounds of that array. This means that the offset
	 * <ul>
	 * <li>must be non-negative, and
	 * <li>must be small enough that the pointer points to an element of the array or one past the last element of the
	 * array.
	 * </ul>
	 * Depending on the preferences of this plugin we
	 * <ul>
	 * <li>assert that the offset is in the bounds of the array,
	 * <li>assume that the offset is in the bounds of the array, or
	 * <li>add nothing.
	 * </ul>
	 *
	 * @param ptr
	 *            Boogie {@link Expression} that represents the pointer.
	 * @param erb
	 *            {@link ExpressionResult} to which the additional statements are added.
	 */
	private void addOffsetInBoundsCheck(final ILocation loc, final Expression ptr, final ExpressionResultBuilder erb) {
		// TODO: Matthias 2015-09-08 implement this
		// maybe additional parameters are required.
	}

	/**
	 * add havocs if we have a write to a union (which is not on heap, otherwise the heap model should deal with
	 * everything)
	 *
	 * @param loc
	 * @param rVal
	 * @param neighbourUnionFields
	 * @param rightHandSideWithConversionsApplied
	 * @param builder
	 *
	 * @return
	 */
	private ExpressionResultBuilder assignOrHavocUnionNeighbours(final ILocation loc, final RValue rVal,
			final Collection<ExpressionResult> neighbourUnionFields, final RValue rightHandSideWithConversionsApplied,
			final ExpressionResultBuilder builderIn, final IASTNode hook) {
		ExpressionResultBuilder builder = new ExpressionResultBuilder(builderIn);

		for (final ExpressionResult er : neighbourUnionFields) {
			// do not havoc when the type of the field is "compatible"
			if (rightHandSideWithConversionsApplied.getCType().equals(er.getLrValue().getCType())
					|| rightHandSideWithConversionsApplied.getCType().getUnderlyingType() instanceof CPrimitive
							&& er.getLrValue().getCType() instanceof CPrimitive
							&& ((CPrimitive) rightHandSideWithConversionsApplied.getCType().getUnderlyingType())
									.getGeneralType().equals(((CPrimitive) er.getLrValue().getCType()).getGeneralType())
							&& mMemoryHandler.calculateSizeOf(loc, rightHandSideWithConversionsApplied.getCType(),
									hook) == mMemoryHandler.calculateSizeOf(loc, er.getLrValue().getCType(), hook)) {

				builder.resetLrValue(rVal);
				final ExpressionResult assignment =
						makeAssignment(loc, er.getLrValue(), Collections.emptyList(), builder.build(), hook);
				builder = new ExpressionResultBuilder().addAllExceptLrValue(assignment)
						.setLrValue(assignment.getLrValue());

			} else {
				// otherwise we consider the value undefined, thus havoc it
				// TODO: maybe not use auxiliary variables so lavishly
				final AuxVarInfo auxVar =
						mAuxVarInfoBuilder.constructAuxVarInfo(loc, er.getLrValue().getCType(), SFO.AUXVAR.UNION);

				builder.addDeclaration(auxVar.getVarDec());
				builder.addAuxVar(auxVar);

				final RValue tmpVarRVal = new RValueForArrays(auxVar.getExp(), er.getLrValue().getCType());

				final Overapprox overapp = new Overapprox(
						"field of union updated " + "--> havoccing other fields (CHandler.makeAssignment(..))", loc);
				builder.addOverapprox(overapp);
				builder.resetLrValue(tmpVarRVal);

				final ExpressionResult assignment =
						makeAssignment(loc, er.getLrValue(), Collections.emptyList(), builder.build(), hook);
				builder = new ExpressionResultBuilder().addAllExceptLrValue(assignment)
						.setLrValue(assignment.getLrValue());
			}
		}
		return builder;
	}

	/**
	 * Checks ACSL for the next element and whether it must be added at the place where this method is called.
	 *
	 * @param main
	 *            the main IDispatcher.
	 * @param stmt
	 *            the statement list where the acsl should be appended - this is assumed to be <code>null</code> when
	 *            called from within the <i>translation unit</i>.
	 * @param next
	 *            the current child node of a translation unit of compound statement that will be added next. Should be
	 *            <code>null</code> when called at the end of <i>compound statement</i>.
	 * @param resultBuilder
	 *            the result builder where code translated from the ACSL code can be added to by this method
	 * @param compoundStatement
	 *            true iff this method was called during translation of a compound statement
	 * @param translationUnit
	 *            true iff this method was called during translation of the translation unit
	 * @param parent
	 *            the parent node of the current ACSL node. This should only be set if called at the end of a
	 *            <i>compound statement</i> and <code>null</code> otherwise.
	 */
	private void checkForACSL(final IDispatcher main, final ExpressionResultBuilder resultBuilder, final IASTNode next,
			final IASTNode parent, final boolean compoundStatement) {
		if (mAcsl == null) {
			return;
		}
		if (next instanceof IASTTranslationUnit) {
			for (final ACSLNode globAcsl : mAcsl.getAcsl()) {
				if (globAcsl instanceof GlobalLTLInvariant) {
					final LTLExpressionExtractor extractor = new LTLExpressionExtractor();
					extractor.run(globAcsl);
					mGlobAcslExtractors.add(extractor);
					try {
						mAcsl = main.nextACSLStatement();
					} catch (final ParseException e1) {
						final String msg = "Skipped a ACSL node due to: " + e1.getMessage();
						final ILocation loc = mLocationFactory.createCLocation(parent);
						mReporter.unsupportedSyntax(loc, msg);
					}
				}
			} // TODO: deal with other global ACSL stuff
		} else if (mAcsl.getSuccessorCNode() == null) {
			if (parent != null && compoundStatement && next == null) {
				// ACSL at the end of a function or at the end of the last statement in a switch
				// that is not terminated by a break
				// TODO: the latter case needs fixing, the ACSL is inserted outside the
				// corresponding if-scope right now
				// example: int s = 1; switch (s) { case 0: s++; //@ assert \false; } will yield
				// a unsafe boogie program
				for (final ACSLNode acslNode : mAcsl.getAcsl()) {
					if (parent.getFileLocation().getEndingLineNumber() <= acslNode.getStartingLineNumber()) {
						// handle later ...
						return;
					} else if (parent.getFileLocation().getEndingLineNumber() >= acslNode.getEndingLineNumber()
							&& parent.getFileLocation().getStartingLineNumber() <= acslNode.getStartingLineNumber()) {
						final Result acslResult = main.dispatch(acslNode, parent);
						if (acslResult instanceof ExpressionResult) {
							resultBuilder.addDeclarations(((ExpressionResult) acslResult).getDeclarations());
							resultBuilder.addStatements(((ExpressionResult) acslResult).getStatements());
							resultBuilder.addStatements(CTranslationUtil
									.createHavocsForAuxVars(((ExpressionResult) acslResult).getAuxVars()));
							try {
								mAcsl = main.nextACSLStatement();
							} catch (final ParseException e1) {
								final String msg = "Skipped a ACSL node due to: " + e1.getMessage();
								final ILocation loc = mLocationFactory.createCLocation(parent);
								mReporter.unsupportedSyntax(loc, msg);
							}
						} else {
							final String msg = "Unexpected ACSL comment: " + acslResult.getNode().getClass();
							final ILocation loc = mLocationFactory.createCLocation(parent);
							throw new IncorrectSyntaxException(loc, msg);
						}
					}
				}
			}

			// ELSE:
			// ACSL for next compound statement -> handle it next call
			// or in case of translation unit, ACSL in an unexpected
			// location!
		} else if (mAcsl.getSuccessorCNode().equals(next)) {
			assert mContract.isEmpty();
			for (final ACSLNode acslNode : mAcsl.getAcsl()) {
				if (compoundStatement) {
					// this means we are in a compound statement
					if (acslNode instanceof Contract || acslNode instanceof LoopAnnot) {
						// Loop contract
						mContract.add(acslNode);
					} else if (acslNode instanceof CodeAnnot) {
						final Result acslResult = main.dispatch(acslNode, next);
						if (acslResult instanceof ExpressionResult) {
							final ExpressionResult re = (ExpressionResult) acslResult;
							resultBuilder.addStatements(re.getStatements());
							resultBuilder.addDeclarations(re.getDeclarations());
						} else {
							resultBuilder.addStatement((Statement) acslResult.getNode());
						}
					} else {
						final String msg = "Unexpected ACSL comment: " + acslNode.getClass();
						final ILocation loc = mLocationFactory.createCLocation(next);
						throw new IncorrectSyntaxException(loc, msg);
					}
				} else {
					// this means we are in the translation unit
					if (acslNode instanceof Contract || acslNode instanceof LoopAnnot) {
						// Function contract
						mContract.add(acslNode);
					}
				}
			}
			try {
				mAcsl = main.nextACSLStatement();
			} catch (final ParseException e1) {
				final String msg = "Skipped a ACSL node due to: " + e1.getMessage();
				final ILocation loc = mLocationFactory.createCLocation(parent);
				mReporter.unsupportedSyntax(loc, msg);
			}

		}
	}

	/**
	 * Construct {@link Expression} that compares a component of two pointers.
	 *
	 * @param loc
	 * @param op
	 *            Comparison operation.
	 * @param leftPointer
	 *            Boogie expression that represents pointer.
	 * @param rightPointer
	 *            Boogie expression that represents pointer.
	 * @param component
	 *            Defines which component is compared. Either "base" or "offset"
	 */
	private Expression constructPointerComponentRelation(final ILocation loc, final int op,
			final Expression leftPointer, final Expression rightPointer, final String component) {
		assert component.equals(SFO.POINTER_BASE) || component.equals(SFO.POINTER_OFFSET) : "unknown pointer component";
		final StructAccessExpression leftComponent =
				ExpressionFactory.constructStructAccessExpression(loc, leftPointer, component);
		final StructAccessExpression rightComponent =
				ExpressionFactory.constructStructAccessExpression(loc, rightPointer, component);
		switch (op) {
		case IASTBinaryExpression.op_equals:
		case IASTBinaryExpression.op_notequals: {
			return mExpressionTranslation.constructBinaryEqualityExpression(loc, op, leftComponent,
					mExpressionTranslation.getCTypeOfPointerComponents(), rightComponent,
					mExpressionTranslation.getCTypeOfPointerComponents());
		}
		case IASTBinaryExpression.op_lessThan:
		case IASTBinaryExpression.op_lessEqual:
		case IASTBinaryExpression.op_greaterThan:
		case IASTBinaryExpression.op_greaterEqual:
			return mExpressionTranslation.constructBinaryComparisonExpression(loc, op, leftComponent,
					mExpressionTranslation.getCTypeOfPointerComponents(), rightComponent,
					mExpressionTranslation.getCTypeOfPointerComponents());
		default:
			throw new IllegalArgumentException("op " + op);
		}
	}

	/**
	 * Increment or decrement an expression. Construct expression that represents the value of the input expression but
	 * is incremented or decremented by one. If op is IASTBinaryExpression.op_plus we increment, if op is
	 * IASTBinaryExpression.op_minus we decrement. If ctype is CPrimitive, we increment/decrement by one and also call
	 * the method that adds (depending on the settings) an overflow check. If ctype is CPointer, we increment/decrement
	 * by the size of the pointsToType and call the method that adds (depending on the settings) an check if the pointer
	 * arithmetic was legal.
	 *
	 * @param result
	 *            note that this method has sideeffects on this object! (add..BoundCheck(..) calls)
	 */
	private Expression constructXcrementedValue(final ILocation loc, final ExpressionResultBuilder result,
			final CType ctype, final int op, final Expression value, final IASTNode hook) {
		assert op == IASTBinaryExpression.op_plus
				|| op == IASTBinaryExpression.op_minus : "has to be either minus or plus";
		final Expression valueIncremented;
		if (ctype instanceof CPointer) {
			final CPointer cPointer = (CPointer) ctype;
			final Expression oneEpr = mTypeSizes.constructLiteralForIntegerType(loc,
					mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ONE);
			final CPrimitive oneType = mExpressionTranslation.getCTypeOfPointerComponents();
			final RValue one = new RValue(oneEpr, oneType);
			valueIncremented =
					mMemoryHandler.doPointerArithmetic(op, loc, value, one, cPointer.getPointsToType(), hook);
			addOffsetInBoundsCheck(loc, valueIncremented, result);
		} else if (ctype instanceof CPrimitive) {
			final CPrimitive cPrimitive = (CPrimitive) ctype;

			final Expression one;
			if (ctype.isFloatingType()) {
				one = mExpressionTranslation.constructLiteralForFloatingType(loc, cPrimitive, BigDecimal.ONE);
			} else {
				one = mTypeSizes.constructLiteralForIntegerType(loc, cPrimitive, BigInteger.ONE);
			}
			addIntegerBoundsCheck(loc, result, cPrimitive, op, hook, value, one);
			valueIncremented =
					mExpressionTranslation.constructArithmeticExpression(loc, op, value, cPrimitive, one, cPrimitive);
		} else {
			throw new IllegalArgumentException("input has to be CPointer or CPrimitive");
		}
		return valueIncremented;
	}

	/**
	 * Subtract two pointers.
	 *
	 * @param pointsToType
	 *            {@link CType} of the objects to which the pointers point.
	 * @param leftPtr
	 *            Boogie {@link Expression} that represents the left pointer.
	 * @param rightPtr
	 *            Boogie {@link Expression} that represents the right pointer.
	 *
	 * @return An {@link Expression} that represents the difference of two Pointers according to C11 6.5.6.9.
	 */
	private Expression doPointerSubtraction(final ILocation loc, final Expression ptr1, final Expression ptr2,
			final CType pointsToType, final IASTNode hook) {
		final Expression ptr1Offset = ExpressionFactory.constructStructAccessExpression(loc, ptr1, SFO.POINTER_OFFSET);
		final Expression ptr2Offset = ExpressionFactory.constructStructAccessExpression(loc, ptr2, SFO.POINTER_OFFSET);
		final Expression offsetDifference = mExpressionTranslation.constructArithmeticExpression(loc,
				IASTBinaryExpression.op_minus, ptr1Offset, mExpressionTranslation.getCTypeOfPointerComponents(),
				ptr2Offset, mExpressionTranslation.getCTypeOfPointerComponents());
		final Expression typesize = mMemoryHandler.calculateSizeOf(loc, pointsToType, hook);
		final CPrimitive typesizeType = new CPrimitive(CPrimitives.INT);
		// TODO: typesizeType and .getCTypeOfPointerComponents() might be
		// different then one expression has to be converted into the type of
		// the other
		final Expression offsetDifferenceDividedByTypesize =
				mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_divide,
						offsetDifference, mExpressionTranslation.getCTypeOfPointerComponents(), typesize, typesizeType);
		return offsetDifferenceDividedByTypesize;
	}

	private void markAsIntFromPointer(final ILocation loc, final String lId, final IASTNode hook) {
		final String cId4Boogie = mSymbolTable.getCIdForBoogieId(lId);
		final SymbolTableValue old = mSymbolTable.findCSymbol(hook, cId4Boogie);
		final SymbolTableValue newSTV = old.createMarkedIsIntFromPointer();
		mSymbolTable.storeCSymbol(hook, cId4Boogie, newSTV);
	}

	private void processTUchild(final IDispatcher main, final ArrayList<Declaration> decl, final IASTNode child) {
		final ExpressionResultBuilder acslResultBuilder = new ExpressionResultBuilder();
		checkForACSL(main, acslResultBuilder, child, null, false);
		decl.addAll(acslResultBuilder.getDeclarations());
		final Result childRes = main.dispatch(child);

		if (childRes instanceof DeclarationResult) {
			// we have to add a global variable
			final DeclarationResult rd = (DeclarationResult) childRes;

			for (final CDeclaration cd : rd.getDeclarations()) {

				if (cd.getType().isIncomplete()) {
					/*
					 * type of this (variable) declaration is incomplete at the end of the file -- omit the declaration
					 * from Boogie program
					 */
					continue;
				}

				final Declaration boogieDecl = mSymbolTable.getBoogieDeclForCDecl(cd);
				if (boogieDecl instanceof VariableDeclaration) {
					mStaticObjectsHandler.addGlobalVariableDeclaration((VariableDeclaration) boogieDecl, cd);
				} else {
					throw new AssertionError("TODO: handle this case!");
				}
			}
		} else {
			if (childRes instanceof SkipResult) {
				return;
			}
			if (childRes.getNode() == null) {
				return;
			}
			assert childRes.getClass() == Result.class;
			assert childRes.getNode() != null;
			decl.add((Declaration) childRes.getNode());
		}
	}

	/**
	 * Checks if an LRValue is an Integer of value 0
	 *
	 */
	private boolean isNullPointerEquivalent(final RValue value, final CType type) {
		return BigInteger.ZERO.equals(mTypeSizes.extractIntegerValue(value, null));
	}

	/**
	 * Handle the address operator according to Section 6.5.3.2 of C11.
	 */
	private Result handleAddressOfOperator(final ExpressionResult er, final ILocation loc, final IASTNode hook)
			throws AssertionError {
		final RValue rVal;
		if (er.getLrValue() instanceof HeapLValue) {
			rVal = ((HeapLValue) er.getLrValue()).getAddressAsPointerRValue(mTypeHandler.getBoogiePointerType());
		} else if (er.getLrValue() instanceof LocalLValue) {
			if (mIsPrerun) {
				// We are in the prerun mode.
				// As a workaround, we (incorrectly) return the value
				// instead of the address. But we add variables to the
				// heapVars and hence in the non-prerun mode the input
				// will be a HeapLValue instead of a LocalLValue.
				final Expression expr = er.getLrValue().getValue();
				if (expr instanceof IdentifierExpression) {
					final IdentifierExpression idExpr = (IdentifierExpression) expr;
					moveIdOnHeap(loc, idExpr, hook);
				} else {
					moveArrayAndStructIdsOnHeap(loc, er.getLrValue().getUnderlyingType(), expr, er.getAuxVars(), hook);
				}
				rVal = convertToPointerRValue(er.getLrValue(), mTypeHandler.getBoogiePointerType());
			} else {
				throw new AssertionError("cannot take address of LocalLValue: this is a on-heap/off-heap bug");
			}
		} else if (er.getLrValue() instanceof RValue) {
			throw new AssertionError("cannot take address of RValue");
		} else {
			throw new AssertionError("Unknown value");
		}
		return new ExpressionResultBuilder().addAllExceptLrValue(er).setLrValue(rVal).build();
	}

	/**
	 * Handle the indirection operator according to Section 6.5.3.2 of C11. (The indirection operator is the star for
	 * pointer dereference.)
	 */
	private Result handleIndirectionOperator(final ExpressionResult expr, final ILocation loc, final IASTNode hook) {
		final ExpressionResult rop = mExprResultTransformer.makeRepresentationReadyForConversion(expr, this, loc,
				new CPointer(new CPrimitive(CPrimitives.VOID)), hook);
		final RValue rValue = (RValue) rop.getLrValue();
		if (!(rValue.getCType().getUnderlyingType() instanceof CPointer)) {
			throw new IllegalArgumentException("dereference needs pointer but got " + rValue.getCType());
		}
		final CPointer pointer = (CPointer) rValue.getCType().getUnderlyingType();
		final CType pointedType = pointer.getPointsToType();
		if (pointedType.isIncomplete()) {
			throw new IncorrectSyntaxException(loc, "Pointer dereference of incomplete type");
		}

		return new ExpressionResult(rop.getStatements(),
				LRValueFactory.constructHeapLValue(mTypeHandler, rValue.getValue(), pointedType, null),
				rop.getDeclarations(), rop.getAuxVars(), rop.getOverapprs());
	}

	/**
	 * Method that handles loops (for, while, do/while). Each of corresponding visit methods will call this method.
	 *
	 * @param main
	 *            the main IDispatcher
	 * @param node
	 *            the node to visit
	 * @param bodyResult
	 *            the body component of the corresponding loop
	 * @param condResult
	 *            the condition of the loop
	 * @param loopLabel
	 * @param witnessInvariant
	 * @return a result object holding the translated loop (i.e. a while loop)
	 */
	private Result handleLoops(final IDispatcher main, final IASTStatement node, Result bodyResult,
			ExpressionResult condResult, final String loopLabel, final LoopInvariantSpecification witnessInvariant) {
		assert node instanceof IASTWhileStatement || node instanceof IASTDoStatement
				|| node instanceof IASTForStatement;

		final ILocation loc = mLocationFactory.createCLocation(node);

		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();

		Result iterator = null;
		if (node instanceof IASTForStatement) {
			final IASTForStatement forStmt = (IASTForStatement) node;
			// add initialization for this for loop
			final IASTStatement cInitStmt = forStmt.getInitializerStatement();
			if (cInitStmt != null) {
				beginScope();
				final Result initializer = main.dispatch(cInitStmt);
				if (initializer instanceof ExpressionResult) {
					final ExpressionResult rExp = (ExpressionResult) initializer;
					resultBuilder.addAllExceptLrValue(rExp);
				} else if (initializer instanceof SkipResult) {
					// this is an empty statement in the C Code. We will skip it
				} else {
					final String msg = "Uninplemented type of for loop initialization: " + initializer.getClass();
					throw new UnsupportedSyntaxException(loc, msg);
				}
			}

			// translate iterator
			final IASTExpression cItExpr = forStmt.getIterationExpression();
			if (cItExpr != null) {
				iterator = main.dispatch(cItExpr);
			}

			// translate condition
			final IASTExpression cCondExpr = forStmt.getConditionExpression();
			if (cCondExpr != null) {
				condResult = (ExpressionResult) main.dispatch(cCondExpr);
			} else {
				condResult = new ExpressionResult(new RValue(ExpressionFactory.createBooleanLiteral(loc, true),
						new CPrimitive(CPrimitives.BOOL), true), Collections.emptySet());
			}

			mInnerMostLoopLabel.push(loopLabel);
			bodyResult = main.dispatch(forStmt.getBody());
			mInnerMostLoopLabel.pop();
		}
		assert CTranslationUtil.isAuxVarMapComplete(mNameHandler, condResult.getDeclarations(),
				condResult.getAuxVars());

		List<Statement> bodyBlock = new ArrayList<>();
		if (bodyResult instanceof ExpressionResult) {
			final ExpressionResult re = (ExpressionResult) bodyResult;
			resultBuilder.addDeclarations(re.getDeclarations());
			resultBuilder.addOverapprox(re.getOverapprs());
			bodyBlock.addAll(re.getStatements());
		} else if (bodyResult != null) {
			if (bodyResult.getNode() instanceof Body) {
				final Body body = (Body) bodyResult.getNode();
				bodyBlock.addAll(Arrays.asList(body.getBlock()));
				resultBuilder.addDeclarations(Arrays.asList(body.getLocalVars()));
			} else if (bodyResult instanceof SkipResult) {
				// do nothing - this is the special case where the loop does
				// not have a body.
			} else {
				final String msg = "Error: unexpected dispatch result" + bodyResult.getClass();
				throw new UnsupportedSyntaxException(loc, msg);
			}
		}

		if (node instanceof IASTForStatement) {
			// add the loop label (continue statements become a jump to the loop label)
			bodyBlock.add(new Label(loc, loopLabel));
		}

		if (node instanceof IASTForStatement && iterator != null) {
			// add iterator statements of this for loop
			if (iterator instanceof ExpressionListResult) {
				for (final ExpressionResult el : ((ExpressionListResult) iterator).getList()) {
					bodyBlock.addAll(el.getStatements());
					resultBuilder.addDeclarations(el.getDeclarations());
					bodyBlock.addAll(CTranslationUtil.createHavocsForAuxVars(el.getAuxVars()));
				}
			} else if (iterator instanceof ExpressionResult) {
				final ExpressionResult iteratorRE = (ExpressionResult) iterator;
				bodyBlock.addAll(iteratorRE.getStatements());
				resultBuilder.addDeclarations(iteratorRE.getDeclarations());
				resultBuilder.addOverapprox(iteratorRE.getOverapprs());
				bodyBlock.addAll(CTranslationUtil.createHavocsForAuxVars(iteratorRE.getAuxVars()));
			} else {
				final String msg = "Uninplemented type of loop iterator: " + iterator.getClass();
				throw new UnsupportedSyntaxException(loc, msg);
			}
		}

		condResult = mExprResultTransformer.switchToRValueAndRexIntToBoolIfNecessary(condResult, loc, node);
		resultBuilder.addDeclarations(condResult.getDeclarations());
		final RValue condRVal = (RValue) condResult.getLrValue();
		IfStatement ifStmt;
		{
			final Expression cond = ExpressionFactory.constructUnaryExpression(loc, UnaryExpression.Operator.LOGICNEG,
					condRVal.getValue());
			final ArrayList<Statement> thenStmt =
					new ArrayList<>(CTranslationUtil.createHavocsForAuxVars(condResult.getAuxVars()));
			thenStmt.add(new BreakStatement(loc));
			final Statement[] elseStmt =
					CTranslationUtil.createHavocsForAuxVars(condResult.getAuxVars()).toArray(new Statement[0]);
			ifStmt = new IfStatement(loc, cond, thenStmt.toArray(new Statement[thenStmt.size()]), elseStmt);
		}

		if (node instanceof IASTWhileStatement || node instanceof IASTForStatement) {
			bodyBlock.add(0, ifStmt);
			bodyBlock.addAll(0, condResult.getStatements());
			if (node instanceof IASTWhileStatement) {
				bodyBlock.add(0, new Label(loc, loopLabel));
			}
		} else if (node instanceof IASTDoStatement) {
			bodyBlock.add(new Label(loc, loopLabel));
			bodyBlock.addAll(condResult.getStatements());
			bodyBlock.add(ifStmt);
		}

		LoopInvariantSpecification[] spec;
		if (mContract == null) {
			spec = new LoopInvariantSpecification[0];
		} else {
			final List<LoopInvariantSpecification> specList = new ArrayList<>();
			if (witnessInvariant != null) {
				specList.add(witnessInvariant);
			}
			if (node instanceof IASTForStatement) {
				for (int i = 0; i < mContract.size(); i++) {
					// retranslate ACSL specification needed e.g., in cases
					// where ids of function parameters differ from is in ACSL
					// expression
					final Result retranslateRes = main.dispatch(mContract.get(i), node);
					if (retranslateRes instanceof ContractResult) {
						final ContractResult resContr = (ContractResult) retranslateRes;
						assert resContr.getSpecs().length == 1;
						for (final Specification cSpec : resContr.getSpecs()) {
							specList.add((LoopInvariantSpecification) cSpec);
						}
					} else {
						specList.add((LoopInvariantSpecification) retranslateRes.getNode());
					}
				}
			}
			spec = specList.toArray(new LoopInvariantSpecification[specList.size()]);
			// take care for behavior and completeness
			clearContract();
		}

		// bit of a workaround using an extra builder here..
		final ExpressionResultBuilder bodyBlockResultBuilder = new ExpressionResultBuilder();
		bodyBlockResultBuilder.addStatements(bodyBlock);

		if (node instanceof IASTForStatement) {
			if (((IASTForStatement) node).getInitializerStatement() != null) {
				updateStmtsAndDeclsAtScopeEnd(bodyBlockResultBuilder, node);
				endScope();

				resultBuilder.addDeclarations(bodyBlockResultBuilder.getDeclarations());
				bodyBlock = bodyBlockResultBuilder.getStatements();
			}
		}

		final ILocation ignoreLocation = LocationFactory.createIgnoreCLocation(node);
		final WhileStatement whileStmt =
				new WhileStatement(ignoreLocation, ExpressionFactory.createBooleanLiteral(ignoreLocation, true), spec,
						bodyBlock.toArray(new Statement[bodyBlock.size()]));
		resultBuilder.getOverappr().stream().forEach(a -> a.annotate(whileStmt));
		resultBuilder.addStatement(whileStmt);

		assert resultBuilder.getLrValue() == null : "there is an lrvalue although there should be none";
		assert resultBuilder.getAuxVars().isEmpty() : "auxvars were added although they should have been havoced";
		return resultBuilder.build();
	}

	/**
	 * Handle postfix increment and decrement operators according to Section 6.5.2.4 of C11. We translate the expression
	 * <code>LV++</code> to an auxiliary variable <code>t~post</code> and add to the resulting {@link ExpressionResult}
	 * the two assignments <code>t~post := LV</code> and <code>LV := t~post + 1</code>. Hence the auxiliary variable
	 * <code>t~post</code> stores the old value of the object to which the lvalue <code>LV</code> refers.
	 */
	private Result handlePostfixIncrementAndDecrement(final ILocation loc, final int postfixOp,
			ExpressionResult exprRes, final IASTNode hook) {
		assert !exprRes.getLrValue().isBoogieBool();
		final LRValue modifiedLValue = exprRes.getLrValue();
		exprRes = mExprResultTransformer.switchToRValueIfNecessary(exprRes, loc, hook);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder().addAllIncludingLrValue(exprRes);

		// In this case we need a temporary variable for the old value
		final AuxVarInfo auxvar =
				mAuxVarInfoBuilder.constructAuxVarInfo(loc, exprRes.getLrValue().getCType(), SFO.AUXVAR.POST_MOD);
		builder.addDeclaration(auxvar.getVarDec());
		builder.addAuxVar(auxvar);

		// assign the old value to the temporary variable
		final LeftHandSide[] tmpAsLhs = new LeftHandSide[] { auxvar.getLhs() };
		final Expression[] oldValue = new Expression[] { exprRes.getLrValue().getValue() };
		builder.addStatement(StatementFactory.constructAssignmentStatement(loc, tmpAsLhs, oldValue));
		final CType oType = exprRes.getLrValue().getCType().getUnderlyingType();
		final RValue tmpRValue = new RValue(auxvar.getExp(), oType);

		final int op;
		if (postfixOp == IASTUnaryExpression.op_postFixIncr) {
			op = IASTBinaryExpression.op_plus;
		} else if (postfixOp == IASTUnaryExpression.op_postFixDecr) {
			op = IASTBinaryExpression.op_minus;
		} else {
			throw new AssertionError("no postfix");
		}

		// in-/decremented value
		final Expression valueXcremented =
				constructXcrementedValue(loc, builder, oType, op, tmpRValue.getValue(), hook);

		builder.setOrResetLrValue(new RValue(valueXcremented, oType, false, false));
		final ExpressionResult assign =
				makeAssignment(loc, modifiedLValue, Collections.emptyList(), builder.build(), hook);
		return new ExpressionResultBuilder().addAllExceptLrValue(assign).setLrValue(tmpRValue).build();
	}

	/**
	 * Handle prefix increment and decrement operators according to Section 6.5.3.1 of C11. We translate the expression
	 * <code>++LV</code> to an auxiliary variable <code>t~pre</code> and add to the resulting {@link ExpressionResult}
	 * the two assignments <code>t~pre := LV+1</code> and <code>LV := t~pre</code>. Hence, the auxiliary variable
	 * <code>t~pre</code> stores the new value of the object to which the lvalue <code>LV</code> refers.
	 *
	 * Question: Why are we doing this complicated replacement and do not replace <code>++LV</code> by
	 * <code>LV + 1</code> ? Answer: We want to be ready for dealing with cases where there are several pre/post
	 * increment/decrement operations in one expression. We might extend our implementation in a way where the operation
	 * is done at a certain sequence point or all evaluation orders are considered.
	 */
	private Result handlePrefixIncrementAndDecrement(final int prefixOp, final ILocation loc, ExpressionResult exprRes,
			final IASTNode hook) {
		assert !exprRes.getLrValue().isBoogieBool();
		final LRValue modifiedLValue = exprRes.getLrValue();
		exprRes = mExprResultTransformer.switchToRValueIfNecessary(exprRes, loc, hook);
		final ExpressionResultBuilder builder = new ExpressionResultBuilder().addAllExceptLrValue(exprRes);

		// In this case we need a temporary variable for the new value
		final AuxVarInfo auxvar =
				mAuxVarInfoBuilder.constructAuxVarInfo(loc, exprRes.getLrValue().getCType(), SFO.AUXVAR.PRE_MOD);
		builder.addDeclaration(auxvar.getVarDec());
		builder.addAuxVar(auxvar);

		final int op;
		if (prefixOp == IASTUnaryExpression.op_prefixIncr) {
			op = IASTBinaryExpression.op_plus;
		} else if (prefixOp == IASTUnaryExpression.op_prefixDecr) {
			op = IASTBinaryExpression.op_minus;
		} else {
			throw new AssertionError("no prefix");
		}

		final CType oType = exprRes.getLrValue().getCType().getUnderlyingType();
		// in-/decremented value
		final Expression valueXcremented =
				constructXcrementedValue(loc, builder, oType, op, exprRes.getLrValue().getValue(), hook);

		// assign the old value to the temporary variable
		final LeftHandSide[] tmpAsLhs = new LeftHandSide[] { auxvar.getLhs() };
		final Expression[] newValue = new Expression[] { valueXcremented };
		builder.addStatement(StatementFactory.constructAssignmentStatement(loc, tmpAsLhs, newValue));

		builder.setLrValue(new RValue(valueXcremented, oType, false, false));
		final ExpressionResult assign =
				makeAssignment(loc, modifiedLValue, Collections.emptyList(), builder.build(), hook);
		final RValue tmpRValue = new RValue(auxvar.getExp(), oType);
		return new ExpressionResultBuilder().addAllExceptLrValue(assign).setLrValue(tmpRValue).build();
	}

	/**
	 * Handle equality operators according to Section 6.5.7 of C11. Assumes that left (resp. right) are the results from
	 * handling the operands. Requires that the {@link LRValue} of operands is an {@link RValue} (i.e.,
	 * switchToRValueIfNecessary was applied if needed). requires that the Boogie expressions in left (resp. right) are
	 * a non-boolean representation of these results (i.e., rexBoolToIntIfNecessary() has already been applied if
	 * needed).
	 *
	 * @param lhs
	 *            is non-null iff we haven an assignment
	 */
	private ExpressionResult handleBitshiftOperation(final ILocation loc, final LRValue lhs, final int op,
			final ExpressionResult left, final ExpressionResult right, final IASTNode hook) {
		assert left.getLrValue() instanceof RValue : "no RValue";
		assert right.getLrValue() instanceof RValue : "no RValue";
		final CType lType = left.getLrValue().getCType().getUnderlyingType();
		final CType rType = right.getLrValue().getCType().getUnderlyingType();
		if (!rType.isIntegerType() || !lType.isIntegerType()) {
			throw new UnsupportedOperationException("operands have to have integer types");
		}
		final ExpressionResult leftPromoted = mExpressionTranslation.doIntegerPromotion(loc, left);
		final CPrimitive typeOfResult = (CPrimitive) leftPromoted.getLrValue().getCType();
		final ExpressionResult rightConverted = mExprResultTransformer.convert(loc, right, typeOfResult);

		final Expression expr =
				mExpressionTranslation.constructBinaryBitwiseExpression(loc, op, leftPromoted.getLrValue().getValue(),
						typeOfResult, rightConverted.getLrValue().getValue(), typeOfResult, hook);
		final RValue rval = new RValue(expr, typeOfResult, false, false);
		final ExpressionResultBuilder result =
				new ExpressionResultBuilder().addAllExceptLrValue(leftPromoted, rightConverted);
		switch (op) {
		case IASTBinaryExpression.op_shiftLeft:
		case IASTBinaryExpression.op_shiftRight: {
			assert lhs == null : "no assignment";
			if (op == IASTBinaryExpression.op_shiftLeft) {
				addIntegerBoundsCheck(loc, result, (CPrimitive) rval.getCType(), op, hook,
						leftPromoted.getLrValue().getValue(), rightConverted.getLrValue().getValue());
			}
			result.setLrValue(rval);
			return result.build();
		}
		case IASTBinaryExpression.op_shiftLeftAssign:
		case IASTBinaryExpression.op_shiftRightAssign: {
			if (op == IASTBinaryExpression.op_shiftLeftAssign) {
				addIntegerBoundsCheck(loc, result, (CPrimitive) rval.getCType(), op, hook,
						leftPromoted.getLrValue().getValue(), rightConverted.getLrValue().getValue());
			}
			result.setLrValue(rval);
			return makeAssignment(loc, lhs, Collections.emptyList(), result.build(), hook);
		}
		default:
			throw new AssertionError("no bitshift " + op);
		}
	}

	/**
	 * Handle bitwise AND, bitwise XOR, and bitwise OR operators according to sections 6.5.10, 6.5.11, 6.5.12 of C11.
	 * Assumes that left (resp. right) are the results from handling the operands. Requires that the {@link LRValue} of
	 * operands is an {@link RValue} (i.e., switchToRValueIfNecessary was applied if needed). requires that the Boogie
	 * expressions in left (resp. right) are a non-boolean representation of these results (i.e.,
	 * rexBoolToIntIfNecessary() has already been applied if needed).
	 *
	 * @param lhs
	 *            is non-null iff we haven an assignment
	 */
	private ExpressionResult handleBitwiseArithmeticOperation(final ILocation loc, final LRValue lhs, final int op,
			ExpressionResult left, ExpressionResult right, final IASTNode hook) {
		assert left.getLrValue() instanceof RValue : "no RValue";
		assert right.getLrValue() instanceof RValue : "no RValue";
		final CType lType = left.getLrValue().getCType().getUnderlyingType();
		final CType rType = right.getLrValue().getCType().getUnderlyingType();
		if (!rType.isIntegerType() || !lType.isIntegerType()) {
			throw new UnsupportedOperationException("operands have to have integer types");
		}
		final Pair<ExpressionResult, ExpressionResult> newOps =
				mExpressionTranslation.usualArithmeticConversions(loc, left, right);
		left = newOps.getFirst();
		right = newOps.getSecond();
		final CPrimitive typeOfResult = (CPrimitive) left.getLrValue().getCType();
		assert typeOfResult.equals(left.getLrValue().getCType());
		final Expression expr = mExpressionTranslation.constructBinaryBitwiseExpression(loc, op,
				left.getLrValue().getValue(), typeOfResult, right.getLrValue().getValue(), typeOfResult, hook);
		final RValue rval = new RValue(expr, typeOfResult, false, false);
		switch (op) {
		case IASTBinaryExpression.op_binaryAnd:
		case IASTBinaryExpression.op_binaryXor:
		case IASTBinaryExpression.op_binaryOr: {
			assert lhs == null : "no assignment";
			return new ExpressionResultBuilder().addAllExceptLrValue(left, right).setLrValue(rval).build();
		}
		case IASTBinaryExpression.op_binaryAndAssign:
		case IASTBinaryExpression.op_binaryXorAssign:
		case IASTBinaryExpression.op_binaryOrAssign: {
			final ExpressionResult copy =
					new ExpressionResultBuilder().addAllExceptLrValue(left, right).setLrValue(rval).build();
			return makeAssignment(loc, lhs, Collections.emptyList(), copy, hook);
		}
		default:
			throw new AssertionError("no bitwise arithmetic operation " + op);
		}
	}

	/**
	 * Handle additive operators according to Sections 6.5.6 of C11. Assumes that left (resp. right) are the results
	 * from handling the operands. Requires that the {@link LRValue} of operands is an {@link RValue} (i.e.,
	 * switchToRValueIfNecessary was applied if needed). requires that the Boogie expressions in left (resp. right) are
	 * a non-boolean representation of these results (i.e., rexBoolToIntIfNecessary() has already been applied if
	 * needed).
	 *
	 * @param lhs
	 *            is non-null iff we haven an assignment
	 */
	ExpressionResult handleAdditiveOperation(final ILocation loc, final LRValue lhs, final int op,
			ExpressionResult left, ExpressionResult right, final IASTNode hook) {
		assert left.getLrValue() instanceof RValue : "no RValue";
		assert right.getLrValue() instanceof RValue : "no RValue";

		CType lType = left.getLrValue().getCType().getUnderlyingType();
		final CType rType = right.getLrValue().getCType().getUnderlyingType();

		if (lType instanceof CArray && rType.isArithmeticType()) {
			// arrays decay to pointers in this case
			assert !(((CArray) lType).getBound().getCType() instanceof CArray) : "TODO: think about this case";
			final CType valueType = ((CArray) lType).getValueType().getUnderlyingType();
			left = mExprResultTransformer.convert(loc, left, new CPointer(valueType));
			lType = left.getLrValue().getCType().getUnderlyingType();
		}

		final ExpressionResultBuilder builder;
		final Expression expr;
		final CType typeOfResult;
		if (lType.isArithmeticType() && rType.isArithmeticType()) {
			final Pair<ExpressionResult, ExpressionResult> newOps =
					mExpressionTranslation.usualArithmeticConversions(loc, left, right);
			left = newOps.getFirst();
			right = newOps.getSecond();
			builder = new ExpressionResultBuilder().addAllExceptLrValue(left, right);
			typeOfResult = left.getLrValue().getCType();
			assert typeOfResult.equals(right.getLrValue().getCType());

			addIntegerBoundsCheck(loc, builder, (CPrimitive) typeOfResult, op, hook, left.getLrValue().getValue(),
					right.getLrValue().getValue());
			expr = mExpressionTranslation.constructArithmeticExpression(loc, op, left.getLrValue().getValue(),
					(CPrimitive) typeOfResult, right.getLrValue().getValue(), (CPrimitive) typeOfResult);
		} else if (lType instanceof CPointer && rType.isArithmeticType()) {
			typeOfResult = left.getLrValue().getCType();
			final CType pointsToType = ((CPointer) typeOfResult).getPointsToType();
			final ExpressionResult re = mMemoryHandler.doPointerArithmeticWithConversion(op, loc,
					left.getLrValue().getValue(), (RValue) right.getLrValue(), pointsToType, hook);
			builder = new ExpressionResultBuilder().addAllExceptLrValue(left, right);
			builder.addAllExceptLrValue(re);
			expr = re.getLrValue().getValue();
			addOffsetInBoundsCheck(loc, expr, builder);
		} else if (lType.isArithmeticType() && rType instanceof CPointer) {
			if (op != IASTBinaryExpression.op_plus && op != IASTBinaryExpression.op_plusAssign) {
				throw new AssertionError("lType arithmetic, rType CPointer only legal if op is plus");
			}
			typeOfResult = right.getLrValue().getCType();
			final CType pointsToType = ((CPointer) typeOfResult).getPointsToType();
			final ExpressionResult re = mMemoryHandler.doPointerArithmeticWithConversion(op, loc,
					right.getLrValue().getValue(), (RValue) left.getLrValue(), pointsToType, hook);
			builder = new ExpressionResultBuilder().addAllExceptLrValue(left, right);
			builder.addAllExceptLrValue(re);
			expr = re.getLrValue().getValue();
			addOffsetInBoundsCheck(loc, expr, builder);
		} else if (lType instanceof CPointer && rType instanceof CPointer) {
			if (op != IASTBinaryExpression.op_minus && op != IASTBinaryExpression.op_minusAssign) {
				throw new AssertionError("lType arithmetic, rType CPointer only legal if op is minus");
			}
			// C11 6.5.6.9 says
			// "The size of the result is implementation-defined,
			// and its type (a signed integer type) is ptrdiff_t defined in
			// the <stddef.h> header."
			// We randomly choose the type whose Boogie translation we use to
			// represent pointer components.
			typeOfResult = mExpressionTranslation.getCTypeOfPointerComponents();
			CType pointsToType;
			{
				final CType leftPointsToType = ((CPointer) lType).getPointsToType();
				final CType rightPointsToType = ((CPointer) rType).getPointsToType();
				if (!leftPointsToType.equals(rightPointsToType)) {
					// TODO: Matthias 2015-09-08: Maybe this is too strict and we
					// have to check leftPointsToType.isCompatibleWith(rightPointsToType)
					throw new UnsupportedOperationException(
							"incompatible pointers: pointsto " + leftPointsToType + " " + rightPointsToType);
				}
				pointsToType = leftPointsToType;
			}
			builder = new ExpressionResultBuilder().addAllExceptLrValue(left, right);
			addBaseEqualityCheck(loc, left.getLrValue().getValue(), right.getLrValue().getValue(), builder);
			expr = doPointerSubtraction(loc, left.getLrValue().getValue(), right.getLrValue().getValue(), pointsToType,
					hook);

		} else {
			throw new UnsupportedOperationException("non-standard case of pointer arithmetic");
		}
		final RValue rval = new RValue(expr, typeOfResult, false, false);
		builder.setLrValue(rval);

		final ExpressionResult intermediateResult;
		if (left instanceof StringLiteralResult) {
			assert lhs == null : "unforseen case";
			/*
			 * if we had a StringLiteralResult as input, we have to restore the StringLiteralResult from the
			 * ExpressionResult.
			 */
			intermediateResult = new StringLiteralResult(builder.getLrValue(), builder.getOverappr(),
					((StringLiteralResult) left).getAuxVar(), ((StringLiteralResult) left).getLiteralString(),
					((StringLiteralResult) left).overApproximatesLongStringLiteral());
			builder.getDeclarations().forEach(decl -> mStaticObjectsHandler
					.addGlobalVarDeclarationWithoutCDeclaration((VariableDeclaration) decl));
			mStaticObjectsHandler.addStatementsForUltimateInit(builder.getStatements());

		} else {
			intermediateResult = builder.build();
		}

		switch (op) {
		case IASTBinaryExpression.op_plus:
		case IASTBinaryExpression.op_minus: {
			assert lhs == null : "no assignment";
			return intermediateResult;
		}
		case IASTBinaryExpression.op_plusAssign:
		case IASTBinaryExpression.op_minusAssign: {
			return makeAssignment(loc, lhs, Collections.emptyList(), intermediateResult, hook);
		}
		default:
			throw new AssertionError("no additive operation " + op);
		}
	}

	/**
	 * Handle conditional operator according to Section 6.5.15 of C11. Assumes that opCondition, opPositive, and
	 * opNegative are the results from handling the operands. Requires that the {@link LRValue} of operands is an
	 * {@link RValue} (i.e., switchToRValueIfNecessary was applied if needed). TODO: Check all corner cases, write some
	 * testfiles.
	 *
	 */
	ExpressionResult handleConditionalOperator(final ILocation loc, final ExpressionResult opConditionRaw,
			final ExpressionResult opPositiveRaw, final ExpressionResult opNegativeRaw, final IASTNode hook) {

		final ExpressionResult opCondition = mExprResultTransformer.rexIntToBoolIfNecessary(opConditionRaw, loc);
		ExpressionResult opPositive = mExprResultTransformer.rexBoolToIntIfNecessary(opPositiveRaw, loc);
		ExpressionResult opNegative = mExprResultTransformer.rexBoolToIntIfNecessary(opNegativeRaw, loc);

		/*
		 * C11 6.5.15.2 The first operand shall have scalar type.
		 */
		if (!opCondition.getLrValue().getCType().isScalarType()) {
			throw new IncorrectSyntaxException(loc, "first operand of a conditional operator must have scalar type");
		}

		/*
		 * C11 6.5.15.3 One of the following shall hold for the second and third operands: <li> both operands have
		 * arithmetic type; <li> both operands have the same structure or union type; <li> both operands have void type;
		 * <li> both operands are pointers to qualified or unqualified versions of compatible types; <li> one operand is
		 * a pointer and the other is a null pointer constant; or <li> one operand is a pointer to an object type and
		 * the other is a pointer to a qualified or unqualified version of void.
		 */

		/*
		 * C11 6.5.15.4 The first operand is evaluated; there is a sequence point between its evaluation and the
		 * evaluation of the second or third operand (whichever is evaluated). The second operand is evaluated only if
		 * the first compares unequal to 0; the third operand is evaluated only if the first compares equal to 0; the
		 * result is the value of the second or third operand (whichever is evaluated), converted to the type described
		 * below. 110)
		 *
		 * --> we translate this by a Boogie if-statement, such that the side effects of the evaluation of each C
		 * expression go into the respective branch of the Boogie if statement.
		 */

		/*
		 * C11 6.5.15.5 If both the second and third operands have arithmetic type, the result type that would be
		 * determined by the usual arithmetic conversions, were they applied to those two operands, is the type of the
		 * result. If both the operands have structure or union type, the result has that type. If both operands have
		 * void type, the result has void type.
		 */

		/*
		 * C11 6.5.15.6 If both the second and third operands are pointers or one is a null pointer constant and the
		 * other is a pointer, the result type is a pointer to a type qualified with all the type qualifiers of the
		 * types referenced by both operands. Furthermore, if both operands are pointers to compatible types or to
		 * differently qualified versions of compatible types, the result type is a pointer to an appropriately
		 * qualified version of the composite type; if one operand is a null pointer constant, the result has the type
		 * of the other operand; otherwise, one operand is a pointer to void or a qualified version of void, in which
		 * case the result type is a pointer to an appropriately qualified version of void.
		 *
		 * TODO: this is only partially implemented, for example we are not doing anything about the qualifiers,
		 * currently.
		 */

		/*
		 * Treatment of the cases where one or both branches have void type and the LRValue of the dispatch result of
		 * the branch is is null: We give a dummy LRValue, whose BoogieType is a type error so it cannot be used
		 * further.
		 */
		boolean secondArgIsVoid = false;
		boolean thirdArgIsVoid = false;
		if (!opPositive.hasLRValue() || !opNegative.hasLRValue()) {
			final RValue rVal =
					new RValue(ExpressionFactory.createVoidDummyExpression(loc), new CPrimitive(CPrimitives.VOID));
			if (!opPositive.hasLRValue()) {
				opPositive = new ExpressionResultBuilder(opPositive).setLrValue(rVal).build();
				secondArgIsVoid = true;
			}
			if (!opNegative.hasLRValue()) {
				opNegative = new ExpressionResultBuilder(opNegative).setLrValue(rVal).build();
				thirdArgIsVoid = true;
			}
		}

		final CType resultCType;
		if (opPositive.getLrValue().getCType().isArithmeticType()
				&& opNegative.getLrValue().getCType().isArithmeticType()) {
			/*
			 * C11 6.5.15.5: If both the second and third operands have arithmetic type, the result type that would be
			 * determined by the usual arithmetic conversions, were they applied to those two operands, is the type of
			 * the result.
			 */
			final Pair<ExpressionResult, ExpressionResult> newOps =
					mExpressionTranslation.usualArithmeticConversions(loc, opPositive, opNegative);
			opPositive = newOps.getFirst();
			opNegative = newOps.getSecond();
			resultCType = opPositive.getLrValue().getCType();
		} else if (secondArgIsVoid && thirdArgIsVoid) {
			/* C11 6.5.15.5 If both operands have void type, the result has void type. */
			resultCType = new CPrimitive(CPrimitives.VOID);
		} else if (opPositive.getLrValue().isNullPointerConstant()) {
			/* C11 6.5.15.6 if one operand is a null pointer constant, the result has the type of the other operand; */

			if (opNegative.getLrValue().getCType().getUnderlyingType() instanceof CPointer) {
				// convert the "0" to a pointer
				opPositive = mExpressionTranslation.convertIntToPointer(loc, opPositive,
						(CPointer) opNegative.getLrValue().getCType().getUnderlyingType());
				resultCType = opNegative.getLrValue().getCType();
			} else if (opNegative.getLrValue().getCType().getUnderlyingType() instanceof CArray) {
				/* if one of the branches has pointer type and one has array type, the array decays to a pointer. */
				opNegative = decayArrayToPointer(opNegative, loc, hook);
				opPositive = mExpressionTranslation.convertIntToPointer(loc, opPositive,
						(CPointer) opNegative.getLrValue().getCType().getUnderlyingType());
				resultCType = opNegative.getLrValue().getCType();
			} else {
				resultCType = opNegative.getLrValue().getCType();
			}

		} else if (opNegative.getLrValue().isNullPointerConstant()) {
			/* C11 6.5.15.6 if one operand is a null pointer constant, the result has the type of the other operand; */

			if (opPositive.getLrValue().getCType().getUnderlyingType() instanceof CPointer) {
				// convert the "0" to a pointer
				opNegative = mExpressionTranslation.convertIntToPointer(loc, opNegative,
						(CPointer) opPositive.getLrValue().getCType().getUnderlyingType());
				resultCType = opPositive.getLrValue().getCType();
			} else if (opPositive.getLrValue().getCType().getUnderlyingType() instanceof CArray) {
				/* if one of the branches has pointer type and one has array type, the array decays to a pointer. */
				opPositive = decayArrayToPointer(opPositive, loc, hook);
				opNegative = mExpressionTranslation.convertIntToPointer(loc, opNegative,
						(CPointer) opPositive.getLrValue().getCType().getUnderlyingType());
				resultCType = opPositive.getLrValue().getCType();
			} else {
				resultCType = opPositive.getLrValue().getCType();
			}
		} else {
			// default case: the types of the operands (should) match --> we choose one of them as the result CType
			resultCType = opPositive.getLrValue().getCType();
		}

		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();

		// TODO: a solution that checks if the void value is ever assigned would be nice, but unclear if necessary..
		// /*
		// * the value of this aux var may never be used outside the translation of this conditional operator.
		// * Using the aux var in the hope of detecting such errors easier. Otherwise one could just not make the
		// * assignment.
		// */

		resultBuilder.addAllExceptLrValue(opCondition);

		// auxvar that will hold the result of the ite expression
		final AuxVarInfo auxvar;
		if (resultCType.isVoidType()) {
			/* in this case we will not make any assignment, so we do not need the aux var */
			auxvar = null;
		} else {
			auxvar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, resultCType, SFO.AUXVAR.ITE);
			resultBuilder.addDeclaration(auxvar.getVarDec());
			resultBuilder.addAuxVar(auxvar);
		}

		// collect side effects of "then" branch
		final List<Statement> ifStatements = new ArrayList<>();
		{
			ifStatements.addAll(opPositive.getStatements());
			if (!resultCType.isVoidType() && !secondArgIsVoid) {
				final LeftHandSide[] lhs = { auxvar.getLhs() };
				final Expression assignedVal = opPositive.getLrValue().getValue();
				final AssignmentStatement assignStmt =
						StatementFactory.constructAssignmentStatement(loc, lhs, new Expression[] { assignedVal });
				for (final Overapprox overapprItem : resultBuilder.getOverappr()) {
					overapprItem.annotate(assignStmt);
				}
				ifStatements.add(assignStmt);
			}
			resultBuilder.addAllExceptLrValueAndStatements(opPositive);
		}

		// collect side effects of "else" branch
		final List<Statement> elseStatements = new ArrayList<>();
		{
			elseStatements.addAll(opNegative.getStatements());
			if (!resultCType.isVoidType() && !thirdArgIsVoid) {
				final LeftHandSide[] lhs = { auxvar.getLhs() };
				final Expression assignedVal = opNegative.getLrValue().getValue();
				final AssignmentStatement assignStmt =
						StatementFactory.constructAssignmentStatement(loc, lhs, new Expression[] { assignedVal });
				for (final Overapprox overapprItem : resultBuilder.getOverappr()) {
					overapprItem.annotate(assignStmt);
				}
				elseStatements.add(assignStmt);
			}
			resultBuilder.addAllExceptLrValueAndStatements(opNegative);
		}
		final Statement ifStatement = new IfStatement(loc, opCondition.getLrValue().getValue(),
				ifStatements.toArray(new Statement[ifStatements.size()]),
				elseStatements.toArray(new Statement[elseStatements.size()]));
		for (final Overapprox overapprItem : resultBuilder.getOverappr()) {
			overapprItem.annotate(ifStatement);
		}
		resultBuilder.addStatement(ifStatement);

		if (!resultCType.isVoidType()) {
			/* the result has a value only if the result type is not void.. */
			resultBuilder.setLrValue(new RValue(auxvar.getExp(), resultCType));
		} else {
			// for better error detection we give the dummy void value here (edit: see the todo above)
		}
		return resultBuilder.build();
	}

	/**
	 * Handle equality operators according to Section 6.5.9 of C11. Assumes that left (resp. right) are the results from
	 * handling the operands. Requires that the {@link LRValue} of operands is an {@link RValue} (i.e.,
	 * switchToRValueIfNecessary was applied if needed). requires that the Boogie expressions in left (resp. right) are
	 * a non-boolean representation of these results (i.e., rexBoolToIntIfNecessary() has already been applied if
	 * needed).
	 */
	ExpressionResult handleEqualityOperators(final ILocation loc, final int op, ExpressionResult left,
			ExpressionResult right) {
		assert left.getLrValue() instanceof RValue : "no RValue";
		assert right.getLrValue() instanceof RValue : "no RValue";
		{
			final CType lType = left.getLrValue().getCType().getUnderlyingType();
			final CType rType = right.getLrValue().getCType().getUnderlyingType();
			// FIXME Matthias 2015-09-05: operation only legal if both have type
			// CPointer I guess the following implicit casts are a workaround
			// for arrays (or structs or union?)
			if (lType instanceof CPointer || rType instanceof CPointer) {
				if (!(lType instanceof CPointer)) {
					// FIXME: the following is a workaround for the null pointer
					left = mExprResultTransformer.convert(loc, left, new CPointer(new CPrimitive(CPrimitives.VOID)));
				}
				if (!(rType instanceof CPointer)) {
					// FIXME: the following is a workaround for the null pointer
					right = mExprResultTransformer.convert(loc, right, new CPointer(new CPrimitive(CPrimitives.VOID)));
				}
			} else if (lType.isArithmeticType() && rType.isArithmeticType()) {
				final Pair<ExpressionResult, ExpressionResult> newOps =
						mExpressionTranslation.usualArithmeticConversions(loc, left, right);
				left = newOps.getFirst();
				right = newOps.getSecond();
			} else {
				throw new UnsupportedOperationException("unsupported " + rType + ", " + lType);
			}
		}
		// The result has type int (C11 6.5.9.1)
		final CPrimitive typeOfResult = new CPrimitive(CPrimitives.INT);
		final Expression expr =
				mExpressionTranslation.constructBinaryEqualityExpression(loc, op, left.getLrValue().getValue(),
						left.getLrValue().getCType(), right.getLrValue().getValue(), right.getLrValue().getCType());
		final RValue rval = new RValue(expr, typeOfResult, true, false);
		return new ExpressionResultBuilder().addAllExceptLrValue(left, right).setLrValue(rval).build();
	}

	/**
	 * Handle multiplicative operators according to Sections 6.5.5 of C11. Assumes that left (resp. right) are the
	 * results from handling the operands. Requires that the {@link LRValue} of operands is an {@link RValue} (i.e.,
	 * switchToRValueIfNecessary was applied if needed). requires that the Boogie expressions in left (resp. right) are
	 * a non-boolean representation of these results (i.e., rexBoolToIntIfNecessary() has already been applied if
	 * needed).
	 *
	 * @param lhs
	 *            is non-null iff we haven an assignment
	 */
	ExpressionResult handleMultiplicativeOperation(final ILocation loc, final LRValue lhs, final int op,
			ExpressionResult left, ExpressionResult right, final IASTNode hook) {
		assert left.getLrValue() instanceof RValue : "no RValue";
		assert right.getLrValue() instanceof RValue : "no RValue";
		final CType lType = left.getLrValue().getCType().getUnderlyingType();
		final CType rType = right.getLrValue().getCType().getUnderlyingType();
		if (!rType.isArithmeticType() || !lType.isArithmeticType()) {
			throw new UnsupportedOperationException("operands have to have integer types");
		}
		if (op == IASTBinaryExpression.op_divide || op == IASTBinaryExpression.op_modulo) {
			right = addDivisionByZeroCheck(loc, right);
		}
		final Pair<ExpressionResult, ExpressionResult> newOps =
				mExpressionTranslation.usualArithmeticConversions(loc, left, right);
		left = newOps.getFirst();
		right = newOps.getSecond();
		final CPrimitive typeOfResult = (CPrimitive) left.getLrValue().getCType();
		assert typeOfResult.equals(right.getLrValue().getCType());

		final ExpressionResultBuilder result = new ExpressionResultBuilder().addAllExceptLrValue(left, right);
		switch (op) {
		case IASTBinaryExpression.op_multiply:
		case IASTBinaryExpression.op_divide:
		case IASTBinaryExpression.op_multiplyAssign:
		case IASTBinaryExpression.op_divideAssign: {
			addIntegerBoundsCheck(loc, result, typeOfResult, op, hook, left.getLrValue().getValue(),
					right.getLrValue().getValue());
			break;
		}
		case IASTBinaryExpression.op_modulo:
		case IASTBinaryExpression.op_moduloAssign: {
			// no integer bounds check needed
			break;
		}
		default:
			throw new AssertionError("no multiplicative " + op);
		}

		final Expression expr = mExpressionTranslation.constructArithmeticExpression(loc, op,
				left.getLrValue().getValue(), typeOfResult, right.getLrValue().getValue(), typeOfResult);
		final RValue rval = new RValue(expr, typeOfResult, false, false);

		switch (op) {
		case IASTBinaryExpression.op_multiply:
		case IASTBinaryExpression.op_divide:
		case IASTBinaryExpression.op_modulo: {
			assert lhs == null : "no assignment";
			return result.setLrValue(rval).build();
		}
		case IASTBinaryExpression.op_multiplyAssign:
		case IASTBinaryExpression.op_divideAssign:
		case IASTBinaryExpression.op_moduloAssign: {
			return makeAssignment(loc, lhs, Collections.emptyList(), result.setLrValue(rval).build(), hook);
		}
		default:
			throw new AssertionError("no multiplicative " + op);
		}
	}

	/**
	 * Handle relational operators according to Section 6.5.8 of C11. Assumes that left (resp. right) are the results
	 * from handling the operands. Requires that the {@link LRValue} of operands is an {@link RValue} (i.e.,
	 * switchToRValueIfNecessary was applied if needed).
	 */
	ExpressionResult handleRelationalOperators(final ILocation loc, final int op, ExpressionResult left,
			ExpressionResult right) {
		assert left.getLrValue() instanceof RValue : "no RValue";
		assert right.getLrValue() instanceof RValue : "no RValue";
		left = mExprResultTransformer.rexBoolToIntIfNecessary(left, loc);
		right = mExprResultTransformer.rexBoolToIntIfNecessary(right, loc);
		CType lType = left.getLrValue().getCType().getUnderlyingType();
		CType rType = right.getLrValue().getCType().getUnderlyingType();

		final Expression expr;

		// Convert integer with a value of 0 to a Null pointer if necessary
		if (lType instanceof CPrimitive && rType instanceof CPointer
				&& isNullPointerEquivalent((RValue) left.getLrValue(), lType)) {
			// FIXME: the following is a workaround for the null pointer
			left = mExprResultTransformer.convert(loc, left, new CPointer(new CPrimitive(CPrimitives.VOID)));
			lType = left.getLrValue().getCType().getUnderlyingType();
		} else if (lType instanceof CPointer && rType instanceof CPrimitive
				&& isNullPointerEquivalent((RValue) right.getLrValue(), rType)) {
			// FIXME: the following is a workaround for the null pointer
			right = mExprResultTransformer.convert(loc, right, new CPointer(new CPrimitive(CPrimitives.VOID)));
			rType = right.getLrValue().getCType().getUnderlyingType();
		}
		ExpressionResultBuilder result = new ExpressionResultBuilder().addAllExceptLrValue(left, right);
		if (lType instanceof CPrimitive && rType instanceof CPrimitive) {
			assert lType.isRealType() && rType.isRealType() : "no real type";
			final Pair<ExpressionResult, ExpressionResult> newOps =
					mExpressionTranslation.usualArithmeticConversions(loc, left, right);
			left = newOps.getFirst();
			right = newOps.getSecond();
			result = new ExpressionResultBuilder().addAllExceptLrValue(left, right);
			expr = mExpressionTranslation.constructBinaryComparisonExpression(loc, op, left.getLrValue().getValue(),
					(CPrimitive) left.getLrValue().getCType(), right.getLrValue().getValue(),
					(CPrimitive) right.getLrValue().getCType());
		} else if (lType instanceof CPointer && rType instanceof CPointer) {
			final Expression baseEquality = constructPointerComponentRelation(loc, IASTBinaryExpression.op_equals,
					left.getLrValue().getValue(), right.getLrValue().getValue(), SFO.POINTER_BASE);
			final Expression offsetRelation = constructPointerComponentRelation(loc, op, left.getLrValue().getValue(),
					right.getLrValue().getValue(), SFO.POINTER_OFFSET);
			switch (mSettings.getPointerSubtractionAndComparisonValidityCheckMode()) {
			case ASSERTandASSUME:
				final Statement assertStm = new AssertStatement(loc, baseEquality);
				final Check chk = new Check(Spec.ILLEGAL_POINTER_ARITHMETIC);
				chk.annotate(assertStm);
				result.addStatement(assertStm);
				expr = offsetRelation;
				break;
			case ASSUME:
				final Statement assumeStm = new AssumeStatement(loc, baseEquality);
				result.addStatement(assumeStm);
				expr = offsetRelation;
				break;
			case IGNORE:
				// use conjunction
				expr = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND, baseEquality, offsetRelation);
				// TODO: Do not use conjunction. Use nondeterministic value
				// if baseEquality does not hold.
				break;
			default:
				throw new AssertionError("unknown value");
			}

		} else {
			throw new UnsupportedOperationException("unsupported " + lType + ", " + rType);
		}
		// The result has type int (C11 6.5.8.6)
		final CPrimitive typeOfResult = new CPrimitive(CPrimitives.INT);
		final RValue rval = new RValue(expr, typeOfResult, true, false);
		return result.setLrValue(rval).build();
	}

	/**
	 * Handle unary arithmetic operators according to Section 6.5.3.3 of C11. Assumes that left (resp. right) are the
	 * results from handling the operands. Requires that the {@link LRValue} of operands is an {@link RValue} (i.e.,
	 * switchToRValueIfNecessary was applied if needed).
	 */
	ExpressionResult handleUnaryArithmeticOperators(final ILocation loc, final int op, ExpressionResult operand,
			final IASTNode hook) {
		assert operand.getLrValue() instanceof RValue : "no RValue";
		final CType inputType = operand.getLrValue().getCType().getUnderlyingType();

		switch (op) {
		case IASTUnaryExpression.op_not: {
			if (!inputType.isScalarType()) {
				throw new IllegalArgumentException("scalar type required");
			}
			final Expression negated;
			if (operand.getLrValue().isBoogieBool()) {
				// in Boogie already represented by bool, we only negate
				negated = ExpressionFactory.constructUnaryExpression(loc, UnaryExpression.Operator.LOGICNEG,
						operand.getLrValue().getValue());
			} else {
				final Expression rhsOfComparison;
				if (inputType instanceof CPointer) {
					rhsOfComparison = mExpressionTranslation.constructNullPointer(loc);
				} else if (inputType instanceof CEnum) {
					final CPrimitive intType = new CPrimitive(CPrimitives.INT);
					rhsOfComparison = mExpressionTranslation.constructZero(loc, intType);
				} else if (inputType instanceof CPrimitive) {
					rhsOfComparison = mExpressionTranslation.constructZero(loc, inputType);
				} else {
					throw new AssertionError("illegal case");
				}
				negated = mExpressionTranslation.constructBinaryEqualityExpression(loc, IASTBinaryExpression.op_equals,
						operand.getLrValue().getValue(), inputType, rhsOfComparison, inputType);

			}
			final ExpressionResultBuilder builder = new ExpressionResultBuilder().addAllExceptLrValue(operand);
			// C11 6.5.3.3.5 The result has type int.
			final CPrimitive resultType = new CPrimitive(CPrimitives.INT);
			// type of Operator.COMPEQ expression is bool
			final boolean isBoogieBool = true;
			final RValue rval = new RValue(negated, resultType, isBoogieBool);
			return builder.setLrValue(rval).build();
		}
		case IASTUnaryExpression.op_plus: {
			if (!inputType.isArithmeticType()) {
				throw new UnsupportedOperationException("arithmetic type required");
			}
			if (inputType.isArithmeticType()) {
				operand = mExprResultTransformer.rexBoolToIntIfNecessary(operand, loc);
				operand = mExpressionTranslation.doIntegerPromotion(loc, operand);
			}
			return operand;
		}
		case IASTUnaryExpression.op_minus:
		case IASTUnaryExpression.op_tilde:
			if (!inputType.isArithmeticType()) {
				throw new UnsupportedOperationException("arithmetic type required");
			}
			operand = mExprResultTransformer.rexBoolToIntIfNecessary(operand, loc);
			operand = mExpressionTranslation.doIntegerPromotion(loc, operand);
			final CPrimitive resultType = (CPrimitive) operand.getLrValue().getCType();
			final ExpressionResultBuilder result = new ExpressionResultBuilder().addAllExceptLrValue(operand);
			if (op == IASTUnaryExpression.op_minus && resultType.isIntegerType()) {
				addIntegerBoundsCheck(loc, result, resultType, op, hook, operand.getLrValue().getValue());
			}
			final Expression bwexpr = mExpressionTranslation.constructUnaryExpression(loc, op,
					operand.getLrValue().getValue(), resultType);
			final RValue rval = new RValue(bwexpr, resultType, false);
			return result.setLrValue(rval).build();
		default:
			throw new IllegalArgumentException("not a unary arithmetic operator " + op);
		}
	}

}
