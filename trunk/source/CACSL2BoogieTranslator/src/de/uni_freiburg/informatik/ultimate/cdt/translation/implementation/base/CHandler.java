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
import org.eclipse.cdt.core.dom.ast.IASTTypeId;
import org.eclipse.cdt.core.dom.ast.IASTTypeIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTTypeIdInitializerExpression;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTWhileStatement;
import org.eclipse.cdt.core.dom.ast.IBinding;
import org.eclipse.cdt.core.dom.ast.IFunction;
import org.eclipse.cdt.core.dom.ast.IProblemBinding;
import org.eclipse.cdt.core.dom.ast.ITypedef;
import org.eclipse.cdt.core.dom.ast.IVariable;
import org.eclipse.cdt.core.dom.ast.c.ICASTCompositeTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.gnu.IGNUASTCompoundStatementExpression;
import org.eclipse.cdt.core.dom.ast.gnu.c.ICASTKnRFunctionDeclarator;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTDesignatedInitializer;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTLiteralExpression;
import org.eclipse.cdt.internal.core.dom.parser.c.CVariable;

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
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
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
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings.SettingsChange;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.ArrayHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.CCharacterConstant;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.CStringLiteral;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.FunctionHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.InitializationHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.LocalLValueILocationPair;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler.MemoryArea;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.PostProcessor;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.ProcedureManager;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.StaticObjectsHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.StructHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizeAndOffsetComputer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.BitabsTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.standardfunctions.StandardFunctionHandler;
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
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionWithIncompleteTypeResult;
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
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.MemoryModel;

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

	/** Set this flag if you want to trigger a restart of the translation with different settings */
	private boolean mRestartTranslationWithDifferentSettings;

	private TranslationSettings.SettingsChange mSettingsChangeForTranslationRestart;

	private final CExpressionTranslator mCExpressionTranslator;

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

		mTypeSizeComputer = new TypeSizeAndOffsetComputer(mTypeSizes, mExpressionTranslation, mTypeHandler,
				mSettings.useBitpreciseBitfields());

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
		mInitHandler = new InitializationHandler(mSettings, mMemoryHandler, mExpressionTranslation, mProcedureManager,
				mTypeHandler, mAuxVarInfoBuilder, mTypeSizeComputer, mTypeSizes, this, mExprResultTransformer);

		mCExpressionTranslator = new CExpressionTranslator(mSettings, mMemoryHandler, mExpressionTranslation,
				mExprResultTransformer, mAuxVarInfoBuilder, mTypeSizes, mStaticObjectsHandler);
		mStandardFunctionHandler = new StandardFunctionHandler(mLogger, functionTable, mAuxVarInfoBuilder, mNameHandler,
				mExpressionTranslation, mMemoryHandler, mTypeSizeComputer, mProcedureManager, mReporter, mTypeSizes,
				mSymbolTable, mSettings, mExprResultTransformer, mLocationFactory, mTypeHandler,
				mCExpressionTranslator);

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
		mInitHandler = new InitializationHandler(mSettings, mMemoryHandler, mExpressionTranslation, procedureManager,
				mTypeHandler, mAuxVarInfoBuilder, mTypeSizeComputer, mTypeSizes, this, mExprResultTransformer);

		mCExpressionTranslator = new CExpressionTranslator(mSettings, mMemoryHandler, mExpressionTranslation,
				mExprResultTransformer, mAuxVarInfoBuilder, mTypeSizes, mStaticObjectsHandler);
		mStandardFunctionHandler = new StandardFunctionHandler(mLogger, prerunCHandler.mFunctionTable,
				mAuxVarInfoBuilder, mNameHandler, mExpressionTranslation, mMemoryHandler, mTypeSizeComputer,
				procedureManager, mReporter, mTypeSizes, mSymbolTable, mSettings, mExprResultTransformer,
				mLocationFactory, mTypeHandler, mCExpressionTranslator);
		mPostProcessor = new PostProcessor(mLogger, mExpressionTranslation, mTypeHandler, mReporter, mAuxVarInfoBuilder,
				mFunctionToIndex, mTypeSizes, mSymbolTable, mStaticObjectsHandler, mSettings, procedureManager,
				mMemoryHandler, mInitHandler, mFunctionHandler, this);

	}

	/**
	 * @return An {@link ExpressionResultTransformer} that is bound to this {@link CHandler} instance.
	 */
	public ExpressionResultTransformer getExpressionResultTransformer() {
		return mExprResultTransformer;
	}

	public CExpressionTranslator getCExpressionTranslator() {
		return mCExpressionTranslator;
	}

	private void
			signalTranslationRestartWithDifferentSettings(final TranslationSettings.SettingsChange settingsChange) {
		assert mIsPrerun : "currently only checking the restart flag after the prerunner -- might change it perhaps "
				+ "(in MainTranslator).";

		mRestartTranslationWithDifferentSettings = true;

		if (mSettingsChangeForTranslationRestart == null) {
			mSettingsChangeForTranslationRestart = settingsChange;
		} else if (mSettingsChangeForTranslationRestart.equals(settingsChange)) {
			// nothing to do
		} else {
			mLogger.warn("More than one settings change for restart is not yet implemented; using only the first "
					+ "one to be reported");
			// do nothing
		}
	}

	public boolean restartTranslationWithDifferentSettings() {
		return mRestartTranslationWithDifferentSettings;
	}

	public SettingsChange getSettingsChangeForTranslationRestart() {
		return mSettingsChangeForTranslationRestart;
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
		return mInitHandler.handleDesignatedInitializer(main, mLocationFactory, mMemoryHandler, mStructHandler, node);
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
		//@CL, with binary expression, we check bitwise operator first
		boolean isBit = BitabsTranslation.containBitwise(node.getOperand2());
		switch (node.getOperator()) {
		case IASTBinaryExpression.op_assign: {
			
			//@Cyrus, debug. In this case we only transform with and-rule: r= a&b => r<=b, r<=a, they are positive, 
			// and rhs is a bitwise binary expression.
			
			mLogger.debug("left hand side expression in assignment: "+ leftOperand.getLrValue().toString());
			if (isBit & (node.getOperand1() instanceof IASTIdExpression)) {
				return BitabsTranslation.abstractAssgin(this, mProcedureManager, mDeclarations, mExpressionTranslation, mNameHandler, mAuxVarInfoBuilder,
						mSymbolTable, mExprResultTransformer, main, mLocationFactory, node);
			} else {
					final ExpressionResultBuilder builder = new ExpressionResultBuilder();
					builder.addAllExceptLrValue(leftOperand);
					final CType lType = leftOperand.getLrValue().getCType().getUnderlyingType();
					final ExpressionResult rightOperandSwitched = mExprResultTransformer
							.makeRepresentationReadyForConversionAndRexBoolToInt(rightOperand, loc, lType, node);
					builder.addAllIncludingLrValue(rightOperandSwitched);
					return makeAssignment(loc, leftOperand.getLrValue(), leftOperand.getNeighbourUnionFields(), builder.build(),
					node);
					}
			}
		case IASTBinaryExpression.op_equals:
		case IASTBinaryExpression.op_notequals: {
			final ExpressionResult rl = mExprResultTransformer.transformSwitchRexBoolToInt(leftOperand, loc, node);
			final ExpressionResult rr = mExprResultTransformer.transformSwitchRexBoolToInt(rightOperand, loc, node);
			return mCExpressionTranslator.handleEqualityOperators(loc, node.getOperator(), rl, rr);
		}
		case IASTBinaryExpression.op_greaterEqual:
		case IASTBinaryExpression.op_greaterThan:
		case IASTBinaryExpression.op_lessEqual:
		case IASTBinaryExpression.op_lessThan: {
		/*
		 * if (isBit & (node.getOperand1() instanceof IASTIdExpression)) {
		 * System.out.println("---get bitwise in realational operators: "+node.toString(
		 * )); return BitabsTranslation.abstractRelational(this, mProcedureManager,
		 * mDeclarations, mExpressionTranslation, mNameHandler, mAuxVarInfoBuilder,
		 * mSymbolTable, mExprResultTransformer, main, mLocationFactory, node); } else {
		 */
				final ExpressionResult rl = mExprResultTransformer.switchToRValue(leftOperand, loc, node);
				final ExpressionResult rr = mExprResultTransformer.switchToRValue(rightOperand, loc, node);
				return mCExpressionTranslator.handleRelationalOperators(loc, node.getOperator(), rl, rr);
		//	}
		}

		case IASTBinaryExpression.op_logicalAnd:
		case IASTBinaryExpression.op_logicalOr: {
			final ExpressionResult rl = mExprResultTransformer.transformSwitchRexIntToBool(leftOperand, loc, node);
			final ExpressionResult rr = mExprResultTransformer.transformSwitchRexIntToBool(rightOperand, loc, node);
			return handleAndOrOperators(loc, node.getOperator(), rl, rr);
		}
		case IASTBinaryExpression.op_modulo:
		case IASTBinaryExpression.op_multiply:
		case IASTBinaryExpression.op_divide: {
			final ExpressionResult rl = mExprResultTransformer.transformSwitchRexBoolToInt(leftOperand, loc, node);
			final ExpressionResult rr = mExprResultTransformer.transformSwitchRexBoolToInt(rightOperand, loc, node);
			return mCExpressionTranslator.handleMultiplicativeOperation(loc, node.getOperator(), rl, rr, node);
		}
		case IASTBinaryExpression.op_moduloAssign:
		case IASTBinaryExpression.op_multiplyAssign:
		case IASTBinaryExpression.op_divideAssign: {
			final ExpressionResult rl = mExprResultTransformer.transformSwitchRexBoolToInt(leftOperand, loc, node);
			final ExpressionResult rr = mExprResultTransformer.transformSwitchRexBoolToInt(rightOperand, loc, node);
			final ExpressionResult result =
					mCExpressionTranslator.handleMultiplicativeOperation(loc, node.getOperator(), rl, rr, node);
			return makeAssignment(loc, leftOperand.getLrValue(), Collections.emptyList(), result, node);
		}
		case IASTBinaryExpression.op_plus:
		case IASTBinaryExpression.op_minus: {
			assert checkSubstractPointerArith(node, leftOperand,
					rightOperand) : "subtraction is not allowed in pointer arithmetic, right?";

			// if we are "adding" arrays, they must be treated as pointers
			final ExpressionResult rl = mExprResultTransformer.transformDecaySwitchRexBoolToInt(leftOperand, loc, node);
			final ExpressionResult rr =
					mExprResultTransformer.transformDecaySwitchRexBoolToInt(rightOperand, loc, node);

			return mCExpressionTranslator.handleAdditiveOperation(loc, node.getOperator(), rl, rr, node);
		}
		case IASTBinaryExpression.op_plusAssign:
		case IASTBinaryExpression.op_minusAssign: {
			assert checkSubstractPointerArith(node, leftOperand,
					rightOperand) : "subtraction is not allowed in pointer arithmetic, right?";

			final ExpressionResult rl = mExprResultTransformer.transformDecaySwitchRexBoolToInt(leftOperand, loc, node);
			final ExpressionResult rr =
					mExprResultTransformer.transformDecaySwitchRexBoolToInt(rightOperand, loc, node);
			final ExpressionResult result =
					mCExpressionTranslator.handleAdditiveOperation(loc, node.getOperator(), rl, rr, node);
			return makeAssignment(loc, leftOperand.getLrValue(), Collections.emptyList(), result, node);
		}
		case IASTBinaryExpression.op_binaryAnd:
		case IASTBinaryExpression.op_binaryOr:
		case IASTBinaryExpression.op_binaryXor: {
			final ExpressionResult rl = mExprResultTransformer.transformSwitchRexBoolToInt(leftOperand, loc, node);
			final ExpressionResult rr = mExprResultTransformer.transformSwitchRexBoolToInt(rightOperand, loc, node);
			return mCExpressionTranslator.handleBitwiseArithmeticOperation(loc, node.getOperator(), rl, rr, node);
		}
		case IASTBinaryExpression.op_binaryAndAssign:
		case IASTBinaryExpression.op_binaryOrAssign:
		case IASTBinaryExpression.op_binaryXorAssign: {
			final ExpressionResult rl = mExprResultTransformer.transformSwitchRexBoolToInt(leftOperand, loc, node);
			final ExpressionResult rr = mExprResultTransformer.transformSwitchRexBoolToInt(rightOperand, loc, node);
			final ExpressionResult result =
					mCExpressionTranslator.handleBitwiseArithmeticOperation(loc, node.getOperator(), rl, rr, node);
			return makeAssignment(loc, leftOperand.getLrValue(), Collections.emptyList(), result, node);
		}
		case IASTBinaryExpression.op_shiftLeft:
		case IASTBinaryExpression.op_shiftRight: {
			final ExpressionResult rl = mExprResultTransformer.transformSwitchRexBoolToInt(leftOperand, loc, node);
			final ExpressionResult rr = mExprResultTransformer.transformSwitchRexBoolToInt(rightOperand, loc, node);
			return mCExpressionTranslator.handleBitshiftOperation(loc, node.getOperator(), rl, rr, node);

		}
		case IASTBinaryExpression.op_shiftLeftAssign:
		case IASTBinaryExpression.op_shiftRightAssign: {
			final ExpressionResult rl = mExprResultTransformer.transformSwitchRexBoolToInt(leftOperand, loc, node);
			final ExpressionResult rr = mExprResultTransformer.transformSwitchRexBoolToInt(rightOperand, loc, node);
			final ExpressionResult result =
					mCExpressionTranslator.handleBitshiftOperation(loc, node.getOperator(), rl, rr, node);
			return makeAssignment(loc, leftOperand.getLrValue(), Collections.emptyList(), result, node);
		}
		default: 
			final String msg = "Unknown or unsupported unary operation";
			throw new UnsupportedSyntaxException(loc, msg);
		}
	}

	private static boolean checkSubstractPointerArith(final IASTBinaryExpression node,
			final ExpressionResult leftOperand, final ExpressionResult rightOperand) {
		if (!(leftOperand.getLrValue().getCType() instanceof CArray)
				|| node.getOperator() == IASTBinaryExpression.op_plus) {
			return true;
		}
		return !(rightOperand.getLrValue().getCType() instanceof CArray)
				|| node.getOperator() == IASTBinaryExpression.op_plus;
	}

	private Result handleAndOrOperators(final ILocation loc, final int operator, final ExpressionResult rl,
			final ExpressionResult rr) {
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();

		// // NOTE: no rr.stmt
		builder.addAllExceptLrValue(rl);

		// NOTE: do not unconditionally add rr.stmt as it may be short-circuited
		builder.addDeclarations(rr.getDeclarations());
		builder.addAuxVars(rr.getAuxVars());
		builder.addOverapprox(rr.getOverapprs());

		final BinaryExpression.Operator boogieOp;
		if (operator == IASTBinaryExpression.op_logicalOr) {
			boogieOp = BinaryExpression.Operator.LOGICOR;
		} else if (operator == IASTBinaryExpression.op_logicalAnd) {
			boogieOp = BinaryExpression.Operator.LOGICAND;
		} else {
			throw new IllegalArgumentException("Wrong binary operator " + operator);
		}

		if (rr.getStatements().isEmpty()) {
			// no statements in right operands, hence no side effects in operand
			// we can directly combine operands with LOGICAND/OR
			final RValue newRVal =
					new RValue(ExpressionFactory.newBinaryExpression(loc, boogieOp, rl.getLrValue().getValue(),
							rr.getLrValue().getValue()), new CPrimitive(CPrimitive.CPrimitives.INT), true);

			builder.setLrValue(newRVal);
			return builder.build();
		}

		// there are side effects, we have to handle them
		// create and add shortcircuit "auxvar #t~SHORT~UID"
		final CPrimitive intType = new CPrimitive(CPrimitives.INT);
		final AuxVarInfo auxvarInfo = mAuxVarInfoBuilder.constructAuxVarInfo(loc, intType,
				new PrimitiveType(loc, BoogieType.TYPE_BOOL, SFO.BOOL), SFO.AUXVAR.SHORTCIRCUIT);
		builder.addDeclaration(auxvarInfo.getVarDec());
		builder.addAuxVar(auxvarInfo);
		final RValue auxvarRval = new RValue(auxvarInfo.getExp(), intType, true);

		// add auxvar assignment "#t~SHORT~UID = left"
		final AssignmentStatement assignStmt = StatementFactory.constructAssignmentStatement(loc,
				new LeftHandSide[] { auxvarInfo.getLhs() }, new Expression[] { rl.getLrValue().getValue() });
		builder.addStatementAndAnnotateOverapprox(assignStmt);

		final Statement[] thenPart;
		final Statement[] elsePart;
		final List<Statement> tmpList = new ArrayList<>();
		tmpList.addAll(rr.getStatements());
		tmpList.add(StatementFactory.constructAssignmentStatement(loc, new LeftHandSide[] { auxvarInfo.getLhs() },
				new Expression[] { rr.getLrValue().getValue() }));
		if (boogieOp == Operator.LOGICAND) {
			// generate "if (#t~SHORT~UID) {#t~SHORT~UID = right;}"
			thenPart = tmpList.toArray(new Statement[tmpList.size()]);
			elsePart = new Statement[0];
		} else {
			// generate "if (#t~SHORT~UID) {} else {#t~SHORT~UID = right;}"
			thenPart = new Statement[0];
			elsePart = tmpList.toArray(new Statement[tmpList.size()]);
		}
		final IfStatement ifStatement = new IfStatement(loc, auxvarRval.getValue(), thenPart, elsePart);
		builder.addStatementAndAnnotateOverapprox(ifStatement);
		builder.setLrValue(auxvarRval);
		return builder.build();
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
		final ExpressionResult switched =
				mExprResultTransformer.switchToRValue(dispatched, mLocationFactory.createCLocation(node), node);
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
		expr = mExprResultTransformer.makeRepresentationReadyForConversion(expr, loc, newCType, node);
		checkUnsupportedPointerCast(expr, loc, newCType);

		if (mSettings.isAdaptMemoryModelResolutionOnPointerCasts() && mIsPrerun) {
			checkIfNecessaryMemoryModelAdaption(node, loc, newCType, expr);
		}

		expr = mExprResultTransformer.rexBoolToInt(expr, loc);
		expr = mExprResultTransformer.performImplicitConversion(expr, newCType, loc);
		return expr;
	}

	private void checkIfNecessaryMemoryModelAdaption(final IASTCastExpression node, final ILocation loc,
			final CType castTargetType, final ExpressionResult operand) {
		final CType operandType = operand.getLrValue().getCType().getUnderlyingType();
		if (!(operandType instanceof CArray) && !(operandType instanceof CPointer)
				|| !(castTargetType instanceof CArray) && !(castTargetType instanceof CPointer)) {
			return;
		}

		// memory model adaptation might be necessary
		final CType operandValueType;
		if (operandType instanceof CArray) {
			operandValueType = ((CArray) operandType).getValueType().getUnderlyingType();
		} else {
			operandValueType = ((CPointer) operandType).getPointsToType().getUnderlyingType();
		}

		final CType castTargetValueType;
		if (castTargetType instanceof CArray) {
			castTargetValueType = ((CArray) castTargetType).getValueType().getUnderlyingType();
		} else {
			castTargetValueType = ((CPointer) castTargetType).getPointsToType().getUnderlyingType();
		}

		final Expression operandTypeByteSizeExp;
		try {
			operandTypeByteSizeExp = mTypeSizeComputer.constructBytesizeExpression(loc, operandValueType, node);
		} catch (final UnsupportedOperationException e) {
			mLogger.debug("saw a pointer cast to a type that we could not get a type size for, not adapting memory "
					+ "model");
			return;
		}
		final BigInteger operandTypeByteSize =
				mTypeSizes.extractIntegerValue(operandTypeByteSizeExp, mTypeSizeComputer.getSizeT(), node);

		final Expression castTargetByteSizeExp;
		try {
			castTargetByteSizeExp = mTypeSizeComputer.constructBytesizeExpression(loc, castTargetValueType, node);
		} catch (final UnsupportedOperationException e) {
			mLogger.debug("saw a pointer cast to a type that we could not get a type size for, not adapting memory "
					+ "model");
			return;
		}
		final BigInteger castTargetByteSize =
				mTypeSizes.extractIntegerValue(castTargetByteSizeExp, mTypeSizeComputer.getSizeT(), node);

		if (castTargetByteSize.compareTo(operandTypeByteSize) <= 0) {
			// type sizes are already compatible
			return;
		}

		final String msg;
		if (mSettings.getMemoryModelPreference() == MemoryModel.HoenickeLindenmann_Original) {
			// memory model has no resolution and the operand is
			// cast to a bigger type
			msg = "Found a cast between two array/pointer types where the value type is smaller than the "
					+ "cast-to type while using memory model " + MemoryModel.HoenickeLindenmann_Original;
		} else if (BigInteger.valueOf(mSettings.getMemoryModelPreference().getByteSize())
				.compareTo(operandTypeByteSize) > 0) {
			// memory model resolution is strictly bigger than the operand's type's, and the operand is
			// cast to a bigger type
			msg = "Found a cast between two array/pointer types where the value type is smaller than the"
					+ " cast-to type, and where that value type is smaller than our current memory "
					+ "model resolution";
		} else {
			// no need to change memory model
			return;
		}

		if (operandTypeByteSize.intValueExact() == 0) {
			// operand's type has size 0 -- not sure what makes sense to do here, doing nothing
			// case where I encountered it was a struct with a 0-sized array in it; if someone wants to read more on
			// that phenomenon:
			// https://stackoverflow.com/questions/52630441/c-struct-with-zero-sized-array-members
			return;
		}

		if (mLogger.isDebugEnabled()) {
			mLogger.debug(msg);
			mLogger.debug(" at location: " + loc);
			mLogger.debug(" current memory model: " + mSettings.getMemoryModelPreference());
		}
		// signal a restart of the translation with a memory model precise
		// enough for the operands
		signalTranslationRestartWithDifferentSettings(new TranslationSettings.SettingsChange(loc, msg,
				MemoryModel.getPreciseEnoughMemoryModelFor(operandTypeByteSize.intValueExact())));
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
		opCondition = mExprResultTransformer.switchToRValue(opCondition, loc, node);
		ExpressionResult opPositive = (ExpressionResult) main.dispatch(node.getPositiveResultExpression());
		opPositive = mExprResultTransformer.switchToRValue(opPositive, loc, node);
		ExpressionResult opNegative = (ExpressionResult) main.dispatch(node.getNegativeResultExpression());
		opNegative = mExprResultTransformer.switchToRValue(opNegative, loc, node);
		return mCExpressionTranslator.handleConditionalOperator(loc, opCondition, opPositive, opNegative, node);
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
		final boolean isOnHeap = isOnHeap(node);

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
					final ExpressionResult switched = mExprResultTransformer.switchToRValue(dispatched, loc, node);
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
			if (binding == null) {
				// this happens if the parent is actually a cast
				cType = CFunction.createEmptyCFunction().newReturnType(resType.getCType()).newParameter(paramsParsed);
			} else if (binding instanceof IProblemBinding) {
				// this happens if CDT detects a parse issue at this position
				mLogger.warn("Detected problem " + ((IProblemBinding) binding).getMessage() + " at " + loc);
				cType = CFunction.createEmptyCFunction().newReturnType(resType.getCType()).newParameter(paramsParsed);
			} else if (binding instanceof IFunction) {
				cType = CFunction.createCFunction(resType.getCType(), paramsParsed, (IFunction) binding);
			} else if (binding instanceof IVariable) {
				// it is a function pointer
				cType = CFunction.tryCreateCFunction(resType.getCType(), paramsParsed, (IVariable) binding);
			} else if (binding instanceof ITypedef) {
				// it is a typedef of a function pointer or a function
				cType = CFunction.tryCreateCFunction(resType.getCType(), paramsParsed, (ITypedef) binding);
			} else {
				throw new UnsupportedOperationException(
						"Cannot extract function type from binding " + binding.getClass());
			}
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
			cType = CFunction.createCFunction(resType.getCType(), paramsParsed,
					(IFunction) funcDecl.getName().getBinding());
			declName = mSymbolTable.applyMultiparseRenaming(node.getContainingFilename(), node.getName().toString());
		} else {
			cType = resType.getCType();
			declName = getNonFunctionDeclaratorName(node);
		}
		final int bitfieldSize;
		if (node instanceof IASTFieldDeclarator) {
			final IASTExpression expr = ((IASTFieldDeclarator) node).getBitFieldSize();
			final ExpressionResult res = (ExpressionResult) main.dispatch(expr);

			assert res.hasNoSideEffects() && res.hasLRValue() : "unexpected, todo: deal with sideeffects";

			final BigInteger bigIntExtracted = CTranslationUtil.extractIntegerValue(res.getLrValue().getValue());
			bitfieldSize = bigIntExtracted.intValueExact();
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

	private boolean isOnHeap(final IASTDeclarator node) {
		if (mIsPrerun) {
			return false;
		}
		if (mVariablesOnHeap.contains(node)) {
			return true;
		}
		final IBinding binding = node.getName().resolveBinding();
		if (binding instanceof CVariable) {
			final IASTNode[] decls = ((CVariable) binding).getDeclarations();
			// check if any of the declarations of this var are on heap, because then, all have to be on heap
			if (decls != null && decls.length > 0) {
				for (final IASTNode decl : decls) {
					if (decl == null) {
						// DD: Bug in CDT sometimes yields null in this array
						continue;
					}
					if (mVariablesOnHeap.contains(decl.getParent())) {
						return true;
					}
				}
			}
		}
		return false;
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

		if (mSymbolTable.containsCSymbol(node, cId)) {
			if (mProcedureManager.hasProcedure(cIdMp)) {
				mLogger.warn("Possible shadowing of function " + cId);
			}
			// a local variable
			final SymbolTableValue stv = mSymbolTable.findCSymbol(node, cId);
			bId = stv.getBoogieName();
			cType = stv.getCType();
			useHeap = isHeapVar(bId);
			intFromPtr = stv.isIntFromPointer();
			declarationInformation = stv.getDeclarationInformation();
		} else if (mSymbolTable.containsCSymbol(node, cIdMp)) {
			if (mProcedureManager.hasProcedure(cIdMp)) {
				mLogger.warn("Possible shadowing of function " + cId);
			}
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
		condResult = mExprResultTransformer.transformSwitchRexIntToBool(condResult, loc, node);
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

	public Result visit(final IDispatcher main, final IASTTypeIdInitializerExpression node) {
		// node represents a compound literal (something like "(int []) { 1, 2 }")
		final ILocation loc = mLocationFactory.createCLocation(node);

		// translate type
		final IASTTypeId typeId = node.getTypeId();
		final TypesResult declSpecifierResult = (TypesResult) main.dispatch(typeId.getDeclSpecifier());
		mCurrentDeclaredTypes.push(declSpecifierResult);
		final DeclaratorResult declaratorResult = (DeclaratorResult) main.dispatch(typeId.getAbstractDeclarator());
		mCurrentDeclaredTypes.pop();

		final CDeclaration cDeclaration = declaratorResult.getDeclaration();
		assert !cDeclaration.hasInitializer() : "unexpected, inspect this case";
		assert !cDeclaration.isOnHeap() : "unexpected, inspect this case";
		final CType cType = cDeclaration.getType().getUnderlyingType();

		// translate initializer
		final IASTInitializer initializer = node.getInitializer();
		final InitializerResult ir = (InitializerResult) main.dispatch(initializer);

		final boolean isAddressTaken = node.getParent() instanceof IASTUnaryExpression
				&& ((IASTUnaryExpression) node.getParent()).getOperator() == IASTUnaryExpression.op_amper;
		// catch simple case
		if (!isAddressTaken) {
			if (cType instanceof CPrimitive || cType instanceof CEnum) {
				final CPrimitive cPrim = (CPrimitive) cType;
				final ExpressionResult exprRes = mExprResultTransformer
						.switchToRValue(InitializerResult.getFirstValueInInitializer(ir), loc, node);
				assert exprRes.hasLRValue();
				final ExpressionResult converted =
						mExprResultTransformer.performImplicitConversion(exprRes, cType, loc);

				final RValue rVal = (RValue) converted.getLrValue();

				// used to check if rVal is a constant
				final BigInteger intVal = mTypeSizes.extractIntegerValue(rVal, node);

				if (converted.hasNoSideEffects() && intVal != null
						&& cPrim.getGeneralType() == CPrimitiveCategory.INTTYPE) {
					// ExpressionResult is just an integer constant
					return converted;
				}
			}
		}

		/*
		 * @formatter:off
		 * treat the general case
		 *  - introduce an auxiliary variable aux of type pointer
		 *    (c type: pointer to the type from the compound literal's type id)
		 *  - aux points to fresh memory
		 *  - the value of aux never changes and aux is associated with this compound literal
		 *  - set the contents of aux to the value of the initializer
		 *  - the scope of the compound literal depends on where it occurs, like for variable declarations
		 *  TODO:
		 *  - the const specifier is not supported at the moment
		 *    -- we would have to check that the compound literal's memory is not written to
		 *    -- we would have to account for possible sharing of memory between different compound literals, and
		 *      possibly string literals (right now, the addresses of distinct compound literals are guaranteed to be
		 *       distinct in our Boogie program, even if the compound literals have the same contents, this is unsound)
		 * @formatter:on
		 */

		/*
		 * find out the size of the memory block that the compound literal takes, there are two cases - incomplete array
		 * declarator: (e.g. (int [])): then the size depends on the initializer - otherwise: the size is given by the
		 * CType
		 */
		mTypeSizeComputer.constructBytesizeExpression(loc, cType, node);

		final ExpressionResultBuilder builder = new ExpressionResultBuilder();

		final CPointer pointerType = new CPointer(cType);

		// declare aux
		final AuxVarInfo aux;
		{

			/*
			 * note: it seems ok to make the aux declaration local to Ultimate.Init, since the compound literal cannot
			 * be from another point in the program. (this is in contrast e.g. to on heap variables, which aux is
			 * somewhat similar to)
			 */
			final DeclarationInformation declInfo =
					mProcedureManager.isGlobalScope() ? new DeclarationInformation(StorageClass.LOCAL, SFO.INIT)
							: new DeclarationInformation(StorageClass.LOCAL, mProcedureManager.getCurrentProcedureID());

			aux = mAuxVarInfoBuilder.constructAuxVarInfoForBlockScope(loc, pointerType, SFO.AUXVAR.COMPOUNDLITERAL,
					declInfo);
			builder.addDeclaration(aux.getVarDec());
			// do not add aux var to builder for havoccing here (havoccing is done after freeing at endScope
		}

		// add malloc/free
		{
			final LocalLValue llv = new LocalLValue(aux.getLhs(), cType, null);
			if (mProcedureManager.isGlobalScope()) {
				final CallStatement malloc = mMemoryHandler.getUltimateMemAllocCall(llv, loc, node, MemoryArea.STACK);
				mStaticObjectsHandler.addStatementsForUltimateInit(Collections.singletonList(malloc));

			} else {
				final LocalLValueILocationPair llvp = new LocalLValueILocationPair(llv, loc);
				// malloc auxvar; note that in contrast to on-heap variables, this malloc must only happen at the
				// beginning
				// of the scope, not each time the declaration point of the variable/this compound literal is reached
				mMemoryHandler.addVariableToBeMalloced(llvp);
				// schedule aux to be freed at scope end
				mMemoryHandler.addVariableToBeFreed(llvp);
			}
		}

		// write the contents of the compound literal to the memory location designated by aux
		final ExpressionResult initialization = mInitHandler.initialize(loc, aux.getLhs(), cType, ir, true, node);
		builder.addAllExceptLrValue(initialization);

		builder.setLrValue(LRValueFactory.constructHeapLValue(mTypeHandler, aux.getExp(), cType, null));

		return builder.build();
	}

	public Result visit(final IDispatcher main, final IASTInitializerClause node) {
		if (node.getChildren().length == 1) {
			final ExpressionResult rex = (ExpressionResult) main.dispatch(node.getChildren()[0]);
			return mExprResultTransformer.switchToRValue(rex, mLocationFactory.createCLocation(node), node);
		}
		throw new UnsupportedOperationException(
				"Cannot understand initializer that has more than two children." + node.getRawSignature());
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
				rex = mExprResultTransformer.transformDecaySwitch(rex, loc, node);
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
		case IASTLiteralExpression.lk_string_literal:
			return handleStringLiteralExpression(loc, main, node);
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

	private Result handleStringLiteralExpression(final ILocation loc, final IDispatcher main,
			final IASTLiteralExpression node) {
		// Note: We can either use loc here or create a new ignore-loc s.t. the string literal assignment will not be
		// shown in the backtranslation
		final ILocation actualLoc = LocationFactory.createIgnoreCLocation(node);

		final CStringLiteral stringLiteral = new CStringLiteral(node.getValue(), mTypeSizes.getSignednessOfChar());
		final int sizeInBytes = stringLiteral.getByteValues().size();
		final Expression sizeInBytesExpr = mTypeSizes.constructLiteralForIntegerType(actualLoc,
				mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.valueOf(sizeInBytes));

		final RValue auxVarRValue;
		final AuxVarInfo auxvar;

		final RValue dimension = new RValue(sizeInBytesExpr, mExpressionTranslation.getCTypeOfPointerComponents());
		final CArray arrayType = new CArray(dimension, new CPrimitive(CPrimitives.CHAR));
		final CPointer pointerType = new CPointer(new CPrimitive(CPrimitives.CHAR));
		auxvar = mAuxVarInfoBuilder.constructGlobalAuxVarInfo(actualLoc, pointerType, SFO.AUXVAR.STRINGLITERAL);
		auxVarRValue = new RValueForArrays(auxvar.getExp(), arrayType);
		// the declaration of the variable that corresponds to a string literal has to be made globally
		mStaticObjectsHandler.addGlobalVarDeclarationWithoutCDeclaration(auxvar.getVarDec());

		// overapproximate string literals of length STRING_OVERAPPROXIMATION_THRESHOLD or longer
		final boolean writeValues =
				stringLiteral.getByteValues().size() < ExpressionTranslation.STRING_OVERAPPROXIMATION_THRESHOLD;

		final List<Statement> statements = new ArrayList<>();
		final CallStatement ultimateAllocCall =
				mMemoryHandler.getUltimateMemAllocCall(sizeInBytesExpr, auxvar.getLhs(), actualLoc, MemoryArea.STACK);
		statements.add(ultimateAllocCall);

		if (writeValues) {
			final ExpressionResult exprRes =
					mInitHandler.writeStringLiteral(actualLoc, auxVarRValue, stringLiteral, node);
			assert !exprRes.hasLRValue();
			assert exprRes.getDeclarations().isEmpty();
			assert exprRes.getOverapprs().isEmpty();
			assert exprRes.getAuxVars().isEmpty();
			assert exprRes.getNeighbourUnionFields().isEmpty();
			statements.addAll(exprRes.getStatements());
		}
		mStaticObjectsHandler.addStatementsForUltimateInit(statements);

		final List<Overapprox> overapproxList;
		if (writeValues) {
			overapproxList = Collections.emptyList();
		} else {
			final Overapprox overapprox = new Overapprox("large string literal", actualLoc);
			overapproxList = new ArrayList<>();
			overapproxList.add(overapprox);
		}
		return new StringLiteralResult(auxVarRValue, overapproxList, auxvar, stringLiteral, !writeValues);
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
		for (final IASTDeclarator declarator : node.getDeclarators()) {
			final DeclaratorResult declResult = (DeclaratorResult) main.dispatch(declarator);
			final CDeclaration cDec = declResult.getDeclaration();
			cDec.setStorageClass(storageClass);

			// are we in prerun mode?
			if (mIsPrerun) {
				// all unions should be on heap
				if (CStructOrUnion.isUnion(cDec.getType().getUnderlyingType())
						&& storageClass != CStorageClass.TYPEDEF) {
					addToVariablesOnHeap(declarator.getName());
				}
			}

			if (cDec.getType() instanceof CFunction && storageClass != CStorageClass.TYPEDEF) {
				// update functionHandler.procedures instead of symbol table
				mFunctionHandler.handleFunctionDeclarator(main, mLocationFactory.createCLocation(declarator), mContract,
						cDec, declarator);
				continue;
			}
			intermediateResults.add(handleIASTDeclarator(main, loc, node, declResult, declarator, cDec, storageClass));
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
		ExpressionResult expr = mExprResultTransformer.switchToRValue((ExpressionResult) switchParam, loc,
				node.getControllerExpression());
		// 6.8.4.2-1: "The controlling expression of a switch statement shall have integer type."
		// note that this does not mean that it has "int" type, it may be long or char, for instance
		assert expr.getLrValue().getCType().isIntegerType();
		// 6.8.4.2-5: "The integer promotions are performed on the controlling
		// expression."
		expr = mExprResultTransformer.doIntegerPromotion(loc, expr);

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

		// NOTE: Hack for ACSL was removed; we should first process C and then ACSL.
		for (final IASTNode child : node.getChildren()) {
			// Ignore included declarations which might cause problems
			if (!child.isPartOfTranslationUnitFile()) {
				continue;
			}
			processTUchild(main, mDeclarations, child);
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
							mTypeSizeComputer.getSizeT()));
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
			final ExpressionResult rop = mExprResultTransformer.switchToRValue(operand, loc, node);
			return mCExpressionTranslator.handleUnaryArithmeticOperators(loc, node.getOperator(), rop, node);
		}
		case IASTUnaryExpression.op_postFixIncr:
		case IASTUnaryExpression.op_postFixDecr: {
			return mCExpressionTranslator.handlePostfixIncrementAndDecrement(loc, node.getOperator(), operand, node,
					a -> makeAssignment(loc, operand.getLrValue(), Collections.emptyList(), a, node));
		}
		case IASTUnaryExpression.op_prefixDecr:
		case IASTUnaryExpression.op_prefixIncr: {
			return mCExpressionTranslator.handlePrefixIncrementAndDecrement(node.getOperator(), loc, operand, node,
					a -> makeAssignment(loc, operand.getLrValue(), Collections.emptyList(), a, node));
		}
		case IASTUnaryExpression.op_bracketedPrimary:
			return operand;
		case IASTUnaryExpression.op_sizeof:
			final CType operandType = operand.getCType().getUnderlyingType();
			return new ExpressionResult(
					new RValue(mMemoryHandler.calculateSizeOf(loc, operandType, node), mTypeSizeComputer.getSizeT()),
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
		final ExpressionResult rhsConverted =
				mExprResultTransformer.performImplicitConversion(rhs, leftHandSide.getCType(), loc);
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
				rhsWithBitfieldTreatment = mExpressionTranslation.eraseBits(loc,
						rightHandSideValueWithConversionsApplied.getValue(),
						(CPrimitive) CEnum.replaceEnumWithInt(hlv.getCType().getUnderlyingType()), bitfieldWidth, hook);
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
								(CPrimitive) CEnum.replaceEnumWithInt(lValue.getCType().getUnderlyingType()),
								bitfieldWidth, hook);
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
			// TODO: DD 2020-12-02: havocing neighbours should only happen if the field is really on the stack -- it
			// seems that this cannot happen anymore
			// final ExpressionResultBuilder builderWithUnionFieldAndNeighboursUpdated =
			// assignOrHavocUnionNeighbours(loc,
			// (RValue) rhsConverted.getLrValue(), rhsConverted.getNeighbourUnionFields(),
			// rightHandSideValueWithConversionsApplied, builder, hook);
			// return builderWithUnionFieldAndNeighboursUpdated.build();
			return builder.build();
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
	 * @return true iff this is called while in prerun mode, false otherwise
	 */
	public void moveArrayAndStructIdsOnHeap(final ILocation loc, final CType underlyingType, final Expression expr,
			final Set<AuxVarInfo> auxVars, final IASTNode hook) {

		final IASTNode exprHook = CTranslationUtil.findExpressionHook(hook);

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
			final SymbolTableValue value = mSymbolTable.findCSymbol(exprHook, cid);
			if (value == null) {
				throw new AssertionError("no entry in symbol table for C-ID " + cid);
			}
			final CType type = value.getCType().getUnderlyingType();
			if (type instanceof CArray || type instanceof CStructOrUnion) {
				addToVariablesOnHeap(value.getDeclarationNode());
			}
		}
	}

	private boolean isReachable(final IASTDeclaration node) {
		return mReachableDeclarations == null || mReachableDeclarations.contains(node);
	}

	private void checkUnsupportedPointerCast(final ExpressionResult expr, final ILocation loc, final CType newCType) {
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
					identifier = ((CEnum) cDec.getType().getUnderlyingType()).getName();
				} else {
					throw new AssertionError(
							"missing support for global incomplete " + cDec.getType().getUnderlyingType());
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
					erb.addStatement(mMemoryHandler.getUltimateMemAllocCall(llVal, loc, node, MemoryArea.STACK));
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
					erb.addStatement(mMemoryHandler.getUltimateMemAllocCall(llVal, loc, node, MemoryArea.STACK));
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
			}
			// TODO: deal with other global ACSL stuff

		} else if (mAcsl.getSuccessorCNode() == null) {
			if (parent != null && compoundStatement && next == null) {
				// ACSL at the end of a function or at the end of the last statement in a switch
				// that is not terminated by a break
				// TODO: the latter case needs fixing, the ACSL is inserted outside the
				// corresponding if-scope right now
				// example: int s = 1; switch (s) { case 0: s++; //@ assert \false; } will yield
				// a unsafe boogie program
				for (final ACSLNode acslNode : mAcsl.getAcsl()) {
					final int parentLineEnd = parent.getFileLocation().getEndingLineNumber();
					final int aclsLineStart = acslNode.getStartingLineNumber();
					if (parentLineEnd <= aclsLineStart) {
						// handle later ...
						return;
					}
					final int parentLineStart = parent.getFileLocation().getStartingLineNumber();
					final int acslLineEnd = acslNode.getEndingLineNumber();
					if (parentLineEnd < acslLineEnd || parentLineStart > aclsLineStart) {
						// TODO: DD: It seems strange that we may skip a single acslNode in this case
						continue;
					}

					final Result acslResult = main.dispatch(acslNode, parent);
					if (acslResult instanceof ExpressionResult) {
						resultBuilder.addDeclarations(((ExpressionResult) acslResult).getDeclarations());
						resultBuilder.addStatements(((ExpressionResult) acslResult).getStatements());
						resultBuilder.addStatements(
								CTranslationUtil.createHavocsForAuxVars(((ExpressionResult) acslResult).getAuxVars()));

					} else {
						final String msg = "Unexpected ACSL comment: " + acslResult.getNode().getClass();
						final ILocation loc = mLocationFactory.createCLocation(parent);
						throw new IncorrectSyntaxException(loc, msg);
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

				if (cd.getType().isIncomplete() && !cd.isOnHeap()) {
					/*
					 * type of this (variable) declaration is incomplete at the end of the file -- omit the declaration
					 * from Boogie program
					 *
					 * EDIT (alex Nov '18): additional constraint for omission: only omit if object is not on heap. If
					 * it is on heap, then the corresponding pointer may still be used, even if the type is never
					 * completed (if the declaration has storage class extern).
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
		final ExpressionResult rop = mExprResultTransformer.makeRepresentationReadyForConversion(expr, loc,
				new CPointer(new CPrimitive(CPrimitives.VOID)), hook);
		final RValue rValue = (RValue) rop.getLrValue();
		if (!(rValue.getCType().getUnderlyingType() instanceof CPointer)) {
			throw new IllegalArgumentException("dereference needs pointer but got " + rValue.getCType());
		}
		final CPointer pointer = (CPointer) rValue.getCType().getUnderlyingType();
		final CType pointedType = pointer.getPointsToType();
		if (pointedType.isIncomplete()) {
			return new ExpressionWithIncompleteTypeResult(rop.getStatements(),
					LRValueFactory.constructHeapLValue(mTypeHandler, rValue.getValue(), pointedType, null),
					rop.getDeclarations(), rop.getAuxVars(), rop.getOverapprs());

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

		condResult = mExprResultTransformer.transformSwitchRexIntToBool(condResult, loc, node);
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
			if (node instanceof IASTForStatement || node instanceof IASTWhileStatement
					|| node instanceof IASTDoStatement) {
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

}
