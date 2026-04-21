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
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
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
import org.eclipse.cdt.core.dom.ast.c.ICASTDesignatedInitializer;
import org.eclipse.cdt.core.dom.ast.gnu.IGNUASTCompoundStatementExpression;
import org.eclipse.cdt.core.dom.ast.gnu.c.ICASTKnRFunctionDeclarator;
import org.eclipse.cdt.internal.core.dom.parser.c.ICInternalBinding;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieUtils;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieVariableCollector;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.annotation.LTLPropertyCheck;
import de.uni_freiburg.informatik.ultimate.boogie.annotation.LTLPropertyCheck.CheckableExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AtomicStatement;
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
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.TypeDeclaration;
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
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.IMemoryPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.InitializationHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.LocalLValueILocationPair;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryArea;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.PostProcessor;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.ProcedureManager;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.StaticObjectsHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.StructHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizeAndOffsetComputer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.InterruptPostProcessorHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.library.AssertLibraryModel;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.library.AtomicLibraryModel;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.library.FenvLibraryModel;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.library.FunctionModelHelper;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.library.GccBuiltinLibraryModel;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.library.ILibraryModel;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.library.LibraryModelHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.library.LimitsLibraryModel;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.library.LinuxLibraryModel;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.library.MathLibraryModel;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.library.PthreadLibraryModel;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.library.SetjmpLibraryModel;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.library.SocketLibraryModel;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.library.StdboolLibraryModel;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.library.StdintLibraryModel;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.library.StdioLibraryModel;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.library.StdlibLibraryModel;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.library.StringLibraryModel;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.library.SvcompLibraryModel;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.library.TimeLibraryModel;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.library.VariadicLibraryModel;
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
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.ICType;
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
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultWithSideEffects;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.SkipResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.StringLiteralResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.TypesResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.CdtASTUtils;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO.AUXVAR;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.INameHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.OverapproxVariable;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.CodeAnnot;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.CodeAnnotStmt;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.CodeStatement;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Contract;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.GlobalGhostDeclaration;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.GlobalLTLInvariant;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.ICACSL2BoogieBacktranslatorMapping;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.LTLExpressionExtractor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.MemoryStructure;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
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

	private static final boolean ADD_HAVOCS_AT_SCOPE_END = true;

	/**
	 * We translate a string literal to the pointer variable that points to the address where the string is stored. If
	 * this flag is set we add an overapproximation flag to this variable if it refers to a large string literal. <br />
	 * This is required for soundness because we omit the initialization of large string literals. A setting determine
	 * the size from which a string is "large".
	 */
	private static final boolean OVERAPPROX_FLAG_LARGE_STRING_LITERAL = false;

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
	private final Deque<Optional<String>> mInnerMostLoopLabel;

	private final ILogger mLogger;

	private final List<LTLExpressionExtractor> mGlobAcslExtractors;
	private final LibraryModelHandler mLibraryModelHandler;

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

	private final Set<String> mFunctions;

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
	 * Set this flag if you want to trigger a restart of the translation with different settings
	 */
	private boolean mRestartTranslationWithDifferentSettings;

	private TranslationSettings.SettingsChange mSettingsChangeForTranslationRestart;

	private final CExpressionTranslator mCExpressionTranslator;

	private final DataRaceChecker mDataRaceChecker;

	private final boolean mIsInLibraryMode;

	private boolean mIsConcurrent;
	private boolean mHasThreadLocalVars;

	private final IMemoryPointer mMemoryPointer;

	/**
	 * Constructor for CHandler in pre-run mode.
	 *
	 * @param staticObjectsHandler
	 * @param functions
	 * @param set
	 *
	 */
	public CHandler(final ILogger logger, final ICACSL2BoogieBacktranslatorMapping backtranslator,
			final TranslationSettings settings, final FlatSymbolTable symbolTable,
			final Map<String, IASTNode> functionTable, final ExpressionTranslation exprTrans,
			final LocationFactory locationFactory, final TypeSizes typeSizes,
			final Set<IASTDeclaration> reachableDeclarations, final ITypeHandler typeHandler,
			final CTranslationResultReporter reporter, final INameHandler nameHandler,
			final StaticObjectsHandler staticObjectsHandler, final Set<String> functions,
			final IMemoryPointer pointer) {
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
		mMemoryPointer = pointer;

		mFunctions = new LinkedHashSet<>(functions);
		mVariablesOnHeap = new LinkedHashSet<>();

		mContract = new ArrayList<>();
		mInnerMostLoopLabel = new ArrayDeque<>();
		mBoogieIdsOfHeapVars = new LinkedHashSet<>();
		mCurrentDeclaredTypes = new ArrayDeque<>();
		mGlobAcslExtractors = new ArrayList<>();
		mDeclarations = new ArrayList<>();

		mTypeSizeComputer = new TypeSizeAndOffsetComputer(mTypeSizes, mExpressionTranslation, mTypeHandler,
				mSettings.useBitpreciseBitfields());

		// the procedure manager has to be replaced between pre-run and main run
		// the following fields form the transitive dependency hull on the procedure
		// manager
		mProcedureManager = new ProcedureManager(mLogger, settings);

		mAuxVarInfoBuilder = new AuxVarInfoBuilder(mNameHandler, mTypeHandler, mProcedureManager);
		mMemoryHandler = new MemoryHandler(mTypeSizes, mNameHandler, settings.useSmtBoolArrayWorkaround(), mTypeHandler,
				mExpressionTranslation, mProcedureManager, mTypeSizeComputer, mAuxVarInfoBuilder, mSettings,
				mMemoryPointer);

		mStructHandler = new StructHandler(mMemoryHandler, mTypeSizeComputer, mExpressionTranslation, mTypeHandler,
				mLocationFactory);
		mDataRaceChecker =
				mSettings.checkDataRaces()
						? new DataRaceChecker(mAuxVarInfoBuilder, mMemoryHandler, mTypeHandler, mTypeSizeComputer,
								mTypeSizes, mProcedureManager, mExpressionTranslation.getFunctionDeclarations())
						: null;
		mExprResultTransformer =
				new ExpressionResultTransformer(this, mMemoryHandler, mStructHandler, mExpressionTranslation,
						mTypeSizes, mAuxVarInfoBuilder, mTypeHandler, mTypeSizeComputer, mDataRaceChecker);
		mFunctionHandler = new FunctionHandler(mLogger, mNameHandler, mExpressionTranslation, mProcedureManager,
				mTypeHandler, mReporter, mAuxVarInfoBuilder, this, mLocationFactory, mSymbolTable,
				mExprResultTransformer, mVariablesOnHeap, mMemoryPointer);
		mArrayHandler = new ArrayHandler(mSettings, mExpressionTranslation, mTypeHandler, mTypeSizes,
				mExprResultTransformer, mMemoryHandler, mLocationFactory);
		mInitHandler = new InitializationHandler(mSettings, mMemoryHandler, mExpressionTranslation, mTypeHandler,
				mAuxVarInfoBuilder, mTypeSizeComputer, mTypeSizes, this, mExprResultTransformer, mMemoryPointer);
		mCExpressionTranslator = new CExpressionTranslator(mSettings, mMemoryHandler, mExpressionTranslation,
				mExprResultTransformer, mAuxVarInfoBuilder, mTypeSizes, mStaticObjectsHandler, mMemoryPointer);
		mLibraryModelHandler = new LibraryModelHandler(mLogger, functionTable, mSymbolTable,
				mSettings.checkErrorFunction(), mLocationFactory, getLibraryModels());
		mTypeHandler.addLibraryTypes(mLibraryModelHandler.getTypeModels());

		mPostProcessor = new PostProcessor(mLogger, mExpressionTranslation, mTypeHandler, mReporter, mAuxVarInfoBuilder,
				mFunctions, mTypeSizes, mSymbolTable, mStaticObjectsHandler, mSettings, mProcedureManager,
				mMemoryHandler, mInitHandler, mFunctionHandler, this);

		mIsInLibraryMode = false;
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

		// reuse these parts of the old CHandler that have state that was created during
		// the prerun
		mVariablesOnHeap = prerunCHandler.mVariablesOnHeap;
		mFunctions = prerunCHandler.mFunctions;
		mBacktranslator = prerunCHandler.mBacktranslator;
		mLocationFactory = prerunCHandler.mLocationFactory;
		mMemoryPointer = prerunCHandler.mMemoryPointer;

		// reuse these parts of the old CHandler that do not have state that was created
		// during the prerun
		mLogger = prerunCHandler.mLogger;
		mSettings = prerunCHandler.mSettings;
		mReachableDeclarations = prerunCHandler.mReachableDeclarations;
		mReporter = prerunCHandler.mReporter;

		// we need to replace the name handler and all instances that depend on it
		mNameHandler = nameHandler;
		mSymbolTable = symbolTable;
		mTypeSizes = typeSizes;

		// we need to replace the static objects handler and all instances that depend
		// on it
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
		mDataRaceChecker =
				mSettings.checkDataRaces()
						? new DataRaceChecker(mAuxVarInfoBuilder, mMemoryHandler, mTypeHandler, mTypeSizeComputer,
								mTypeSizes, mProcedureManager, mExpressionTranslation.getFunctionDeclarations())
						: null;
		mExprResultTransformer =
				new ExpressionResultTransformer(this, mMemoryHandler, mStructHandler, mExpressionTranslation,
						mTypeSizes, mAuxVarInfoBuilder, mTypeHandler, mTypeSizeComputer, mDataRaceChecker);
		mFunctionHandler = new FunctionHandler(mLogger, mNameHandler, mExpressionTranslation, procedureManager,
				mTypeHandler, mReporter, mAuxVarInfoBuilder, this, mLocationFactory, mSymbolTable,
				mExprResultTransformer, mVariablesOnHeap, mMemoryPointer);
		mArrayHandler = new ArrayHandler(mSettings, mExpressionTranslation, mTypeHandler, mTypeSizes,
				mExprResultTransformer, mMemoryHandler, mLocationFactory);
		mInitHandler = new InitializationHandler(mSettings, mMemoryHandler, mExpressionTranslation, mTypeHandler,
				mAuxVarInfoBuilder, mTypeSizeComputer, mTypeSizes, this, mExprResultTransformer, mMemoryPointer);

		mCExpressionTranslator = new CExpressionTranslator(mSettings, mMemoryHandler, mExpressionTranslation,
				mExprResultTransformer, mAuxVarInfoBuilder, mTypeSizes, mStaticObjectsHandler, mMemoryPointer);
		mLibraryModelHandler = new LibraryModelHandler(mLogger, prerunCHandler.mFunctionTable, mSymbolTable,
				mSettings.checkErrorFunction(), mLocationFactory, getLibraryModels());
		mTypeHandler.addLibraryTypes(mLibraryModelHandler.getTypeModels());
		mPostProcessor = new PostProcessor(mLogger, mExpressionTranslation, mTypeHandler, mReporter, mAuxVarInfoBuilder,
				mFunctions, mTypeSizes, mSymbolTable, mStaticObjectsHandler, mSettings, procedureManager,
				mMemoryHandler, mInitHandler, mFunctionHandler, this);
		mIsInLibraryMode = !prerunCHandler.mProcedureManager.hasProcedure(mSettings.getEntryFunction());
		copyGlobalsFromPrerun(prerunCHandler.mSymbolTable);
	}

	private void copyGlobalsFromPrerun(final FlatSymbolTable prerunSymbolTable) {
		final ASTType pointerType = mTypeHandler.constructPointerType(null);
		for (final var entry : prerunSymbolTable.getGlobalScope().entrySet()) {
			final String id = entry.getKey();
			final SymbolTableValue oldStv = entry.getValue();
			final IASTNode hook = oldStv.getDeclarationNode();
			final SymbolTableValue stv;
			if (mVariablesOnHeap.contains(hook)) {
				// Create a new pointer value
				final CDeclaration oldDecl = oldStv.getCDecl();
				// This is just required for ACSL, so we can ommit the Boogie-declaration and the initializers
				final CDeclaration newDecl = new CDeclaration(oldDecl.getType(), oldDecl.getName(), null, null, true,
						oldDecl.getStorageClass(), oldDecl.getBitfieldSize());
				final String bId = mNameHandler.getUniqueIdentifier(hook, oldDecl.getName(), 1, true, oldDecl.getType(),
						oldStv.getDeclarationInformation());
				stv = new SymbolTableValue(bId, null, pointerType, newDecl, oldStv.getDeclarationInformation(), hook,
						false);
				addBoogieIdsOfHeapVars(bId);
			} else {
				// Copy the old value to the symbol table
				stv = oldStv;
			}
			mSymbolTable.storeCSymbol(hook, id, stv);
		}
	}

	private List<ILibraryModel> getLibraryModels() {
		final FunctionModelHelper helper =
				new FunctionModelHelper(mAuxVarInfoBuilder, mExpressionTranslation, mMemoryHandler, mTypeSizes,
						mTypeHandler, mSettings.getFunctionsCheckedForMemoryNeutrality().contains("main"),
						mSettings.isSvcompMemtrackCompatibilityMode(), mMemoryPointer);

		return List.of(new AssertLibraryModel(helper, mExprResultTransformer, mSettings.checkAssertions()),
				new AtomicLibraryModel(helper, mExprResultTransformer, mExpressionTranslation, mAuxVarInfoBuilder),
				new FenvLibraryModel(helper, mExprResultTransformer, mExpressionTranslation, mAuxVarInfoBuilder),
				new GccBuiltinLibraryModel(helper, mExprResultTransformer, mExpressionTranslation, mAuxVarInfoBuilder,
						mMemoryHandler, mTypeSizeComputer),
				new LinuxLibraryModel(helper, mAuxVarInfoBuilder, mExprResultTransformer, mTypeSizes,
						mExpressionTranslation),
				new MathLibraryModel(helper, mExprResultTransformer, mExpressionTranslation, mCExpressionTranslator,
						mNameHandler, mAuxVarInfoBuilder),
				new PthreadLibraryModel(helper, mSymbolTable, mAuxVarInfoBuilder, mExprResultTransformer,
						mExpressionTranslation, mMemoryHandler, mTypeHandler, mTypeSizes, mProcedureManager,
						mMemoryPointer),
				new SetjmpLibraryModel(helper, mExpressionTranslation), new SocketLibraryModel(helper),
				new StdioLibraryModel(helper, mExprResultTransformer, mAuxVarInfoBuilder, mExpressionTranslation,
						mTypeSizes, mMemoryHandler, mDataRaceChecker, mTypeHandler),
				new StdlibLibraryModel(helper, mExprResultTransformer, mTypeSizes, mTypeSizeComputer,
						mExpressionTranslation, mAuxVarInfoBuilder, mMemoryHandler, mProcedureManager, mNameHandler,
						mSettings.checkSignedIntegerBounds()),
				new StringLibraryModel(helper, mExprResultTransformer, mAuxVarInfoBuilder, mMemoryHandler,
						mProcedureManager, mExpressionTranslation, mTypeSizeComputer, mMemoryPointer),
				new SvcompLibraryModel(helper, mAuxVarInfoBuilder, mExpressionTranslation, mNameHandler,
						mSettings.checkErrorFunction(), mExprResultTransformer),
				new TimeLibraryModel(helper, mExpressionTranslation, mAuxVarInfoBuilder),
				new VariadicLibraryModel(helper, mMemoryHandler, mProcedureManager, mTypeHandler,
						mExprResultTransformer, mExpressionTranslation, mAuxVarInfoBuilder),
				new StdintLibraryModel(), new LimitsLibraryModel(mTypeSizes, helper), new StdboolLibraryModel(helper));
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
		final List<Statement> additionalInitializations = handleWitnessDeclarations(main);
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
		int offset = 0;
		for (final String f : mFunctions) {
			final String funcId = SFO.FUNCTION_ADDRESS + f;
			final VarList varList = new VarList(loc, new String[] { funcId }, mTypeHandler.constructPointerType(loc));
			// would unique make sense here?? -- would potentially add lots of axioms
			mDeclarations.add(new ConstDeclaration(loc, new Attribute[0], false, varList, null, false));

			final Expression funcIdExpr = ExpressionFactory.constructIdentifierExpression(loc,
					mTypeHandler.getBoogiePointerType(), funcId, DeclarationInformation.DECLARATIONINFO_GLOBAL);

			final BigInteger offsetValue = BigInteger.valueOf(offset);
			final var funcPtr = mMemoryHandler.createFunctionPointer(loc, offsetValue);

			mDeclarations.add(new Axiom(loc, new Attribute[0],
					ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ, funcIdExpr, funcPtr)));

			offset++;
		}

		if (!mIsPrerun) {
			// S2S transformation of interrupt programs to thread-based programs if enabled
			final var interruptPostProcessor = getInterruptPostProcessorHandler();
			mDeclarations.addAll(interruptPostProcessor.postProcess(loc, globalHook, additionalInitializations));
			additionalInitializations.addAll(interruptPostProcessor.getAdditionalInitializations());
		}

		mDeclarations.addAll(0, mPostProcessor.postProcess(loc, globalHook, additionalInitializations));

		/*
		 * this must come after the post processor because the post processor might add declarations when dispatching
		 * initializers of static variables
		 */
		mDeclarations.addAll(mStaticObjectsHandler.getGlobalDeclarations());

		// this has to happen after postprocessing as pping may add sizeof
		// constants for initializations
		mDeclarations.addAll(mTypeSizeComputer.getConstants());
		mDeclarations.addAll(mTypeSizeComputer.getAxioms());
		mDeclarations.addAll(mMemoryHandler.declareMemoryStructureInfrastructure(this, loc, mDataRaceChecker));

		if (mDataRaceChecker != null) {
			mDeclarations.addAll(mDataRaceChecker.declareRaceCheckingInfrastructure(loc));
		}

		// add type declarations introduced by the translation, e.g., $Pointer$
		mDeclarations.add(mMemoryPointer.getTypeDeclaration(loc));

		/**
		 * For Notes on our handling of procedures see {@link FunctionHandler.handleFunctionDefinition(..)}. Short
		 * version:
		 * <li>procedure implementations have already been inserted into the Boogie program by code above
		 * <li>procedure declarations have been collected in the ProcedureManager
		 * <li>now we recompute the declarations, in order to give them correct modifies clauses and insert them into
		 * the Boogie program
		 *
		 * have to block this in prerun, because there, Memory Structure is not declared which may cause problems with
		 * the call graph computation
		 */
		if (!mIsPrerun) {
			// handle proc. declaration & resolve their transitive modified globals
			mDeclarations.addAll(mProcedureManager.computeFinalProcedureDeclarations(mMemoryHandler));
			mDeclarations.addAll(
					mFunctionHandler.handleFunctionsWithoutDefinitions(mSettings.getUndefinedFunctionBehaviour()));
		}

		final IASTTranslationUnit hook = units.get(0).getSourceTranslationUnit();
		final List<LTLPropertyCheck> propChecks = new ArrayList<>();
		// annotate the Unit with LTLPropertyChecks if applicable
		for (final LTLExpressionExtractor ex : mGlobAcslExtractors) {
			final Map<String, LTLPropertyCheck.CheckableExpression> checkableAtomicPropositions = new LinkedHashMap<>();

			for (final Entry<String, de.uni_freiburg.informatik.ultimate.model.acsl.ast.Expression> en : ex
					.getAP2SubExpressionMap().entrySet()) {
				final ExpressionResult r = (ExpressionResult) main.dispatch(en.getValue(), hook);
				// TODO: some switchToRValue and handling of sideeffects?
				checkableAtomicPropositions.put(en.getKey(), new CheckableExpression(r.getLrValue().getValue(), null));
			}
			propChecks.add(new LTLPropertyCheck(ex.getLTLFormatString(), checkableAtomicPropositions, null));
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
						units.stream().map(DecoratedUnit::getSourceTranslationUnit).collect(Collectors.toSet())),
				mDeclarations.toArray(new Declaration[mDeclarations.size()]));
		propChecks.forEach(x -> x.annotate(boogieUnit));
		return new CHandlerTranslationResult(boogieUnit, mSymbolTable.getBoogieCIdentifierMapping());
	}

	private InterruptPostProcessorHandler getInterruptPostProcessorHandler() {
		return new InterruptPostProcessorHandler(mLogger, mSymbolTable, mSettings, mProcedureManager, this,
				mAuxVarInfoBuilder, mExpressionTranslation, mDeclarations);
	}

	private List<Statement> handleWitnessDeclarations(final IDispatcher dispatcher) {
		final List<Statement> result = new ArrayList<>();
		for (final var ghost : dispatcher.getWitnessDeclarations()) {
			final ExpressionResult exprRes = ghost.getInitializationResult(dispatcher);
			// Collect all statement for initialization to return them and add in PostProcessor
			result.addAll(exprRes.getStatements());
			result.addAll(CTranslationUtil.createHavocsForAuxVars(exprRes.getAuxVars()));
			// Add the declaration of global ghost variables (and possible auxiliary variables)
			for (final var d : exprRes.getDeclarations()) {
				mStaticObjectsHandler.addGlobalVarDeclarationWithoutCDeclaration((VariableDeclaration) d);
			}
			mStaticObjectsHandler.addGlobalVarDeclarationWithoutCDeclaration(ghost.getDeclaration(mSymbolTable));
		}
		return result;
	}

	public Result visit(final IDispatcher main, final ICASTDesignatedInitializer node) {
		return mInitHandler.handleDesignatedInitializer(main, mLocationFactory, node);
	}

	public Result visit(final IDispatcher main, final IASTArraySubscriptExpression node) {
		final ILocation loc = mLocationFactory.createCLocation(node);
		final ExpressionResult array = (ExpressionResult) main.dispatch(node.getArrayExpression());
		final ExpressionResult subscript =
				mExprResultTransformer.transformDispatchSwitchRexBoolToInt(main, loc, node.getArgument());
		return handleArraySubscriptExpression(array, subscript, node);
	}

	public ExpressionResult handleArraySubscriptExpression(final ExpressionResult array,
			final ExpressionResult subscript, final IASTNode hook) {
		return mArrayHandler.handleArraySubscriptExpression(array, subscript, hook);
	}

	public Result visit(final IDispatcher main, final IASTASMDeclaration node) {
		mReporter.warn(mLocationFactory.createCLocation(node), "Ignoring inline assembler instruction");
		return new SkipResult();
	}

	public Result visit(final IDispatcher main, final IASTBinaryExpression node) {
		final ILocation loc = mLocationFactory.createCLocation(node);
		final ExpressionResult leftOperand = (ExpressionResult) main.dispatch(node.getOperand1());
		final ExpressionResult rightOperand = (ExpressionResult) main.dispatch(node.getOperand2());
		// with binary expression, we check bitwise operator first
		switch (node.getOperator()) {
		case IASTBinaryExpression.op_assign: {
			final ExpressionResultBuilder builder = new ExpressionResultBuilder();
			builder.addAllExceptLrValue(leftOperand);
			final ICType lType = leftOperand.getLrValue().getCType().getUnderlyingType();
			final ExpressionResult rightOperandSwitched = mExprResultTransformer
					.makeRepresentationReadyForConversionAndRexBoolToInt(rightOperand, loc, lType, node);
			builder.addAllIncludingLrValue(rightOperandSwitched);
			return makeAssignment(loc, leftOperand.getLrValue(), leftOperand.getNeighbourUnionFields(), builder.build(),
					node);
		}
		case IASTBinaryExpression.op_equals:
		case IASTBinaryExpression.op_notequals: {
			final ExpressionResult rl = mExprResultTransformer.transformDecaySwitchRexBoolToInt(leftOperand, loc, node);
			final ExpressionResult rr =
					mExprResultTransformer.transformDecaySwitchRexBoolToInt(rightOperand, loc, node);
			return mCExpressionTranslator.handleEqualityOperators(loc, node.getOperator(), rl, rr);
		}
		case IASTBinaryExpression.op_greaterEqual:
		case IASTBinaryExpression.op_greaterThan:
		case IASTBinaryExpression.op_lessEqual:
		case IASTBinaryExpression.op_lessThan: {
			final ExpressionResult rl = mExprResultTransformer.switchToRValue(leftOperand, loc, node);
			final ExpressionResult rr = mExprResultTransformer.switchToRValue(rightOperand, loc, node);
			return mCExpressionTranslator.handleRelationalOperators(loc, node.getOperator(), rl, rr);
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
			return mCExpressionTranslator.handleMultiplicativeOperation(loc, node.getOperator(), rl, rr);
		}
		case IASTBinaryExpression.op_moduloAssign:
		case IASTBinaryExpression.op_multiplyAssign:
		case IASTBinaryExpression.op_divideAssign: {
			final ExpressionResult rl = mExprResultTransformer.transformSwitchRexBoolToInt(leftOperand, loc, node);
			final ExpressionResult rr = mExprResultTransformer.transformSwitchRexBoolToInt(rightOperand, loc, node);
			final ExpressionResult result =
					mCExpressionTranslator.handleMultiplicativeOperation(loc, node.getOperator(), rl, rr);
			// Make sure that the evaluation of the operands is not inside an atomic block, but the read of the left
			// operand (i.e., the potential of a heap variable) is.
			final List<Statement> statementsBeforeRead =
					DataStructureUtils.concat(leftOperand.getStatements(), rr.getStatements());
			return handleAtomicReadWrite(loc, leftOperand.getLrValue(), statementsBeforeRead, result, node);
		}
		case IASTBinaryExpression.op_plus:
		case IASTBinaryExpression.op_minus: {
			assert checkSubstractPointerArith(node, leftOperand, rightOperand)
					: "subtraction is not allowed in pointer arithmetic, right?";

			// if we are "adding" arrays, they must be treated as pointers
			final ExpressionResult rl = mExprResultTransformer.transformDecaySwitchRexBoolToInt(leftOperand, loc, node);
			final ExpressionResult rr =
					mExprResultTransformer.transformDecaySwitchRexBoolToInt(rightOperand, loc, node);

			return mCExpressionTranslator.handleAdditiveOperation(loc, node.getOperator(), rl, rr);
		}
		case IASTBinaryExpression.op_plusAssign:
		case IASTBinaryExpression.op_minusAssign: {
			assert checkSubstractPointerArith(node, leftOperand, rightOperand)
					: "subtraction is not allowed in pointer arithmetic, right?";

			final ExpressionResult rl = mExprResultTransformer.transformDecaySwitchRexBoolToInt(leftOperand, loc, node);
			final ExpressionResult rr =
					mExprResultTransformer.transformDecaySwitchRexBoolToInt(rightOperand, loc, node);
			final ExpressionResult result =
					mCExpressionTranslator.handleAdditiveOperation(loc, node.getOperator(), rl, rr);
			// Make sure that the evaluation of the operands is not inside an atomic block, but the read of the left
			// operand (i.e., the potential of a heap variable) is.
			final List<Statement> statementsBeforeRead =
					DataStructureUtils.concat(leftOperand.getStatements(), rr.getStatements());
			return handleAtomicReadWrite(loc, leftOperand.getLrValue(), statementsBeforeRead, result, node);
		}
		case IASTBinaryExpression.op_binaryAnd:
		case IASTBinaryExpression.op_binaryOr:
		case IASTBinaryExpression.op_binaryXor:
			return handleBitwiseOperation(node, loc, leftOperand, rightOperand);
		case IASTBinaryExpression.op_binaryAndAssign:
		case IASTBinaryExpression.op_binaryOrAssign:
		case IASTBinaryExpression.op_binaryXorAssign: {
			final ExpressionResult rl = mExprResultTransformer.transformSwitchRexBoolToInt(leftOperand, loc, node);
			final ExpressionResult rr = mExprResultTransformer.transformSwitchRexBoolToInt(rightOperand, loc, node);
			final ExpressionResult result =
					mCExpressionTranslator.handleBitwiseArithmeticOperation(loc, node.getOperator(), rl, rr);
			// Make sure that the evaluation of the operands is not inside an atomic block, but the read of the left
			// operand (i.e., the potential of a heap variable) is.
			final List<Statement> statementsBeforeRead =
					DataStructureUtils.concat(leftOperand.getStatements(), rr.getStatements());
			return handleAtomicReadWrite(loc, leftOperand.getLrValue(), statementsBeforeRead, result, node);
		}
		case IASTBinaryExpression.op_shiftLeft:
		case IASTBinaryExpression.op_shiftRight: {
			final ExpressionResult rl = mExprResultTransformer.transformSwitchRexBoolToInt(leftOperand, loc, node);
			final ExpressionResult rr = mExprResultTransformer.transformSwitchRexBoolToInt(rightOperand, loc, node);
			return mCExpressionTranslator.handleBitshiftOperation(loc, node.getOperator(), rl, rr);

		}
		case IASTBinaryExpression.op_shiftLeftAssign:
		case IASTBinaryExpression.op_shiftRightAssign: {
			final ExpressionResult rl = mExprResultTransformer.transformSwitchRexBoolToInt(leftOperand, loc, node);
			final ExpressionResult rr = mExprResultTransformer.transformSwitchRexBoolToInt(rightOperand, loc, node);
			final ExpressionResult result =
					mCExpressionTranslator.handleBitshiftOperation(loc, node.getOperator(), rl, rr);
			// Make sure that the evaluation of the operands is not inside an atomic block, but the read of the left
			// operand (i.e., the potential of a heap variable) is.
			final List<Statement> statementsBeforeRead =
					DataStructureUtils.concat(leftOperand.getStatements(), rr.getStatements());
			return handleAtomicReadWrite(loc, leftOperand.getLrValue(), statementsBeforeRead, result, node);
		}
		default:
			final String msg = "Unknown or unsupported unary operation";
			throw new UnsupportedSyntaxException(loc, msg);
		}
	}

	private ExpressionResult handleBitwiseOperation(final IASTBinaryExpression node, final ILocation loc,
			final ExpressionResult leftOperand, final ExpressionResult rightOperand) {
		// If the left operand and the right operand are both bools, simply translate it to a boolean expression.
		if (leftOperand.getLrValue().isBoogieBool() && rightOperand.getLrValue().isBoogieBool()) {
			final ExpressionResultBuilder builder = new ExpressionResultBuilder();
			final ExpressionResult rl = mExprResultTransformer.switchToRValue(leftOperand, loc, node);
			final ExpressionResult rr = mExprResultTransformer.switchToRValue(rightOperand, loc, node);
			builder.addAllExceptLrValue(rl, rr);
			Operator operator;
			switch (node.getOperator()) {
			case IASTBinaryExpression.op_binaryAnd:
				operator = Operator.LOGICAND;
				break;
			case IASTBinaryExpression.op_binaryOr:
				operator = Operator.LOGICOR;
				break;
			case IASTBinaryExpression.op_binaryXor:
				operator = Operator.COMPNEQ;
				break;
			default:
				throw new AssertionError("Unexpected operator " + node.getOperator());
			}
			final Expression leftValue = rl.getLrValue().getValue();
			final Expression rightValue = rr.getLrValue().getValue();
			final Expression resultExpr = ExpressionFactory.newBinaryExpression(loc, operator, leftValue, rightValue);
			return builder.setLrValue(new RValue(resultExpr, new CPrimitive(CPrimitive.CPrimitives.INT), true)).build();
		}
		final ExpressionResult rl = mExprResultTransformer.transformSwitchRexBoolToInt(leftOperand, loc, node);
		final ExpressionResult rr = mExprResultTransformer.transformSwitchRexBoolToInt(rightOperand, loc, node);
		return mCExpressionTranslator.handleBitwiseArithmeticOperation(loc, node.getOperator(), rl, rr);
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
		builder.addAuxVarWithDeclaration(auxvarInfo);
		final RValue auxvarRval = new RValue(auxvarInfo.getExp(), intType, true);

		// add auxvar assignment "#t~SHORT~UID = left"
		final AssignmentStatement assignStmt = StatementFactory.constructAssignmentStatement(loc,
				new LeftHandSide[] { auxvarInfo.getLhs() }, new Expression[] { rl.getLrValue().getValue() });
		builder.addStatementAndAnnotateOverapprox(assignStmt);

		final Statement[] thenPart;
		final Statement[] elsePart;
		final List<Statement> tmpList = new ArrayList<>(rr.getStatements());
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
		final ICType newCType = declResult.getDeclaration().getType();
		mCurrentDeclaredTypes.pop();

		final ExpressionResult expr = (ExpressionResult) main.dispatch(node.getOperand());
		ExpressionResult exprWithType = new ExpressionResultBuilder().addAllSideEffects(declResult)
				.addAllExceptLrValue(expr).setLrValue(expr.getLrValue()).build();

		if (!exprWithType.hasLRValue()) {
			// creates a void expression for null RValues
			final Expression newExpression = ExpressionFactory.createVoidDummyExpression(loc);
			final RValue rVal = new RValue(newExpression, new CPrimitive(CPrimitives.VOID));
			exprWithType = new ExpressionResultBuilder().addAllExceptLrValue(exprWithType).setLrValue(rVal).build();
		}
		exprWithType = mExprResultTransformer.makeRepresentationReadyForConversion(exprWithType, loc, newCType, node);
		checkUnsupportedPointerCast(exprWithType, loc, newCType);

		if (mSettings.isAdaptMemoryStructureResolutionOnPointerCasts() && mIsPrerun) {
			checkIfNecessaryMemoryStructureAdaption(loc, newCType, exprWithType);
		}

		exprWithType = mExprResultTransformer.rexBoolToInt(exprWithType, loc);
		return mExprResultTransformer.performImplicitConversion(exprWithType, newCType, loc);
	}

	private void checkIfNecessaryMemoryStructureAdaption(final ILocation loc, final ICType castTargetType,
			final ExpressionResult operand) {
		final ICType operandType = operand.getLrValue().getCType().getUnderlyingType();
		if (!(operandType instanceof CArray) && !(operandType instanceof CPointer)
				|| !(castTargetType instanceof CArray) && !(castTargetType instanceof CPointer)) {
			return;
		}

		// memory model adaptation might be necessary
		final ICType operandValueType;
		if (operandType instanceof CArray) {
			operandValueType = ((CArray) operandType).getValueType().getUnderlyingType();
		} else {
			operandValueType = ((CPointer) operandType).getPointsToType().getUnderlyingType();
		}

		final ICType castTargetValueType;
		if (castTargetType instanceof CArray) {
			castTargetValueType = ((CArray) castTargetType).getValueType().getUnderlyingType();
		} else {
			castTargetValueType = ((CPointer) castTargetType).getPointsToType().getUnderlyingType();
		}
		if (operandValueType.isIncomplete() || castTargetValueType.isIncomplete()) {
			mLogger.warn(
					"saw a pointer cast to a type that we could not get a type size for, not adapting memory model");
			return;
		}

		final Expression operandTypeByteSizeExp;
		try {
			operandTypeByteSizeExp = mTypeSizeComputer.constructBytesizeExpression(loc, operandValueType);
		} catch (final UnsupportedOperationException e) {
			mLogger.debug("saw a pointer cast to a type that we could not get a type size for, not adapting memory "
					+ "model");
			return;
		}
		final BigInteger operandTypeByteSize =
				mTypeSizes.extractIntegerValue(operandTypeByteSizeExp, mTypeSizeComputer.getSizeT());

		if (operandTypeByteSize.signum() == 0) {
			// operand's type has size 0 -- not sure what makes sense to do here, doing
			// nothing
			// case where I encountered it was a struct with a 0-sized array in it; if
			// someone wants to read more on
			// that phenomenon:
			// https://stackoverflow.com/questions/52630441/c-struct-with-zero-sized-array-members
			return;
		}

		final Expression castTargetByteSizeExp;
		try {
			castTargetByteSizeExp = mTypeSizeComputer.constructBytesizeExpression(loc, castTargetValueType);
		} catch (final UnsupportedOperationException e) {
			mLogger.debug("saw a pointer cast to a type that we could not get a type size for, not adapting memory "
					+ "model");
			return;
		}
		final BigInteger castTargetByteSize =
				mTypeSizes.extractIntegerValue(castTargetByteSizeExp, mTypeSizeComputer.getSizeT());

		// TODO 2022-02-25 Matthias: Currently we omit a change of the memory model if
		// the bytesize to which we cast is smaller that the bytesize of the operand.
		// The example "SubwordAccess.c" in our repository shows that this in unsound.
		// We should probably change the "<=" in the line below to "==". This change
		// will however cost performance and maybe we want make a decision only after we
		// saw real-world examples where this is a problem.
		if (castTargetByteSize.compareTo(operandTypeByteSize) <= 0) {
			// type sizes are already compatible
			return;
		}
		final BigInteger requiredByteSize = castTargetByteSize.min(operandTypeByteSize);

		final String msg;
		if (mSettings.getMemoryStructurePreference() == MemoryStructure.HoenickeLindenmann_Original) {
			// memory model has no resolution and the operand is
			// cast to a type of a different size
			msg = "Found a cast between two array/pointer types of different sizes while using memory model "
					+ MemoryStructure.HoenickeLindenmann_Original;
		} else if (BigInteger.valueOf(mSettings.getMemoryStructurePreference().getByteSize())
				.compareTo(requiredByteSize) > 0) {
			// memory model resolution is strictly bigger than the minimum of the size of
			// the operand and the target
			msg = "Found a cast between two array/pointer types of different sizes where the minimum of "
					+ "both sizes is smaller than the resolution of our memory model";
		} else {
			// no need to change memory model
			return;
		}

		if (mLogger.isDebugEnabled()) {
			mLogger.debug(msg);
			mLogger.debug(" at location: " + loc);
			mLogger.debug(" current memory model: " + mSettings.getMemoryStructurePreference());
		}
		// signal a restart of the translation with a memory model precise
		// enough for the operands
		signalTranslationRestartWithDifferentSettings(new TranslationSettings.SettingsChange(loc, msg,
				MemoryStructure.getPreciseEnoughMemoryStructureFor(requiredByteSize.intValueExact())));
	}

	public Result visit(final IDispatcher main, final IASTCompoundStatement node) {
		return handleCompoundStatement(main, node, false);
	}

	private Result handleCompoundStatement(final IDispatcher main, final IASTCompoundStatement node,
			final boolean useRValue) {
		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();
		LRValue expr = null;
		final boolean isNewScopeRequired = !(node.getParent() instanceof IASTFunctionDefinition);

		if (isNewScopeRequired) {
			beginScope();
		}

		Set<AuxVarInfo> auxVars = Set.of();
		for (final IASTNode child : node.getChildren()) {
			checkForACSL(main, resultBuilder, child, null, true);
			resultBuilder.addStatements(CTranslationUtil.createHavocsForAuxVars(auxVars));
			final Result r = main.dispatch(child);
			if (r instanceof ExpressionResult) {
				final ExpressionResult res = (ExpressionResult) r;
				resultBuilder.addDeclarations(res.getDeclarations());
				// TODO Frank: We somehow should not copy the overapproximations here
				resultBuilder.addStatements(res.getStatements());
				auxVars = res.getAuxVars();
				expr = res.getLrValue();
			} else if (r.getNode() != null && r.getNode() instanceof Body) {
				assert false : "should not happen, as CompoundStatement now yields an "
						+ "ExpressionResult or a CompoundStatementExpressionResult";
				// already have a unique naming for variables! --> unfold
				final Body b = (Body) r.getNode();
				resultBuilder.addDeclarations(Arrays.asList(b.getLocalVars()));
				resultBuilder.addStatements(Arrays.asList(b.getBlock()));
				auxVars = Set.of();
			} else if (r instanceof SkipResult) {
				// skip
			} else {
				assert false : "should not happen, as CompoundStatement now yields an "
						+ "ExpressionResult or a CompoundStatementExpressionResult, but was " + r.getClass();
			}
		}
		checkForACSL(main, resultBuilder, null, node, true);
		if (useRValue && expr != null) {
			final ILocation loc = mLocationFactory.createCLocation(node);
			if (expr instanceof HeapLValue) {
				// The read already creates an aux-var, so we just use the RValue of the read
				resultBuilder.addAllIncludingLrValue(
						mMemoryHandler.getReadCall(((HeapLValue) expr).getAddress(), expr.getCType()));
			} else {
				final AuxVarInfo auxVarInfo =
						mAuxVarInfoBuilder.constructAuxVarInfo(loc, expr.getCType(), AUXVAR.RETURNED);
				resultBuilder.addAuxVarWithDeclaration(auxVarInfo);
				resultBuilder.setLrValue(new RValue(auxVarInfo.getExp(), expr.getCType()));
				resultBuilder.addStatement(
						StatementFactory.constructSingleAssignmentStatement(loc, auxVarInfo.getLhs(), expr.getValue()));
			}
		}
		if (isNewScopeRequired) {
			updateStmtsAndDeclsAtScopeEnd(resultBuilder, node);
			addHavocsAtScopeEnd(node, resultBuilder);
			endScope();
		}
		resultBuilder.addStatements(CTranslationUtil.createHavocsForAuxVars(auxVars));
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
		final Optional<String> label = mInnerMostLoopLabel.peek();
		if (label.isEmpty()) {
			throw new AssertionError("Label for continue not found");
		}
		return new ExpressionResult(List.of(new GotoStatement(loc, new String[] { label.get() })), null);
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
		final ICType nestedPointerType = getPointerType(pointerOps.length, pendingResType.getCType());
		final TypesResult resType = TypesResult.create(pendingResType, nestedPointerType);

		// Adapt the name for multiparse input
		final String declName;
		final ICType cType;
		ResultWithSideEffects sideEffects = null;
		if (node instanceof final IASTArrayDeclarator arrDecl) {
			// the innermost type is the value type.
			ICType arrayType = resType.getCType();
			final CPrimitive boundType = mExpressionTranslation.getCTypeOfPointerComponents();

			// expression results of from array modifiers
			final ArrayList<ExpressionResult> expressionResults = new ArrayList<>();

			final ListIterator<IASTArrayModifier> it =
					Arrays.asList(arrDecl.getArrayModifiers()).listIterator(arrDecl.getArrayModifiers().length);
			while (it.hasPrevious()) {
				final IASTArrayModifier am = it.previous();
				final Expression bound;
				if (am.getConstantExpression() != null) {
					// case where we have a number between the brackets,
					// e.g., a[23] or a[n+1]
					final ExpressionResult dispatched = (ExpressionResult) main.dispatch(am.getConstantExpression());
					final ExpressionResult switched = mExprResultTransformer.switchToRValue(dispatched, loc, node);
					final ExpressionResult converted = mExpressionTranslation.convertIntToInt(loc, switched, boundType);
					expressionResults.add(converted);
					bound = converted.getLrValue().getValue();
				} else if (am.getConstantExpression() == null
						&& arrDecl.getArrayModifiers()[arrDecl.getArrayModifiers().length - 1] == am) {
					// the innermost array modifier may be empty, if there is an initializer; like
					// int a[1][2][] = {...}
					final int intSizeFactor;
					if (arrDecl.getInitializer() != null) {
						if (!(arrDecl.getInitializer() instanceof IASTEqualsInitializer)) {
							throw new UnsupportedOperationException("expected IASTEqualsInitializer");
						}
						intSizeFactor = computeSizeOfInitializer((IASTEqualsInitializer) arrDecl.getInitializer());
						bound = mTypeSizes.constructLiteralForIntegerType(loc, boundType,
								BigInteger.valueOf(intSizeFactor));
					} else if (resType.getCType() instanceof CFunction) {
						// if we have an array of function pointers,
						// the initializer is stored in the parent node
						// 2016-12-31 Matthias: I think this is only a workaround.
						// What if we do not have an array of function pointers
						// but an arrray of pointers to function pointers? Then
						// we probably have to check the parent of the parent
						final IASTFunctionDeclarator fundecl = (IASTFunctionDeclarator) arrDecl.getParent();
						if (fundecl.getInitializer() == null) {
							throw new UnsupportedOperationException("expected initializer");
						}
						intSizeFactor = computeSizeOfInitializer((IASTEqualsInitializer) fundecl.getInitializer());
						bound = mTypeSizes.constructLiteralForIntegerType(loc, boundType,
								BigInteger.valueOf(intSizeFactor));
					} else {
						// we have an incomplete array type without an initializer --
						// this may happen in a function parameter or as a flexible array in structs
						bound = null;
					}

				} else {
					throw new IncorrectSyntaxException(loc, "wrong array type in declaration");
				}
				arrayType = new CArray(bound, boundType, arrayType);
			}
			final ExpressionResult allResults = new ExpressionResultBuilder()
					.addAllExceptLrValue(expressionResults.toArray(new ExpressionResult[expressionResults.size()]))
					.build();
			cType = arrayType;
			declName = getNonFunctionDeclaratorName(node);
			sideEffects = allResults;
		} else if (node instanceof final IASTStandardFunctionDeclarator funcDecl) {
			// functions as well as function pointers can have
			// IASTStandardFunctionDeclarator
			final IASTParameterDeclaration[] paramDecls = funcDecl.getParameters();
			CDeclaration[] paramsParsed = new CDeclaration[paramDecls.length];
			for (int i = 0; i < paramDecls.length; i++) {
				final DeclaratorResult decl = (DeclaratorResult) main.dispatch(paramDecls[i]);
				if (!decl.hasNoSideEffects()) {
					// TODO but this should be possible
					throw new AssertionError("passing side-effects from DeclaratorResults is not yet implemented");
				}
				if (decl.getDeclaration().getName().isEmpty() && decl.getDeclaration().getType().isVoidType()) {
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
		} else if (node instanceof final ICASTKnRFunctionDeclarator funcDecl) {
			// Check that each parameter has a declarator.
			// (Simply comparing the lengths of the arrays is insufficient, as multiple parameter names may have a
			// common declarator when using K&R-style function definitions.)
			assert Arrays.stream(funcDecl.getParameterNames())
					.allMatch(name -> funcDecl.getDeclaratorForParameterName(name) != null)
					: "implicit int declarations are forbidden from C99 on, this is one, right?";

			// Dispatch each IASTDeclaration.
			// In the case of K&R-style function declarations, these may declare multiple parameters, and occur in a
			// different order than in the parameter list.
			final var decl2Result = new HashMap<IASTDeclarator, CDeclaration>();
			for (final IASTDeclaration astDecl : funcDecl.getParameterDeclarations()) {
				final DeclarationResult paramDeclRes = (DeclarationResult) main.dispatch(astDecl);
				final IASTSimpleDeclaration simpleDecl = (IASTSimpleDeclaration) astDecl;
				assert paramDeclRes.getDeclarations().size() == simpleDecl.getDeclarators().length;

				for (int i = 0; i < simpleDecl.getDeclarators().length; ++i) {
					final IASTDeclarator declarator = simpleDecl.getDeclarators()[i];
					final CDeclaration cdecl = paramDeclRes.getDeclarations().get(i);

					assert declarator.getName().toString().equals(cdecl.getName()) : "mismatch in parameter names";
					decl2Result.put(declarator, cdecl);
				}
			}

			// For each parameter, as ordered by the parameter list, find the translated CDeclaration.
			final CDeclaration[] paramsParsed = new CDeclaration[funcDecl.getParameterNames().length];
			for (int i = 0; i < funcDecl.getParameterNames().length; ++i) {
				final IASTDeclarator decl = funcDecl.getDeclaratorForParameterName(funcDecl.getParameterNames()[i]);
				paramsParsed[i] = decl2Result.get(decl);
				assert paramsParsed[i] != null;
			}

			cType = CFunction.createCFunction(resType.getCType(), paramsParsed,
					(IFunction) funcDecl.getName().resolveBinding());
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
			if (!result.hasNoSideEffects()) {
				// TODO but this should be possible
				throw new AssertionError("passing side-effects from DeclaratorResults is not yet implemented");
			}
			mCurrentDeclaredTypes.pop();
			if (node.getInitializer() != null) {
				final CDeclaration cdec = result.getDeclaration();
				result = new DeclaratorResult(new CDeclaration(cdec.getType(), cdec.getName(), node.getInitializer(),
						null, cdec.isOnHeap(), CStorageClass.UNSPECIFIED, bitfieldSize));
			}
			return result;
		}
		final var decl = new CDeclaration(cType, declName, node.getInitializer(), null, isOnHeap,
				CStorageClass.UNSPECIFIED, bitfieldSize);
		if (sideEffects != null) {
			return new DeclaratorResult(decl, sideEffects);
		}
		return new DeclaratorResult(decl);
	}

	private boolean isOnHeap(final IASTDeclarator node) {
		if (mIsPrerun) {
			return false;
		}
		if (mVariablesOnHeap.contains(node)) {
			return true;
		}
		final IBinding binding = node.getName().resolveBinding();
		if (binding instanceof ICInternalBinding) {
			final IASTNode[] decls = ((ICInternalBinding) binding).getDeclarations();
			// check if any of the declarations of this var are on heap, because then, all
			// have to be on heap
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
	private static ICType getPointerType(int length, final ICType cType) {
		ICType type = cType;
		for (; length > 0; --length) {
			type = new CPointer(type);
		}
		return type;
	}

	public Result visit(final IDispatcher main, final IASTDefaultStatement node) {
		return new ExpressionResult(
				new RValue(ExpressionFactory.createBooleanLiteral(mLocationFactory.createCLocation(node), true),
						new CPrimitive(CPrimitives.INT)));
	}

	/**
	 * Translates a do-statement {@code do body while (cond);} to {@code while (true) { body; Label: if (!cond) break;
	 * }}
	 *
	 * @param main
	 *            dispatcher
	 * @param node
	 *            AST node
	 * @return The do-statement translated to a Boogie-Result
	 */
	public Result visit(final IDispatcher main, final IASTDoStatement node) {
		final ILocation loc = mLocationFactory.createCLocation(node);
		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();
		final List<Statement> bodyBlock = new ArrayList<>();
		final boolean hasContinue = CdtASTUtils.containsContinue(node.getBody());
		final String loopLabel = hasContinue ? mNameHandler.getGloballyUniqueIdentifier(SFO.LOOPLABEL) : null;
		handleLoopBody(loc, main, node.getBody(), loopLabel, resultBuilder, bodyBlock);
		if (hasContinue) {
			bodyBlock.add(BoogieUtils.constuctAuxiliaryLabel(loc, loopLabel));
		}
		final ExpressionResult cond = dispatchLoopCondition(main, node.getCondition(), loc);
		resultBuilder.addDeclarations(cond.getDeclarations());
		bodyBlock.addAll(handleLoopCondition(loc, cond));
		final Expression loopCond =
				ExpressionFactory.createBooleanLiteral(LocationFactory.createIgnoreLocation(loc), true);
		return buildLoopResult(main, node, loopCond, bodyBlock, resultBuilder);
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
		if (r instanceof ExpressionResult || r instanceof SkipResult) {
			return r;
		}
		if (r instanceof ExpressionListResult) {
			return new ExpressionResultBuilder().addAllExceptLrValue(((ExpressionListResult) r).getList()).build();
		}
		final String msg = "We always convert to AssignmentStatement, other options raise this error!";
		final ILocation loc = mLocationFactory.createCLocation(node);
		throw new UnsupportedSyntaxException(loc, msg);
	}

	public Result visit(final IDispatcher main, final IASTFieldReference node) {
		return mStructHandler.handleFieldReference(main, mExprResultTransformer, node);
	}

	/**
	 * Translates a for-statement {@code for (init; cond; iterator) body} to {@code while (true) { if (!cond) break;
	 * body; Label: iterator; }}
	 *
	 * @param main
	 *            dispatcher
	 * @param node
	 *            AST node
	 * @return The for-statement translated to a Boogie-Result
	 */
	public Result visit(final IDispatcher main, final IASTForStatement node) {
		final ILocation loc = mLocationFactory.createCLocation(node);
		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();
		beginScope();
		// Process initializer (insert before the actual loop)
		final IASTStatement cInitStmt = node.getInitializerStatement();
		if (cInitStmt != null) {
			final Result initializer = main.dispatch(cInitStmt);
			if (initializer instanceof ExpressionResult) {
				resultBuilder.addAllExceptLrValueAndHavocAux((ExpressionResult) initializer);
			} else if (initializer instanceof SkipResult) {
				// This is an empty statement in the C Code. We will skip it
			} else {
				throw new UnsupportedSyntaxException(loc,
						"Uninplemented type of for loop initialization: " + initializer.getClass());
			}
		}
		final List<Statement> bodyBlock = new ArrayList<>();
		final Expression loopCond;
		if (node.getConditionExpression() == null) {
			// If the loop condition is omitted, we just translate it to while (true) {...}
			loopCond = ExpressionFactory.createBooleanLiteral(LocationFactory.createIgnoreLocation(loc), true);
		} else {
			final ExpressionResult condResult = dispatchLoopCondition(main, node.getConditionExpression(), loc);
			if (condResult.hasNoSideEffects()) {
				// If the condition has no side-effects, translate the loop to while (cond) {...}
				loopCond = condResult.getLrValue().getValue();
			} else {
				// Otherwise translate it to while (true) if (cond) {} else { break; } }
				resultBuilder.addDeclarations(condResult.getDeclarations());
				loopCond = ExpressionFactory.createBooleanLiteral(LocationFactory.createIgnoreLocation(loc), true);
				bodyBlock.addAll(handleLoopCondition(loc, condResult));
			}
		}
		final boolean hasContinue = CdtASTUtils.containsContinue(node.getBody());
		final String loopLabel = hasContinue ? mNameHandler.getGloballyUniqueIdentifier(SFO.LOOPLABEL) : null;
		handleLoopBody(loc, main, node.getBody(), loopLabel, resultBuilder, bodyBlock);
		if (hasContinue) {
			bodyBlock.add(BoogieUtils.constuctAuxiliaryLabel(loc, loopLabel));
		}

		// Insert the translated iterator at the end of the loop (after the loop label)
		final IASTExpression cItExpr = node.getIterationExpression();
		if (cItExpr != null) {
			final Result iterator = main.dispatch(cItExpr);
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
				throw new UnsupportedSyntaxException(loc,
						"Uninplemented type of loop iterator: " + iterator.getClass());
			}
		}

		final ExpressionResultBuilder bodyBlockBuilder = new ExpressionResultBuilder().addStatements(bodyBlock);
		updateStmtsAndDeclsAtScopeEnd(bodyBlockBuilder, node);
		endScope();
		resultBuilder.addDeclarations(bodyBlockBuilder.getDeclarations());
		return buildLoopResult(main, node, loopCond, bodyBlockBuilder.getStatements(), resultBuilder);
	}

	public Result visit(final IDispatcher main, final IASTFunctionCallExpression node) {
		final IASTExpression functionName = node.getFunctionNameExpression();
		final ILocation loc = mLocationFactory.createCLocation(node);
		// TODO: This is just a workaround for now to crash when thread local variables are used in a concurrent
		// program
		if (functionName instanceof final IASTIdExpression id && "pthread_create".equals(id.getName().toString())) {
			// Only crash for thread local variable in concurrent programs
			mIsConcurrent = true;
			if (mHasThreadLocalVars) {
				throw new UnsupportedSyntaxException(loc, "Thread local variables are not supported yet.");
			}
		}
		final Result standardFunction = mLibraryModelHandler.translateStandardFunction(main, node);
		if (standardFunction != null) {
			return standardFunction;
		}
		return mFunctionHandler.handleFunctionCallExpression(main, loc, functionName, node.getArguments(),
				mMemoryHandler);
	}

	public Result visit(final IDispatcher main, final IASTFunctionDefinition node) {
		if (!isReachable(node)) {
			// Unreachable function declaration. Test for parent=TU skipped: Not necessary,
			// right?
			return new SkipResult();
		}

		final TypesResult resType = (TypesResult) main.dispatch(node.getDeclSpecifier());

		mCurrentDeclaredTypes.push(resType);
		final DeclaratorResult declResult = (DeclaratorResult) main.dispatch(node.getDeclarator());
		if (!declResult.hasNoSideEffects()) {
			throw new AssertionError("passing side-effects from DeclaratorResults is not yet implemented");
		}

		mCurrentDeclaredTypes.pop();
		assert declResult.getDeclaration().getType() instanceof CFunction;
		mContract.addAll(main.getFunctionContractFromWitness(node));
		return mFunctionHandler.handleFunctionDefinition(main, mMemoryHandler, node, declResult.getDeclaration(),
				mContract, mIsInLibraryMode);
	}

	public Result visit(final IDispatcher main, final IASTGotoStatement node) {
		final ArrayList<Statement> stmt = new ArrayList<>();
		final String[] name = { node.getName().toString() };
		stmt.add(new GotoStatement(mLocationFactory.createCLocation(node), name));
		return new ExpressionResult(stmt, null);
	}

	public Result visit(final IDispatcher main, final IASTIdExpression node) {
		final ILocation loc = mLocationFactory.createCLocation(node);

		// Apply multifile input prefixing transformations to the ID
		final String cId = node.getName().toString();

		// deal with builtin constants
		final String cIdMp = mSymbolTable.applyMultiparseRenaming(node.getContainingFilename(), cId);
		if (!mSymbolTable.containsCSymbol(node, cIdMp)) {
			final var libraryConstant = mLibraryModelHandler.getConstantModels().get(cId);
			if (libraryConstant != null) {
				return libraryConstant.handleConstant(loc);
			}
		}

		final String bId;
		final ICType cType;
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
			if (stv.hasConstantValue()) {
				if (useHeap) {
					throw new AssertionError("I expected that constants are never stored on-heap.");
				}
				return new ExpressionResult(new RValue(stv.getConstantValue(), cType));
			}
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
			if (stv.hasConstantValue()) {
				if (useHeap) {
					throw new AssertionError("I expected that constants are never stored on-heap.");
				}
				return new ExpressionResult(new RValue(stv.getConstantValue(), cType));
			}
		} else if (mProcedureManager.hasProcedure(cIdMp)) {
			// C11 6.3.2.1.4 says: A function designator is an expression that has function type.
			final CFunction cFunction = mProcedureManager.getCFunctionType(cIdMp);
			cType = cFunction;
			bId = SFO.FUNCTION_ADDRESS + cIdMp;
			useHeap = true;
			intFromPtr = false;
			declarationInformation = DeclarationInformation.DECLARATIONINFO_GLOBAL;
		} else if (mFunctions.contains(cIdMp)) {
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
			final IdentifierExpression idExp = ExpressionFactory.constructIdentifierExpression(loc,
					mTypeHandler.getBoogiePointerType(), bId, declarationInformation);
			// convention: the ctype in the symbol table of something that we put on the heap
			// is the same as it would be if we did not put it on heap
			lrVal = LRValueFactory.constructHeapLValue(mTypeHandler, idExp, cType, intFromPtr, null);
		} else {
			final VariableLHS idLhs =
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
		if (!declaratorResult.hasNoSideEffects()) {
			throw new AssertionError("passing side-effects from DeclaratorResults is not yet implemented");
		}
		mCurrentDeclaredTypes.pop();

		final CDeclaration cDeclaration = declaratorResult.getDeclaration();
		assert !cDeclaration.hasInitializer() : "unexpected, inspect this case";
		assert !cDeclaration.isOnHeap() : "unexpected, inspect this case";
		ICType cType = cDeclaration.getType().getUnderlyingType();

		// translate initializer
		final IASTInitializer initializer = node.getInitializer();
		final InitializerResult ir = (InitializerResult) main.dispatch(initializer);

		if (cType instanceof final CArray cArray && cType.isIncomplete()) {
			// C11 6.7.9.22:
			// If an array of unknown size is initialized, its size is determined by the largest indexed element with an
			// explicit initializer. The array type is completed at the end of its initializer list.
			cType = new CArray(mExpressionTranslation.constructLiteralForIntegerType(loc,
					mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.valueOf(ir.getList().size())),
					cArray.getBoundType(), cArray.getValueType());
		}

		final boolean isAddressTaken = node.getParent() instanceof IASTUnaryExpression
				&& ((IASTUnaryExpression) node.getParent()).getOperator() == IASTUnaryExpression.op_amper;
		// catch simple case
		if (!isAddressTaken && (cType instanceof CPrimitive || cType instanceof CEnum)) {
			final CPrimitive cPrim = (CPrimitive) cType;
			final ExpressionResult exprRes =
					mExprResultTransformer.switchToRValue(InitializerResult.getFirstValueInInitializer(ir), loc, node);
			assert exprRes.hasLRValue();
			final ExpressionResult converted = mExprResultTransformer.performImplicitConversion(exprRes, cType, loc);

			final RValue rVal = (RValue) converted.getLrValue();

			// used to check if rVal is a constant
			final BigInteger intVal = mTypeSizes.extractIntegerValue(rVal);

			if (converted.hasNoSideEffects() && intVal != null
					&& cPrim.getGeneralType() == CPrimitiveCategory.INTTYPE) {
				// ExpressionResult is just an integer constant
				return converted;
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
			// do not add aux var to builder for havoccing here (havoccing is done after
			// freeing at endScope
		}

		// add malloc/free
		{
			final LocalLValue llv = new LocalLValue(aux.getLhs(), cType, null);
			if (mProcedureManager.isGlobalScope()) {
				final CallStatement malloc = mMemoryHandler.getUltimateMemAllocCall(llv, loc, MemoryArea.STACK);
				mStaticObjectsHandler.addStatementsForUltimateInit(Collections.singletonList(malloc));

			} else {
				final LocalLValueILocationPair llvp = new LocalLValueILocationPair(llv, loc);
				// malloc auxvar; note that in contrast to on-heap variables, this malloc must
				// only happen at the
				// beginning
				// of the scope, not each time the declaration point of the variable/this
				// compound literal is reached
				mMemoryHandler.addVariableToBeMalloced(llvp);
				// schedule aux to be freed at scope end
				mMemoryHandler.addVariableToBeFreed(llvp);
			}
		}

		// write the contents of the compound literal to the memory location designated
		// by aux
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
		final List<Overapprox> overappr = new ArrayList<>();
		final String label = node.getName().toString();
		stmt.add(new Label(loc, label));
		final Result r = main.dispatch(node.getNestedStatement());
		if (r instanceof ExpressionResult) {
			final ExpressionResult res = (ExpressionResult) r;
			decl.addAll(res.getDeclarations());
			stmt.addAll(res.getStatements());
			overappr.addAll(res.getOverapprs());
			return new ExpressionResult(stmt, res.getLrValue(), decl, Collections.emptySet(), overappr);
		}
		if (r instanceof SkipResult) {
			return new ExpressionResult(stmt, null, decl, Collections.emptySet());
		}
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
			return handleStringLiteralExpression(loc, node);
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

	/**
	 * Add Boogie code for allocation and writing of string literals. TODO 20211105 Matthias: Optimization: String
	 * literals are stored in a separate read-only area of the memory. String literals can neither be modified nor
	 * deallocated.
	 */
	private Result handleStringLiteralExpression(final ILocation loc, final IASTLiteralExpression node) {
		// Note: We can either use loc here or create a new ignore-loc s.t. the string
		// literal assignment will not be shown in the backtranslation
		final ILocation actualLoc = LocationFactory.createIgnoreCLocation(node);

		final CStringLiteral stringLiteral = new CStringLiteral(node.getValue(), mTypeSizes.getSignednessOfChar());
		final int sizeInBytes = stringLiteral.getByteValues().size();
		final Expression sizeInBytesExpr = mTypeSizes.constructLiteralForIntegerType(actualLoc,
				mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.valueOf(sizeInBytes));

		final CArray arrayType = new CArray(sizeInBytesExpr, mExpressionTranslation.getCTypeOfPointerComponents(),
				new CPrimitive(CPrimitives.CHAR));
		final CPointer pointerType = new CPointer(new CPrimitive(CPrimitives.CHAR));

		final RValue addressRValue;
		final CallStatement ultimateAllocCall;
		if (mSettings.fixedAddressesForInitialization()) {
			final Pair<RValue, CallStatement> pair = mMemoryHandler.getUltimateMemAllocInitCall(actualLoc, arrayType);

			addressRValue = pair.getFirst();
			ultimateAllocCall = pair.getSecond();

		} else {
			final AuxVarInfo auxvar =
					mAuxVarInfoBuilder.constructGlobalAuxVarInfo(actualLoc, pointerType, SFO.AUXVAR.STRINGLITERAL);
			addressRValue = new RValue(auxvar.getExp(), arrayType);
			// the declaration of the variable that corresponds to a string literal has to
			// be made global
			mStaticObjectsHandler.addGlobalVarDeclarationWithoutCDeclaration(auxvar.getVarDec());
			ultimateAllocCall = mMemoryHandler.getUltimateMemAllocCall(sizeInBytesExpr, auxvar.getLhs(), actualLoc,
					MemoryArea.STACK);
		}

		mStaticObjectsHandler.addStatementsForUltimateInit(List.of(ultimateAllocCall));

		// Overapproximate string literals of length STRING_OVERAPPROXIMATION_THRESHOLD
		// or longer
		if (stringLiteral.getByteValues().size() >= mSettings.getStringOverapproximationThreshold()) {
			final List<Overapprox> overapprox;
			if (OVERAPPROX_FLAG_LARGE_STRING_LITERAL) {
				overapprox = List.of(new Overapprox("Large string literal", actualLoc));
			} else {
				// FIXME Frank 2024-11-18: We omit the overapproximation flag, even thought no initialization is
				// performed. This is unsound, but does not lead to any wrong results in SV-COMP.
				overapprox = List.of();
			}
			return new StringLiteralResult(addressRValue, overapprox, stringLiteral);
		}
		final ExpressionResult exprRes = mInitHandler.writeStringLiteral(actualLoc, addressRValue, stringLiteral, node);
		assert !exprRes.hasLRValue();
		assert exprRes.getDeclarations().isEmpty();
		assert exprRes.getOverapprs().isEmpty();
		assert exprRes.getAuxVars().isEmpty();
		assert exprRes.getNeighbourUnionFields().isEmpty();
		mStaticObjectsHandler.addStatementsForUltimateInit(exprRes.getStatements());
		return new StringLiteralResult(addressRValue, List.of(), stringLiteral);
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
		final String signature = node.getRawSignature();
		if ("_Noreturn".equals(signature) || "noreturn".equals(signature)) {
			// Matthias 20230309: It seems like the parser does not support die _Noreturn
			// function specifier. It considers this as a IASTProblemDeclaration that is a
			// direct child of the translation unit. As a workaround, we skip this node.
			return new SkipResult();

		}
		final ILocation loc = mLocationFactory.createCLocation(node);
		throw new IncorrectSyntaxException(loc, String.format(
				"Syntax error (declaration problem) in C program: %s (%s)", node.getProblem().getMessage(), signature));
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
	 * <li>for global variables and declarations inside of struct definitions, it is a DeclarationResult (containing the
	 * Boogie Declaration of the variable)
	 * <li>for local variables that have an initializer, an ExpressionResult is returned which contains (Boogie)
	 * statements and declarations that make the initialization according to the initializer
	 * <li>for local variables without an initializer, a havoc statement is inserted into the ExpressionResult instead
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
		// TODO: This is just a workaround for now to crash when thread local variables are used in a concurrent program
		if (CTranslationUtil.hasAttribute(node.getDeclSpecifier(), "thread")) {
			mHasThreadLocalVars = true;
			// Only crash for thread local variable in concurrent programs
			if (mIsConcurrent) {
				throw new UnsupportedSyntaxException(loc, "Thread local variables are not supported yet.");
			}
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
		// Skip will be overwritten in case of a global or a local initialized variable

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
			// all unions should be on heap
			if (mIsPrerun && CStructOrUnion.isUnion(cDec.getType().getUnderlyingType())
					&& storageClass != CStorageClass.TYPEDEF) {
				addToVariablesOnHeap(declarator.getName());
			}

			if (cDec.getType() instanceof CFunction && storageClass != CStorageClass.TYPEDEF) {
				if (!declResult.hasNoSideEffects()) {
					throw new AssertionError("passing side-effects from DeclaratorResults is not yet implemented");
				}

				mContract.addAll(main.getFunctionContractFromWitness(node));
				// update functionHandler.procedures instead of symbol table
				mFunctionHandler.handleFunctionDeclarator(main, mLocationFactory.createCLocation(declarator), mContract,
						cDec, declarator);
				continue;
			}
			intermediateResults.add(handleIASTDeclarator(main, loc, node, declResult, declarator, storageClass));
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
		// 6.8.4.2-1: "The controlling expression of a switch statement shall have
		// integer type."
		// note that this does not mean that it has "int" type, it may be long or char,
		// for instance
		assert expr.getLrValue().getCType().isIntegerType();
		// 6.8.4.2-5: "The integer promotions are performed on the controlling
		// expression."
		expr = mExprResultTransformer.promoteToIntegerIfNecessary(loc, expr);

		resultBuilder.addAllExceptLrValue(expr);

		final Expression switchArg = expr.getLrValue().getValue();

		final CPrimitive intType = new CPrimitive(CPrimitives.INT);
		final String breakLabelName = mNameHandler.getGloballyUniqueIdentifier("SWITCH~BREAK~");

		final AuxVarInfo switchAuxvar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, intType,
				new PrimitiveType(loc, BoogieType.TYPE_BOOL, SFO.BOOL), SFO.AUXVAR.SWITCH);

		resultBuilder.addAuxVarWithDeclaration(switchAuxvar);

		boolean isFirst = true;
		boolean firstCond = true;
		Expression cond = null;
		ILocation locC = null;

		ArrayList<Statement> ifBlock = new ArrayList<>();
		beginScope();
		for (final IASTNode child : node.getBody().getChildren()) {
			if (isFirst && !(child instanceof IASTCaseStatement) && !(child instanceof IASTDefaultStatement)) {
				// declarations in the beginning of a switch body (i.e. before the first case/default) are used,
				// statements are dropped see example 6.8.4.2-7

				// we need to dispatch the child in order to fill the symbol table with declarations accordingly
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
					ifBlock.addAll(replaceBreaksWithGotos(locC, res.getStatements(), breakLabelName));
				}
				if (r.getNode() != null && r.getNode() instanceof Body) {
					// we already have a unique naming for variables! -> unfold
					final Body b = (Body) r.getNode();
					resultBuilder.addDeclarations(Arrays.asList(b.getLocalVars()));
					ifBlock.addAll(replaceBreaksWithGotos(locC, Arrays.asList(b.getBlock()), breakLabelName));
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

		resultBuilder.addStatement(BoogieUtils.constuctAuxiliaryLabel(loc, breakLabelName));
		resultBuilder.addStatements(CTranslationUtil.createHavocsForAuxVars(resultBuilder.getAuxVars()));

		// Use body as hook: This is the scope holder for switch statements! (as controller expression is child of the
		// switch itself and may not have scope access.)
		updateStmtsAndDeclsAtScopeEnd(resultBuilder, node.getBody());
		endScope();

		assert resultBuilder.getLrValue() == null;
		return resultBuilder.build();
	}

	private static List<Statement> replaceBreaksWithGotos(final ILocation loc, final Collection<Statement> statements,
			final String label) {
		final List<Statement> result = new ArrayList<>(statements.size());
		for (final Statement st : statements) {
			if (st instanceof BreakStatement) {
				result.add(new GotoStatement(loc, new String[] { label }));
			} else if (st instanceof IfStatement) {
				final IfStatement ifSt = (IfStatement) st;
				final Statement[] newThen =
						replaceBreaksWithGotos(loc, Arrays.asList(ifSt.getThenPart()), label).toArray(Statement[]::new);
				final Statement[] newElse =
						replaceBreaksWithGotos(loc, Arrays.asList(ifSt.getElsePart()), label).toArray(Statement[]::new);
				result.add(new IfStatement(loc, ifSt.getCondition(), newThen, newElse));
			} else {
				// TODO: Are there any other statements, where breaks should be replaced?
				result.add(st);
			}
		}
		return result;
	}

	public Result visit(final IDispatcher main, final IASTTranslationUnit node) {
		for (final IASTPreprocessorStatement preS : node.getAllPreprocessorStatements()) {
			final Result r = main.dispatch(preS);
			if (!(r instanceof SkipResult)) {
				throw new UnsupportedOperationException("Not yet implemented " + preS.toString());
			}
		}
		if (!mIsPrerun && mSettings.checkAcsl()) {
			mAcsl = main.nextACSLStatement();

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

		// The declarations (which are needed for the caller) are handled as a member as they do not consist of a Boogie
		// node. So as a workaround null is returned here
		return null;
	}

	public Result visit(final IDispatcher main, final IASTTypeIdExpression node) {
		final ILocation loc = mLocationFactory.createCLocation(node);
		switch (node.getOperator()) {
		case IASTTypeIdExpression.op_sizeof: {
			final TypesResult rt = (TypesResult) main.dispatch(node.getTypeId().getDeclSpecifier());
			mCurrentDeclaredTypes.push(rt);
			final DeclaratorResult dr = (DeclaratorResult) main.dispatch(node.getTypeId().getAbstractDeclarator());
			mCurrentDeclaredTypes.pop();
			// TypesResult checked = checkForPointer(main,
			// node.getTypeId().getAbstractDeclarator().getPointerOperators(), rt, false);

			final var rVal = new RValue(mMemoryHandler.calculateSizeOf(loc, dr.getDeclaration().getType()),
					mTypeSizeComputer.getSizeT());
			return new ExpressionResultBuilder().addAllSideEffects(dr).setLrValue(rVal).build();
		}
		case IASTTypeIdExpression.op_typeof: {
			final TypesResult rt = (TypesResult) main.dispatch(node.getTypeId().getDeclSpecifier());

			mCurrentDeclaredTypes.push(rt);
			final DeclaratorResult dr = (DeclaratorResult) main.dispatch(node.getTypeId().getAbstractDeclarator());
			mCurrentDeclaredTypes.pop();

			return dr;
		}
		case IASTTypeIdExpression.op_alignof:
			final TypesResult rt = (TypesResult) main.dispatch(node.getTypeId().getDeclSpecifier());
			mCurrentDeclaredTypes.push(rt);
			final DeclaratorResult dr = (DeclaratorResult) main.dispatch(node.getTypeId().getAbstractDeclarator());
			mCurrentDeclaredTypes.pop();
			final ExpressionResultBuilder builder = new ExpressionResultBuilder(
					mMemoryHandler.handleAlignOf(loc, dr.getDeclaration().getType(), mTypeSizeComputer.getSizeT()));
			return builder.addAllSideEffects(dr).build();
		default:
			break;
		}
		final String msg =
				"Unsupported AST node type: " + node.getClass() + " with operator " + node.getOperator() + ": " + loc;
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
			final ExpressionResult rop = mExprResultTransformer.transformDecaySwitch(operand, loc, node);
			return mCExpressionTranslator.handleUnaryArithmeticOperators(loc, node.getOperator(), rop);
		}
		case IASTUnaryExpression.op_postFixIncr:
		case IASTUnaryExpression.op_postFixDecr: {
			return mCExpressionTranslator.handlePostfixIncrementAndDecrement(loc, node.getOperator(), operand, node,
					a -> handleAtomicReadWrite(loc, operand.getLrValue(), operand.getStatements(), a, node));
		}
		case IASTUnaryExpression.op_prefixDecr:
		case IASTUnaryExpression.op_prefixIncr: {
			return mCExpressionTranslator.handlePrefixIncrementAndDecrement(node.getOperator(), loc, operand, node,
					a -> handleAtomicReadWrite(loc, operand.getLrValue(), operand.getStatements(), a, node));
		}
		case IASTUnaryExpression.op_bracketedPrimary:
			return operand;
		case IASTUnaryExpression.op_sizeof:
			final ICType operandType = operand.getCType().getUnderlyingType();
			return new ExpressionResult(
					new RValue(mMemoryHandler.calculateSizeOf(loc, operandType), mTypeSizeComputer.getSizeT()),
					Collections.emptySet());
		case IASTUnaryExpression.op_star: {
			return handleIndirectionOperator(operand, loc, node);
		}
		case IASTUnaryExpression.op_amper: {
			return handleAddressOfOperator(operand, node);
		}
		case IASTUnaryExpression.op_alignOf:
		default:
			final String msg = "Unknown or unsupported unary operation: " + node.getOperator();
			throw new UnsupportedSyntaxException(loc, msg);
		}
	}

	/**
	 * Translates a while-statement {@code while (cond) body} to {@code while (true) { Label: if (!cond) break; body; }}
	 *
	 * @param main
	 *            dispatcher
	 * @param node
	 *            AST node
	 * @return The while-statement translated to a Boogie-Result
	 */
	public Result visit(final IDispatcher main, final IASTWhileStatement node) {
		final ILocation loc = mLocationFactory.createCLocation(node);
		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();
		final boolean hasContinue = CdtASTUtils.containsContinue(node.getBody());
		final String loopLabel = hasContinue ? mNameHandler.getGloballyUniqueIdentifier(SFO.LOOPLABEL) : null;
		final List<Statement> bodyBlock = new ArrayList<>();
		if (hasContinue) {
			// If there is a continue, we need to insert an additional label to jump to.
			// We insert this label right before the actual loop in order to produce the correct invariant and to check
			// an existing invariant correctly (if any).
			resultBuilder.addStatement(BoogieUtils.constuctAuxiliaryLabel(loc, loopLabel));
		}
		final ExpressionResult cond = dispatchLoopCondition(main, node.getCondition(), loc);
		final Expression loopCond;
		if (cond.hasNoSideEffects()) {
			// If the condition has no side-effects, translate the loop to while (cond) {...}
			loopCond = cond.getLrValue().getValue();
		} else {
			// Otherwise translate it to while (true) if (cond) {} else { break; } }
			resultBuilder.addDeclarations(cond.getDeclarations());
			loopCond = ExpressionFactory.createBooleanLiteral(LocationFactory.createIgnoreLocation(loc), true);
			bodyBlock.addAll(handleLoopCondition(loc, cond));
		}
		handleLoopBody(loc, main, node.getBody(), loopLabel, resultBuilder, bodyBlock);
		return buildLoopResult(main, node, loopCond, bodyBlock, resultBuilder);
	}

	public Result visit(final IDispatcher main, final IGNUASTCompoundStatementExpression node) {
		return handleCompoundStatement(main, node.getCompoundStatement(), true);
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
			final ICType cvar = new CPointer(resType.getCType());
			return new TypesResult(t, resType.isConst(), resType.isVoid(), cvar);
		}
		return resType;
	}

	/**
	 * Convert an LrValue of array type to an (otherwise equivalent) RValue of pointer type.
	 * <p>
	 * Background: Array expressions can be used in place of pointer expressions in C. (An array may "decay" to a
	 * pointer in C standard terminology.) E.g. when an array is assigned to a pointer variable.
	 */
	public RValue decayArrayLrValToPointer(final LRValue rightLrVal, final IASTNode hook) {
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
			moveArrayAndStructIdsOnHeap(rightLrVal.getUnderlyingType(), oldValue, hook);
		} else if (rightLrVal instanceof RValue) {
			newValue = rightLrVal.getValue();
		} else {
			newValue = ((HeapLValue) rightLrVal).getAddress();
		}
		final ICType newType = new CPointer(((CArray) rightLrVal.getCType().getUnderlyingType()).getValueType());
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

	private ExpressionResult handleAtomicReadWrite(final ILocation loc, final LRValue leftHandSide,
			final List<Statement> statementsBeforeRead, final ExpressionResult rhs, final IASTNode hook) {
		final ExpressionResult assignment = makeAssignment(loc, leftHandSide, Set.of(), rhs, hook);
		if (!leftHandSide.getCType().isAtomic()) {
			// For non-atomic types return the normal assignment
			return assignment;
		}
		final List<Statement> allStatements = assignment.getStatements();

		// Check if statementsBeforeRead are a prefix of allStatements
		if (!statementsBeforeRead.equals(allStatements.subList(0, statementsBeforeRead.size()))) {
			throw new AssertionError(
					"Unexpected result of makeAssignment: statements do not start with statements of rhs");
		}
		// For atomic types make sure that all statement except the ones before the read are in an atomic block
		final List<Statement> atomicStatements =
				allStatements.subList(statementsBeforeRead.size(), allStatements.size());
		return new ExpressionResultBuilder().addStatements(statementsBeforeRead)
				.addAllExceptLrValueAndStatements(assignment).setLrValue(assignment.getLrValue())
				.addStatement(StatementFactory.constructAtomicStatement(loc, atomicStatements)).build();
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
					markAsIntFromPointer(lId, hook);
				} else {
					// TODO
				}
			} else if (leftHandSide instanceof LocalLValue) {
				String lId = null;
				final LeftHandSide value = ((LocalLValue) leftHandSide).getLhs();
				if (value instanceof VariableLHS) {
					lId = ((VariableLHS) value).getIdentifier();
					markAsIntFromPointer(lId, hook);
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
						(CPrimitive) CEnum.replaceEnumWithInt(hlv.getCType().getUnderlyingType()), bitfieldWidth);
			} else {
				rhsWithBitfieldTreatment = rightHandSideValueWithConversionsApplied.getValue();
			}

			Expression resultRhs;
			if (rhsConverted.getOverapprs().isEmpty()) {
				resultRhs = rhsWithBitfieldTreatment;
			} else {
				// If the right-hand-side of the assignment contains an overapproximation, we create an additional
				// aux-var and annotate the corresponding assignment of the right-hand-side with a variable-based
				// overapproximation (to ensure that not the whole heap is overapproximated).
				final AuxVarInfo auxVar = mAuxVarInfoBuilder.constructAuxVarInfo(loc,
						rightHandSideValueWithConversionsApplied.getCType(), AUXVAR.RETURNED);
				final Statement assignment = StatementFactory.constructSingleAssignmentStatement(loc, auxVar.getLhs(),
						rhsWithBitfieldTreatment);
				for (final var oa : rhsConverted.getOverapprs()) {
					new OverapproxVariable(oa.getOverapproximatedLocations()).annotate(assignment);
				}
				builder.addAuxVarWithDeclaration(auxVar);
				builder.addStatement(assignment);
				resultRhs = auxVar.getExp();
			}
			// MemoryHandler::getWriteCall already handles atomic types properly, so there is nothing to do here.
			builder.addStatements(mMemoryHandler.getWriteCall(loc, hlv, resultRhs,
					rightHandSideValueWithConversionsApplied.getCType(), false));

			// the value of an assignment statement expression is the right hand side of the
			// assignment
			builder.setLrValue(rightHandSideValueWithConversionsApplied);

			if (mDataRaceChecker != null) {
				mDataRaceChecker.checkOnWrite(builder, loc, leftHandSide);
			}
			return builder.build();
		}
		if (!(leftHandSide instanceof LocalLValue)) {
			throw new AssertionError("Type error: trying to assign to an RValue in Statement" + loc.toString());
		}
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		/*
		 * take over everything but neighbour union fields -- those will be given to assignorHavocUnionNeighbours as an
		 * extra parameter
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
			rhsWithBitfieldTreatment = mExpressionTranslation.eraseBits(loc,
					rightHandSideValueWithConversionsApplied.getValue(),
					(CPrimitive) CEnum.replaceEnumWithInt(lValue.getCType().getUnderlyingType()), bitfieldWidth);
		} else {
			rhsWithBitfieldTreatment = rightHandSideValueWithConversionsApplied.getValue();
		}
		final AssignmentStatement assignStmt = StatementFactory.constructAssignmentStatement(loc,
				new LeftHandSide[] { lValue.getLhs() }, new Expression[] { rhsWithBitfieldTreatment });

		if (leftHandSide.getCType().isAtomic()) {
			// For atomic types, make this assignment into an atomic block
			builder.addStatement(new AtomicStatement(loc, new Statement[] { assignStmt }));
		} else {
			builder.addStatement(assignStmt);
		}

		for (final Overapprox oa : rhsConverted.getOverapprs()) {
			new OverapproxVariable(oa.getOverapproximatedLocations()).annotate(assignStmt);
		}
		// TODO: DD 2020-12-02: havocing neighbours should only happen if the field is
		// really on the stack -- it
		// seems that this cannot happen anymore
		// final ExpressionResultBuilder builderWithUnionFieldAndNeighboursUpdated =
		// assignOrHavocUnionNeighbours(loc,
		// (RValue) rhsConverted.getLrValue(), rhsConverted.getNeighbourUnionFields(),
		// rightHandSideValueWithConversionsApplied, builder, hook);
		// return builderWithUnionFieldAndNeighboursUpdated.build();

		if (mDataRaceChecker != null) {
			mDataRaceChecker.checkOnWrite(builder, loc, leftHandSide);
		}
		return builder.build();
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
		exprResultBuilder.resetStatements(mMemoryHandler.insertMallocs(exprResultBuilder.getStatements()));
		for (final SymbolTableValue stv : mSymbolTable.getInnermostCScopeValues(hook)) {
			// there may be a null declaration in case of foo(void) -- therefore we need to
			// check the second conjunct
			// (case where this is called from FunctionHandler.handleFunctionDefinition)
			if (!stv.isBoogieGlobalVar() && stv.getBoogieDecl() != null) {
				exprResultBuilder.addDeclaration(stv.getBoogieDecl());
			}
		}
	}

	private void addHavocsAtScopeEnd(final IASTNode hook, final ExpressionResultBuilder builder) {
		if (!ADD_HAVOCS_AT_SCOPE_END) {
			return;
		}
		final List<VariableLHS> vars = new ArrayList<>();
		final ILocation loc = LocationFactory.createIgnoreCLocation(hook);
		for (final SymbolTableValue stv : mSymbolTable.getInnermostCScopeValues(hook)) {
			if (!stv.isBoogieGlobalVar() && stv.getBoogieDecl() != null) {
				final VariableLHS lhs = new VariableLHS(loc, stv.getAstType().getBoogieType(), stv.getBoogieName(),
						stv.getDeclarationInformation());
				vars.add(lhs);
			}
		}
		if (!vars.isEmpty()) {
			builder.addStatement(new HavocStatement(loc, vars.toArray(VariableLHS[]::new)));
		}
	}

	/**
	 * @return true iff this is called while in prerun mode, false otherwise
	 */
	public void moveArrayAndStructIdsOnHeap(final ICType underlyingType, final Expression expr, final IASTNode hook) {
		if (!mIsPrerun) {
			if (underlyingType instanceof CArray) {
				throw new AssertionError("on-heap/off-heap bug: array has to be on-heap");
			}
			return;
		}
		for (final String id : BoogieVariableCollector.extractIds(expr)) {
			final String cid = mSymbolTable.getCIdForBoogieId(id);
			if (cid == null) {
				// expression does not have a corresponding c identifier --> nothing to move on heap
				continue;
			}
			final SymbolTableValue value = mSymbolTable.findCSymbol(CTranslationUtil.findExpressionHook(hook), cid);
			if (value == null) {
				throw new AssertionError("no entry in symbol table for C-ID " + cid);
			}
			final ICType type = value.getCType().getUnderlyingType();
			if (type instanceof CArray || type instanceof CStructOrUnion) {
				addToVariablesOnHeap(value.getDeclarationNode());
			}
		}
	}

	private boolean isReachable(final IASTDeclaration node) {
		return mReachableDeclarations == null || mReachableDeclarations.contains(node);
	}

	private void checkUnsupportedPointerCast(final ExpressionResult expr, final ILocation loc, final ICType newCType) {
		if (!POINTER_CAST_IS_UNSUPPORTED_SYNTAX || !(newCType instanceof CPointer)
				|| !(expr.getLrValue().getCType() instanceof CPointer)) {
			return;
		}
		final ICType newPointsToType = ((CPointer) newCType).getPointsToType();
		final ICType exprPointsToType = ((CPointer) expr.getLrValue().getCType()).getPointsToType();
		if (newPointsToType instanceof CPrimitive && exprPointsToType instanceof CPrimitive) {
			if (((CPrimitive) newPointsToType).getGeneralType() == CPrimitiveCategory.INTTYPE
					&& ((CPrimitive) exprPointsToType).getGeneralType() == CPrimitiveCategory.INTTYPE) {
				if (mTypeSizes.isUnsigned((CPrimitive) newPointsToType)
						&& !mTypeSizes.isUnsigned((CPrimitive) exprPointsToType)
						|| !mTypeSizes.isUnsigned((CPrimitive) newPointsToType)
						|| !mTypeSizes.isUnsigned((CPrimitive) exprPointsToType)) {
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
			final DeclaratorResult declResult, final IASTDeclarator hook, final CStorageClass storageClass) {

		final CDeclaration cDec = declResult.getDeclaration();
		final boolean onHeap = cDec.isOnHeap() || isOnHeap(hook);
		final DeclarationInformation declarationInformation = getDeclarationInfo(storageClass);
		final String bId = mNameHandler.getUniqueIdentifier(node, cDec.getName(), mSymbolTable.getCScopeId(hook),
				onHeap, cDec.getType(), declarationInformation);
		if (onHeap) {
			addBoogieIdsOfHeapVars(bId);
		}

		// this is only to have a minimal symbolTableEntry (containing boogieID) for
		// translation of the initializer
		final var stv = new SymbolTableValue(bId, null, null, cDec, declarationInformation, hook, false);
		mSymbolTable.storeCSymbol(node, cDec.getName(), stv);
		final InitializerResult initializer = translateInitializer(main, cDec);
		cDec.setInitializerResult(initializer);

		final ASTType translatedType =
				onHeap ? mTypeHandler.constructPointerType(loc) : mTypeHandler.cType2AstType(loc, cDec.getType());

		final Declaration boogieDec;
		final Result result;
		if (storageClass == CStorageClass.TYPEDEF) {
			boogieDec = new TypeDeclaration(loc, new Attribute[0], false, bId, new String[0], translatedType);

			final BoogieType boogieType = mTypeHandler.getBoogieTypeForCType(cDec.getType());

			mTypeHandler.addDefinedType(bId, new TypesResult(new NamedType(loc, boogieType, cDec.getName(), null),
					false, false, cDec.getType()));
			final ICType cType = cDec.getType();
			if (cType.isIncomplete() && !cType.isVoidType()) {
				final ICType underlying = cType.getUnderlyingType();
				final String identifier;
				if (underlying instanceof final CStructOrUnion structOrUnion) {
					identifier = structOrUnion.getName();
				} else if (underlying instanceof final CEnum enumType) {
					identifier = enumType.getName();
				} else {
					throw new AssertionError("missing support for global incomplete " + cType);
				}
				mTypeHandler.registerNamedIncompleteType(identifier, cDec.getName());
			}
			// TODO: add a sizeof-constant for the type??
			mStaticObjectsHandler.addGlobalTypeDeclaration((TypeDeclaration) boogieDec, cDec);

			result = skipOrSideEffects(declResult);
		} else if (storageClass == CStorageClass.STATIC && !mProcedureManager.isGlobalScope()) {
			// we have a local static variable -> special treatment
			// global static variables are treated like normal global variables..
			boogieDec = new VariableDeclaration(loc, new Attribute[0],
					new VarList[] { new VarList(loc, new String[] { bId }, translatedType) });
			final var scope = mSymbolTable.tableFindCursor(hook, cDec.getName(), stv);
			mStaticObjectsHandler.addGlobalVariableDeclaration((VariableDeclaration) boogieDec, cDec, scope);
			result = skipOrSideEffects(declResult);
		} else {
			final BoogieType boogieType =
					mTypeHandler.getBoogieTypeForBoogieASTType(mTypeHandler.cType2AstType(loc, cDec.getType()));

			/**
			 * For Variable length arrays we have a "non-real" initializer which just initializes the aux var for the
			 * array's size. We do not want to treat this like other initializers (call initVar and so).
			 */
			final boolean hasRealInitializer =
					cDec.hasInitializer() && (!(cDec.getType() instanceof CArray) || cDec.getInitializer() != null);

			final boolean isInsideStructDeclaration = mSymbolTable.isInsideStructDeclaration(hook);

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
				erb.addAllSideEffects(declResult);

				final VariableLHS lhs =
						ExpressionFactory.constructVariableLHS(loc, boogieType, bId, declarationInformation);

				if (cDec.hasInitializer()) {
					// must be a non-real initializer for variable length array size
					// --> need to pass this on
					// TODO: double check this
					erb.addAllExceptLrValue(cDec.getInitializer().getRootExpressionResult());
				}

				// no initializer --> essentially needs to be havoced f.i. in each loop
				// iteration
				if (!onHeap) {
					erb.addStatement(new HavocStatement(loc, new VariableLHS[] { lhs }));
				} else {
					final LocalLValue llVal = new LocalLValue(lhs, cDec.getType(), null);
					// old solution: havoc via an auxvar, new solution (below):
					// just malloc at the right place (much shorter for arrays and structs..)
					erb.addStatement(mMemoryHandler.getUltimateMemAllocCall(llVal, loc, MemoryArea.STACK));
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
				erb.addAllSideEffects(declResult);
				final ExpressionResult initRex =
						mInitHandler.initialize(loc, lhs, cDec.getType(), cDec.getInitializer(), hook);

				if (onHeap) {
					final LocalLValue llVal = new LocalLValue(lhs, cDec.getType(), null);
					mMemoryHandler.addVariableToBeFreed(new LocalLValueILocationPair(llVal, loc));
					erb.addStatement(mMemoryHandler.getUltimateMemAllocCall(llVal, loc, MemoryArea.STACK));
				}
				erb.addAllExceptLrValueAndHavocAux(initRex);
				result = erb.build();
			} else {
				if (!declResult.hasNoSideEffects()) {
					throw new AssertionError("passing side-effects from DeclaratorResults is not yet implemented");
				}

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
		// TODO: Unnamed struct fields have cDec.getName() == "" ; is this supposed to
		// happen?
		mSymbolTable.storeCSymbol(node, cDec.getName(),
				new SymbolTableValue(bId, boogieDec, translatedType, cDec, declarationInformation, hook, false));
		return result;
	}

	private static Result skipOrSideEffects(final ResultWithSideEffects result) {
		if (result.hasNoSideEffects()) {
			return new SkipResult();
		}
		return new ExpressionResultBuilder().addAllSideEffects(result).build();
	}

	private DeclarationInformation getDeclarationInfo(final CStorageClass storageClass) {
		if (storageClass == CStorageClass.TYPEDEF || storageClass == CStorageClass.STATIC
				|| mProcedureManager.isGlobalScope()) {
			return DeclarationInformation.DECLARATIONINFO_GLOBAL;
		}
		return new DeclarationInformation(StorageClass.LOCAL, mProcedureManager.getCurrentProcedureID());
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
		}
		if (res instanceof ExpressionResult) {
			return new InitializerResultBuilder().setRootExpressionResult((ExpressionResult) res).build();
		}
		throw new AssertionError("Expected either InitializerResult or ExpressionResult, but got " + res.getClass());
	}

	private static int computeSizeOfInitializer(final IASTEqualsInitializer equalsInitializer) {
		if (equalsInitializer.getInitializerClause() instanceof IASTInitializerList) {
			final IASTInitializerList initList = (IASTInitializerList) equalsInitializer.getInitializerClause();
			return initList.getSize();
		}
		if (equalsInitializer.getInitializerClause() instanceof IASTLiteralExpression
				&& ((IASTLiteralExpression) equalsInitializer.getInitializerClause())
						.getKind() == IASTLiteralExpression.lk_string_literal) {
			final IASTLiteralExpression lit = (IASTLiteralExpression) equalsInitializer.getInitializerClause();
			/*
			 * subtracting -1 because lit.getValue includes the quotation marks (-2) and we will add a termination
			 * character (+1), for example the string literals "bla" will give us length 7, as C will store it as 'b'
			 * 'l' 'a' '\0'
			 */
			return lit.getValue().length - 1;
		}
		throw new AssertionError("attempting to compute size of an unforseen kind of initializer expression");
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

	private void moveIdOnHeap(final IdentifierExpression idExpr, final IASTNode hook) {
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
			if (parent instanceof IASTFunctionDeclarator || parent instanceof ICASTCompositeTypeSpecifier) {
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
							&& mMemoryHandler.calculateSizeOf(loc, rightHandSideWithConversionsApplied
									.getCType()) == mMemoryHandler.calculateSizeOf(loc, er.getLrValue().getCType())) {

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

				builder.addAuxVarWithDeclaration(auxVar);

				final RValue tmpVarRVal = new RValue(auxVar.getExp(), er.getLrValue().getCType());

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
					mAcsl = main.nextACSLStatement();
				}
				if (globAcsl instanceof CodeAnnotStmt) {
					final CodeStatement codeStmt = ((CodeAnnotStmt) globAcsl).getCodeStmt();
					if (codeStmt instanceof GlobalGhostDeclaration) {
						handleGhostDeclaration(main, resultBuilder, next, (GlobalGhostDeclaration) codeStmt);
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
					if (!(acslResult instanceof ExpressionResult)) {
						final String msg = "Unexpected ACSL comment: " + acslResult.getNode().getClass();
						final ILocation loc = mLocationFactory.createCLocation(parent);
						throw new IncorrectSyntaxException(loc, msg);
					}
					resultBuilder.addDeclarations(((ExpressionResult) acslResult).getDeclarations());
					resultBuilder.addStatements(((ExpressionResult) acslResult).getStatements());
					resultBuilder.addStatements(
							CTranslationUtil.createHavocsForAuxVars(((ExpressionResult) acslResult).getAuxVars()));
				}
				mAcsl = main.nextACSLStatement();
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
				} else // this means we are in the translation unit
				if (acslNode instanceof Contract || acslNode instanceof LoopAnnot) {
					// Function contract
					mContract.add(acslNode);
				}
			}
			mAcsl = main.nextACSLStatement();
		}
	}

	private void handleGhostDeclaration(final IDispatcher main, final ExpressionResultBuilder resultBuilder,
			final IASTNode hook, final GlobalGhostDeclaration decl) {
		final ILocation loc = mLocationFactory.createCLocation(hook);
		final SymbolTableValue oldSymbol = mSymbolTable.findCSymbol(hook, decl.getIdentifier());
		if (oldSymbol != null) {
			throw new UnsupportedSyntaxException(loc,
					String.format("The ghost variable %s shadows another variable.", decl.getIdentifier()));
		}
		final String boogieName = SFO.GHOST + decl.getIdentifier();
		final ICType cType = AcslTypeUtils.translateAcslTypeToCType(decl.getType());
		final ASTType astType = mTypeHandler.cType2AstType(loc, cType);
		final VariableDeclaration boogieDecl = new VariableDeclaration(loc, new Attribute[0],
				new VarList[] { new VarList(loc, new String[] { boogieName }, astType) });
		final CDeclaration cDecl = new CDeclaration(cType, decl.getIdentifier());
		final DeclarationInformation declInfo = DeclarationInformation.DECLARATIONINFO_GLOBAL;
		mSymbolTable.storeCSymbol(hook, decl.getIdentifier(),
				new SymbolTableValue(boogieName, boogieDecl, astType, cDecl, declInfo, hook, false));
		resultBuilder.addDeclaration(boogieDecl);
		if (decl.getExpr() != null) {
			final ExpressionResult exprResult = (ExpressionResult) main.dispatch(decl.getExpr(), hook);
			final ExpressionResult converted = mExprResultTransformer
					.makeRepresentationReadyForConversionAndRexBoolToInt(exprResult, loc, cType, hook);
			final VariableLHS lhs =
					new VariableLHS(loc, mTypeHandler.getBoogieTypeForCType(cType), boogieName, declInfo);
			final ExpressionResult assignment =
					makeAssignment(loc, new LocalLValue(lhs, cType, null), List.of(), converted, hook);
			resultBuilder.addAllExceptLrValueAndStatements(assignment);
			mStaticObjectsHandler.addStatementsForUltimateInit(assignment.getStatements());
		}
	}

	private void markAsIntFromPointer(final String lId, final IASTNode hook) {
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
				if (!(boogieDecl instanceof VariableDeclaration)) {
					throw new AssertionError("TODO: handle this case!");
				}
				mStaticObjectsHandler.addGlobalVariableDeclaration((VariableDeclaration) boogieDecl, cd, null);
			}
		} else {
			if (childRes instanceof SkipResult || childRes.getNode() == null) {
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
	private Result handleAddressOfOperator(final ExpressionResult er, final IASTNode hook) throws AssertionError {
		final RValue rVal;
		if (er.getLrValue() instanceof HeapLValue) {
			rVal = ((HeapLValue) er.getLrValue()).getAddressAsPointerRValue(mTypeHandler.getBoogiePointerType());
		} else if (er.getLrValue() instanceof LocalLValue) {
			if (!mIsPrerun) {
				throw new AssertionError("cannot take address of LocalLValue: this is a on-heap/off-heap bug");
			}
			// We are in the prerun mode.
			// As a workaround, we (incorrectly) return the value
			// instead of the address. But we add variables to the
			// heapVars and hence in the non-prerun mode the input
			// will be a HeapLValue instead of a LocalLValue.
			final Expression expr = er.getLrValue().getValue();
			if (expr instanceof IdentifierExpression) {
				final IdentifierExpression idExpr = (IdentifierExpression) expr;
				moveIdOnHeap(idExpr, hook);
			} else {
				moveArrayAndStructIdsOnHeap(er.getLrValue().getUnderlyingType(), expr, hook);
			}
			rVal = convertToPointerRValue(er.getLrValue(), mTypeHandler.getBoogiePointerType());
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
	public Result handleIndirectionOperator(final ExpressionResult expr, final ILocation loc, final IASTNode hook) {
		final ExpressionResult rop =
				mExprResultTransformer.makeRepresentationReadyForConversion(expr, loc, CPointer.voidPointer(), hook);
		final RValue rValue = (RValue) rop.getLrValue();
		if (!(rValue.getCType().getUnderlyingType() instanceof CPointer)) {
			throw new IllegalArgumentException("dereference needs pointer but got " + rValue.getCType());
		}
		final CPointer pointer = (CPointer) rValue.getCType().getUnderlyingType();
		final ICType pointedType = pointer.getPointsToType();
		if (pointedType.isIncomplete()) {
			return new ExpressionWithIncompleteTypeResult(rop.getStatements(),
					LRValueFactory.constructHeapLValue(mTypeHandler, rValue.getValue(), pointedType, null),
					rop.getDeclarations(), rop.getAuxVars(), rop.getOverapprs(), loc);

		}
		return new ExpressionResult(rop.getStatements(),
				LRValueFactory.constructHeapLValue(mTypeHandler, rValue.getValue(), pointedType, null),
				rop.getDeclarations(), rop.getAuxVars(), rop.getOverapprs());
	}

	private void handleLoopBody(final ILocation loc, final IDispatcher main, final IASTStatement bodyStmt,
			final String loopLabel, final ExpressionResultBuilder resultBuilder, final List<Statement> bodyBlock) {
		mInnerMostLoopLabel.push(Optional.ofNullable(loopLabel));
		final Result bodyResult = main.dispatch(bodyStmt);
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
		mInnerMostLoopLabel.pop();
	}

	private ExpressionResult dispatchLoopCondition(final IDispatcher main, final IASTExpression node,
			final ILocation loc) {
		final ExpressionResult result = (ExpressionResult) main.dispatch(node);
		assert CTranslationUtil.isAuxVarMapComplete(mNameHandler, result.getDeclarations(), result.getAuxVars());
		return mExprResultTransformer.transformSwitchRexIntToBool(result, loc, node);
	}

	private static List<Statement> handleLoopCondition(final ILocation loc, final ExpressionResult cond) {
		final List<Statement> result = new ArrayList<>(cond.getStatements());
		// Insert an if-statement: if (cond) {} else break;
		// Note: we could invert the condition and omit the then branch, but we want to keep the negation consistent in
		// C and Boogie.
		// Make sure to havoc all aux-vars that are created from the translation of cond (in the if and else branches)
		final Statement[] havocs = CTranslationUtil.createHavocsForAuxVars(cond.getAuxVars()).toArray(Statement[]::new);
		final IfStatement ifStmt = new IfStatement(loc, cond.getLrValue().getValue(), havocs,
				DataStructureUtils.concat(havocs, new Statement[] { new BreakStatement(loc) }));
		cond.getOverapprs().forEach(oa -> oa.annotate(ifStmt));
		result.add(ifStmt);
		return result;
	}

	private Result buildLoopResult(final IDispatcher main, final IASTStatement node, final Expression cond,
			final List<Statement> bodyBlock, final ExpressionResultBuilder resultBuilder) {
		final LoopInvariantSpecification[] spec = extractLoopInvariants(main, node);
		final WhileStatement whileStmt = new WhileStatement(mLocationFactory.createCLocation(node), cond, spec,
				bodyBlock.toArray(Statement[]::new));
		resultBuilder.getOverappr().stream().forEach(a -> a.annotate(whileStmt));
		resultBuilder.addStatement(whileStmt);

		if (node instanceof IASTForStatement) {
			// Havoc variables declared in the initializer after the loop
			addHavocsAtScopeEnd(node, resultBuilder);
		}

		assert resultBuilder.getLrValue() == null : "there is an lrvalue although there should be none";
		assert resultBuilder.getAuxVars().isEmpty() : "auxvars were added although they should have been havoced";
		return resultBuilder.build();
	}

	private LoopInvariantSpecification[] extractLoopInvariants(final IDispatcher main, final IASTStatement node) {
		if (mContract == null || mContract.isEmpty()) {
			return new LoopInvariantSpecification[0];
		}
		final List<LoopInvariantSpecification> spec = new ArrayList<>();
		for (final ACSLNode acsl : mContract) {
			final Result res = main.dispatch(acsl, node);
			if (res instanceof ContractResult) {
				final ContractResult resContr = (ContractResult) res;
				assert resContr.getSpecs().length == 1;
				for (final Specification cSpec : resContr.getSpecs()) {
					spec.add((LoopInvariantSpecification) cSpec);
				}
			} else {
				spec.add((LoopInvariantSpecification) res.getNode());
			}
		}
		// take care for behavior and completeness
		clearContract();
		return spec.toArray(LoopInvariantSpecification[]::new);
	}
}
