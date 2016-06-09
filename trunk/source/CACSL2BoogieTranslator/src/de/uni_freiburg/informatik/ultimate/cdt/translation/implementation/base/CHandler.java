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
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Stack;

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
import org.eclipse.cdt.core.dom.ast.IASTEnumerationSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTEqualsInitializer;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTExpressionList;
import org.eclipse.cdt.core.dom.ast.IASTExpressionStatement;
import org.eclipse.cdt.core.dom.ast.IASTFieldReference;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTGotoStatement;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTIfStatement;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTInitializerList;
import org.eclipse.cdt.core.dom.ast.IASTLabelStatement;
import org.eclipse.cdt.core.dom.ast.IASTLiteralExpression;
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
import org.eclipse.cdt.core.dom.ast.IASTStatement;
import org.eclipse.cdt.core.dom.ast.IASTSwitchStatement;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.dom.ast.IASTTypeIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTWhileStatement;
import org.eclipse.cdt.core.dom.ast.c.ICASTCompositeTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.gnu.IGNUASTCompoundStatementExpression;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTDeclarator;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTDesignatedInitializer;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTFunctionDeclarator;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.annotation.LTLPropertyCheck;
import de.uni_freiburg.informatik.ultimate.boogie.annotation.LTLPropertyCheck.CheckableExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BreakStatement;
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
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.SymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.ExpressionTranslation.AExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.ExpressionTranslation.BitvectorTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.ExpressionTranslation.IntegerTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.ArrayHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.FunctionHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.InitializationHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.LocalLValueILocationPair;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.PostProcessor;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.StructHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.TypeSizeAndOffsetComputer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.SymbolTableValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CNamed;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.GENERALPRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.PRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStruct;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CUnion;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CStorageClass;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CompoundStatementExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ContractResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.DeclarationResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.DeclaratorResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionListRecResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionListResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.SkipResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.TypesResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.BoogieASTUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ICHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.INameHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check.Spec;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.CodeAnnot;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Contract;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.GlobalLTLInvariant;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.CACSL2BoogieBacktranslator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.LTLExpressionExtractor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.POINTER_CHECKMODE;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.POINTER_INTEGER_CONVERSION;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.UNSIGNED_TREATMENT;

/**
 * Class that handles translation of C nodes to Boogie nodes.
 * 
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @author Matthias Heizmann
 */
public class CHandler implements ICHandler {

	/**
	 * If set to true we say Unsupported Syntax if there is some cast of pointers. Right now we are unable to handle
	 * casts of pointers soundly. However these soundness errors occur seldom.
	 */
	private final static boolean POINTER_CAST_IS_UNSUPPORTED_SYNTAX = false;

	private final MemoryHandler mMemoryHandler;

	private final ArrayHandler mArrayHandler;

	private final FunctionHandler mFunctionHandler;

	protected final StructHandler mStructHandler;

	private final PostProcessor mPostProcessor;

	protected final ITypeHandler mTypeHandler;

	private final INameHandler mNameHandler;

	private final InitializationHandler mInitHandler;

	/**
	 * Holds the next ACSL node in the decorator tree.
	 */
	private NextACSL mAcsl;
	/**
	 * Contract for next procedure
	 */
	protected final List<ACSLNode> mContract;
	/**
	 * The symbol table for the translation.
	 */
	protected final SymbolTable mSymbolTable;

	/**
	 * A set holding declarations of global variables required for variables, declared locally in C but required to be
	 * global in Boogie. e.g. constants for enums (in boogie constants may only be defined globally) or local static
	 * variables. Each declaration can have a set of initialization statements. So the procedure is: typeDeclarations:
	 * added to this map in IASTSimpleDeclaration, declared using this map in ITranslationUnit static variables: added
	 * to this map in IASTSimpleDeclaration, declared using this map in ITranslationUnit, initialized using this map in
	 * PostProcessor.createInit..() global variables: added to this map in IASTTranslationUnit, declared using this map
	 * in ITranslationUnit, initialized using this map in PostProcessor.createInit..()
	 */
	protected final LinkedHashMap<Declaration, CDeclaration> mDeclarationsGlobalInBoogie;

	/**
	 * A collection of axioms generated during translation process.
	 */
	protected final LinkedHashSet<Axiom> mAxioms;

	/**
	 * Translation from Boogie to C for traces and expressions.
	 */
	protected final CACSL2BoogieBacktranslator mBacktranslator;

	/**
	 * If set to true and the program contains an error label ULTIMATE shows a warning that suggests a different
	 * translation mode.
	 */
	protected final boolean mErrorLabelWarning;
	private final LinkedHashSet<String> mBoogieIdsOfHeapVars;

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
	protected ArrayDeque<TypesResult> mCurrentDeclaredTypes;

	/**
	 * Stores the labels of the loops we are currently inside. (For translation of a possible continue statement)
	 */
	private final Stack<String> mInnerMostLoopLabel;
	private final ILogger mLogger;

	private final CACSLPreferenceInitializer.UNSIGNED_TREATMENT mUnsignedTreatment;

	private final List<LTLExpressionExtractor> mGlobAcslExtractors;

	protected final AExpressionTranslation mExpressionTranslation;

	protected final TypeSizeAndOffsetComputer mTypeSizeComputer;

	/**
	 * Constructor.
	 * 
	 * @param main
	 *            a reference to the main dispatcher.
	 * @param backtranslator
	 *            a reference to the Backtranslator object.
	 * @param overapproximateFloatingPointOperations
	 * @param nameHandler
	 */
	public CHandler(Dispatcher main, CACSL2BoogieBacktranslator backtranslator, boolean errorLabelWarning,
			ILogger logger, ITypeHandler typeHandler, boolean bitvectorTranslation,
			boolean overapproximateFloatingPointOperations, INameHandler nameHandler) {

		mLogger = logger;
		mTypeHandler = typeHandler;
		mNameHandler = nameHandler;

		mUnsignedTreatment = main.getPreferences().getEnum(CACSLPreferenceInitializer.LABEL_UNSIGNED_TREATMENT,
				CACSLPreferenceInitializer.UNSIGNED_TREATMENT.class);

		mArrayHandler = new ArrayHandler(main.getPreferences());
		final boolean checkPointerValidity = main.getPreferences()
				.getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_POINTER_VALIDITY);

		mSymbolTable = new SymbolTable(main);

		mDeclarationsGlobalInBoogie = new LinkedHashMap<Declaration, CDeclaration>();
		mAxioms = new LinkedHashSet<Axiom>();
		mBacktranslator = backtranslator;
		mContract = new ArrayList<ACSLNode>();
		mErrorLabelWarning = errorLabelWarning;
		mInnerMostLoopLabel = new Stack<String>();

		mBoogieIdsOfHeapVars = new LinkedHashSet<String>();
		mCurrentDeclaredTypes = new ArrayDeque<TypesResult>();

		mGlobAcslExtractors = new ArrayList<>();

		final POINTER_INTEGER_CONVERSION pointerIntegerConversion = main.getPreferences().getEnum(
				CACSLPreferenceInitializer.LABEL_POINTER_INTEGER_CONVERSION,
				CACSLPreferenceInitializer.POINTER_INTEGER_CONVERSION.class);
		if (bitvectorTranslation) {
			mExpressionTranslation = new BitvectorTranslation(main.getTypeSizes(), typeHandler,
					pointerIntegerConversion, overapproximateFloatingPointOperations);
		} else {
			final boolean inRange = main.getPreferences()
					.getBoolean(CACSLPreferenceInitializer.LABEL_ASSUME_NONDET_VALUES_IN_RANGE);
			mExpressionTranslation = new IntegerTranslation(main.getTypeSizes(), typeHandler, mUnsignedTreatment,
					inRange, pointerIntegerConversion);
		}
		mPostProcessor = new PostProcessor(main, mLogger, mExpressionTranslation);
		mTypeSizeComputer = new TypeSizeAndOffsetComputer((TypeHandler) mTypeHandler, mExpressionTranslation,
				main.getTypeSizes());
		mFunctionHandler = new FunctionHandler(mExpressionTranslation, mTypeSizeComputer);
		final boolean smtBoolArraysWorkaround = main.getPreferences()
				.getBoolean(CACSLPreferenceInitializer.LABEL_SMT_BOOL_ARRAYS_WORKAROUND);
		mMemoryHandler = new MemoryHandler(typeHandler, mFunctionHandler, checkPointerValidity, mTypeSizeComputer,
				main.getTypeSizes(), mExpressionTranslation, bitvectorTranslation, nameHandler, smtBoolArraysWorkaround,
				main.getPreferences());
		mStructHandler = new StructHandler(mMemoryHandler, mTypeSizeComputer, mExpressionTranslation);
		mInitHandler = new InitializationHandler(mFunctionHandler, mStructHandler, mMemoryHandler,
				mExpressionTranslation);
	}

	@Override
	public Result visit(Dispatcher main, IASTNode node) {
		final String msg = "CHandler: Not yet implemented: \"" + node.getRawSignature() + "\" (Type: "
				+ node.getClass().getName() + ")";
		final ILocation loc = LocationFactory.createCLocation(node);
		throw new UnsupportedSyntaxException(loc, msg);
	}

	@Override
	public Result visit(Dispatcher main, IASTASMDeclaration node) {
		final String msg = "CHandler: Not yet implemented: \"" + node.getRawSignature() + "\" (Type: "
				+ node.getClass().getName() + ")";
		throw new UnsupportedSyntaxException(LocationFactory.createCLocation(node), msg);
	}

	/**
	 * @deprecated is not supported in this handler! Do not use!
	 */
	@Deprecated
	@Override
	public Result visit(Dispatcher main, ACSLNode node) {
		throw new UnsupportedOperationException("Implementation Error: Use ACSLHandler for: " + node.getClass());
	}

	@Override
	public Result visit(Dispatcher main, IASTTranslationUnit node) {

		for (final IASTPreprocessorStatement preS : node.getAllPreprocessorStatements()) {
			final Result r = main.dispatch(preS);
			if (!(r instanceof SkipResult)) {
				throw new UnsupportedOperationException("Not yet implemented " + preS.toString());
			}
		}
		final ILocation loc = LocationFactory.createCLocation(node);
		try {
			mAcsl = main.nextACSLStatement();
		} catch (final ParseException e1) {
			final String msg = "Skipped a ACSL node due to: " + e1.getMessage();
			main.unsupportedSyntax(loc, msg);
		}
		final ArrayList<Declaration> decl = new ArrayList<Declaration>();



		// TODO(thrax): Check if decl should be passed as null or not.
		checkForACSL(main, null, decl, node, null);

		// delayed processing of IASTFunctionDefinitions and structs
		// This is a workaround. Invariants my use global variables that
		// are not yet declared.
		// Better solution: obtain function signature in a first pass
		// process function body in a second pass
		final List<IASTNode> complexNodes = new ArrayList<>();
		for (final IASTNode child : node.getChildren()) {
			final String raw = child.getRawSignature();
			if (child instanceof IASTSimpleDeclaration) {
				final IASTSimpleDeclaration simpleDecl = (IASTSimpleDeclaration) child;
				if (simpleDecl.getDeclSpecifier() instanceof IASTElaboratedTypeSpecifier
						|| simpleDecl.getDeclSpecifier() instanceof ICASTCompositeTypeSpecifier
						|| (simpleDecl.getDeclarators().length > 0
								&& simpleDecl.getDeclarators()[0] instanceof CASTFunctionDeclarator)
						|| simpleDecl.getDeclSpecifier() instanceof IASTNamedTypeSpecifier) {
					complexNodes.add(child);
				} else {
					processTUchild(main, decl, child);
				}
			} else if (child instanceof IASTFunctionDefinition) {
				complexNodes.add(child);
			} else {
				processTUchild(main, decl, child);
			}
		}
		for (final IASTNode funcDef : complexNodes) {
			processTUchild(main, decl, funcDef);
		}

		// (alex:) new function pointers
		final BigInteger functionPointerPointerBaseValue = BigInteger.valueOf(-1);
		for (final Entry<String, Integer> en : main.getFunctionToIndex().entrySet()) {
			final String funcId = SFO.FUNCTION_ADDRESS + en.getKey();
			final VarList varList = new VarList(loc, new String[] { funcId }, mTypeHandler.constructPointerType(loc));
			decl.add(new ConstDeclaration(loc, new Attribute[0], false, varList, null, false));// would unique make
																								// sense here?? -- would
																								// potentially add lots
																								// of axioms
			final BigInteger offsetValue = BigInteger.valueOf(en.getValue());
			decl.add(new Axiom(loc, new Attribute[0], ExpressionFactory.newBinaryExpression(loc,
					BinaryExpression.Operator.COMPEQ, new IdentifierExpression(loc, funcId), mExpressionTranslation
							.constructPointerForIntegerValues(loc, functionPointerPointerBaseValue, offsetValue))));
		}

		for (final Declaration d : mDeclarationsGlobalInBoogie.keySet()) {
			assert d instanceof ConstDeclaration || d instanceof VariableDeclaration || d instanceof TypeDeclaration;
			decl.add(d);
		}
		decl.addAll(mAxioms);
		final String undeclaredFunction = mFunctionHandler.isEveryCalledProcedureDeclared();
		if (undeclaredFunction != null) {
			final String msg = "Following method was called but never declared! " + undeclaredFunction;
			throw new IncorrectSyntaxException(loc, msg);
		}

		decl.addAll(0,
				mPostProcessor.postProcess(main, loc, mMemoryHandler, mArrayHandler, mFunctionHandler, mStructHandler,
						(TypeHandler) mTypeHandler, mTypeHandler.getUndefinedTypes(), mDeclarationsGlobalInBoogie,
						mExpressionTranslation));

		// this has to happen after postprocessing as pping may add sizeof
		// constants for initializations
		decl.addAll(mTypeSizeComputer.getConstants());
		decl.addAll(mTypeSizeComputer.getAxioms());
		decl.addAll(mMemoryHandler.declareMemoryModelInfrastructure(main, loc));

		// add type declarations introduced by the translation, e.g., $Pointer$
		decl.addAll(((TypeHandler) mTypeHandler).constructTranslationDefiniedDelarations(loc, mExpressionTranslation));

		// have to block this in prerun, because there, Memorymodel is not declared which may make probelms with the
		// callgraph computation
		if (!(main instanceof PRDispatcher)) {
			// handle proc. declaration & resolve their transitive modified globals
			decl.addAll(mFunctionHandler.calculateTransitiveModifiesClause(main, mMemoryHandler));
		}

		final Collection<FunctionDeclaration> declaredFunctions = mExpressionTranslation.getFunctionDeclarations()
				.getDeclaredFunctions().values();
		decl.addAll(declaredFunctions);

		// handle global ACSL stuff
		// TODO: do it!

		// TODO(thrax): Check if decl should be passed as null.
		checkForACSL(main, null, decl, node, null);

		// the overall translation result:
		final Unit boogieUnit = new Unit(loc, decl.toArray(new Declaration[0]));

		// annotate the Unit with LTLPropertyChecks if applicable
		for (final LTLExpressionExtractor ex : mGlobAcslExtractors) {
			final Map<String, LTLPropertyCheck.CheckableExpression> checkableAtomicPropositions = new LinkedHashMap<String, LTLPropertyCheck.CheckableExpression>();

			for (final Entry<String, de.uni_freiburg.informatik.ultimate.model.acsl.ast.Expression> en : ex
					.getAP2SubExpressionMap().entrySet()) {
				final ExpressionResult r = (ExpressionResult) main.dispatch(en.getValue());
				// TODO: some switchToRValue and handling of sideeffects?
				checkableAtomicPropositions.put(en.getKey(), new CheckableExpression(r.lrVal.getValue(), null));
			}
			final LTLPropertyCheck propCheck = new LTLPropertyCheck(ex.getLTLFormatString(), checkableAtomicPropositions,
					null);
			propCheck.annotate(boogieUnit);
		}

		return new Result(boogieUnit);
	}

	private void processTUchild(Dispatcher main, ArrayList<Declaration> decl, IASTNode child) {
		checkForACSL(main, null, decl, child, null);
		final Result childRes = main.dispatch(child);

		if (childRes instanceof DeclarationResult) {
			// we have to add a global variable
			final DeclarationResult rd = (DeclarationResult) childRes;
			for (final CDeclaration cd : rd.getDeclarations()) {
				mDeclarationsGlobalInBoogie.put(mSymbolTable.getBoogieDeclOfCDecl(cd), cd);
			}
		} else {
			if (childRes instanceof SkipResult) {
				return;
			}
			assert childRes.getClass() == Result.class;
			assert childRes.node != null;
			decl.add((Declaration) childRes.node);
		}
	}

	@Override
	public Result visit(Dispatcher main, IASTFunctionDefinition node) {
		final LinkedHashSet<IASTDeclaration> reachableDecs = main.getReachableDeclarationsOrDeclarators();
		if (reachableDecs != null) {
			if (!reachableDecs.contains(node)) {
				return new SkipResult();
			}
		}

		final TypesResult resType = (TypesResult) main.dispatch(node.getDeclSpecifier());

		mCurrentDeclaredTypes.push(resType);
		final DeclaratorResult declResult = (DeclaratorResult) main.dispatch(node.getDeclarator());
		mCurrentDeclaredTypes.pop();
		return mFunctionHandler.handleFunctionDefinition(main, mMemoryHandler, node, declResult.getDeclaration(),
				mContract);
	}

	@Override
	public Result visit(Dispatcher main, IASTCompoundStatement node) {
		final ILocation loc = LocationFactory.createCLocation(node);
		final ArrayList<Declaration> decl = new ArrayList<Declaration>();
		ArrayList<Statement> stmt = new ArrayList<Statement>();
		LRValue expr = null;
		final IASTNode parent = node.getParent();

		if (isNewScopeRequired(parent)) {
			beginScope();
		}

		for (final IASTNode child : node.getChildren()) {
			final String raw = child.getRawSignature();
			checkForACSL(main, stmt, decl, child, null);
			final Result r = main.dispatch(child);
			if (r instanceof ExpressionResult) {
				final ExpressionResult res = (ExpressionResult) r;
				// assert (res.auxVars.isEmpty()) : "unhavoced auxvars";
				decl.addAll(res.decl);
				stmt.addAll(res.stmt);
				expr = res.lrVal;
			} else if (r instanceof CompoundStatementExpressionResult) {
				final CompoundStatementExpressionResult res = (CompoundStatementExpressionResult) r;
				decl.addAll(res.decl);
				stmt.addAll(res.stmt);
				expr = res.lrVal;
			} else if (r.node != null && r.node instanceof Body) {
				assert false : "should not happen, as CompoundStatement now yields an "
						+ "ExpressionResult or a CompoundStatementExpressionResult";
				// already have a unique naming for variables! --> unfold
				final Body b = ((Body) r.node);
				decl.addAll(Arrays.asList(b.getLocalVars()));
				stmt.addAll(Arrays.asList(b.getBlock()));
			} else if (r instanceof SkipResult) {
				// skip
			} else {
				assert false : "should not happen, as CompoundStatement now yields an "
						+ "ExpressionResult or a CompoundStatementExpressionResult";
			}
		}
		checkForACSL(main, stmt, decl, null, node);
		if (isNewScopeRequired(parent)) {
			stmt = updateStmtsAndDeclsAtScopeEnd(main, decl, stmt);

			endScope();
		}
		// return new Result(new Body(loc, decl.toArray(new VariableDeclaration[0]), stmt.toArray(new Statement[0])));
		return new CompoundStatementExpressionResult(stmt, expr, decl, new HashMap<VariableDeclaration, ILocation>(),
				new ArrayList<Overapprox>());
	}

	/**
	 * At the end of a scope, typically a C compound statement, we need to insert some mallocs and frees surrounding the
	 * stmt block, and we need to insert all the declarations that are needed for that block, according to the symbol
	 * table. (at the dispatch of a simple declaration, the declarations are stored in the symbol table)
	 */
	public ArrayList<Statement> updateStmtsAndDeclsAtScopeEnd(Dispatcher main, ArrayList<Declaration> decl,
			ArrayList<Statement> stmt) {
		stmt = mMemoryHandler.insertMallocs(main, stmt);
		for (final SymbolTableValue stv : mSymbolTable.currentScopeValues()) {
			// there may be a null declaration in case of foo(void) -- therefore we need to check the second conjunct
			// (case where this is called from FunctionHandler.handleFunctionDefinition)
			if (!stv.isBoogieGlobalVar() && stv.getBoogieDecl() != null) {
				decl.add(stv.getBoogieDecl());
			}
		}
		return stmt;
	}

	/**
	 * Visit the SimpleDeclaration (which may be quite complex in fact..). The return value here may have different
	 * uses: - for global variables and declarations inside of struct definitions, it is a ResultDeclaration (containing
	 * the Boogie Declaration of the variable) - for local variables that have an initializer, a ResultExpression is
	 * returned which contains (Boogie) statements and declarations that make the initialization according to the
	 * initializer for local variables without an initializer, a havoc statement is inserted into the ResultExpression
	 * instead The declarations themselves of the local variables (and f.i. typedefs) are stored in the symbolTable and
	 * inserted into the Boogie code at the next endScope() Declarations of static variables are added to
	 * mDeclarationsGlobalInBoogie such that they can be declared and initialized globally. Variables/types that are
	 * global in Boogie but not in C are stored in the Symboltable to keep the association of BoogieId and CId.
	 */
	@Override
	public Result visit(Dispatcher main, IASTSimpleDeclaration node) {
		final LinkedHashSet<IASTDeclaration> reachableDecs = main.getReachableDeclarationsOrDeclarators();
		if (reachableDecs != null) {
			if (node.getParent() instanceof IASTTranslationUnit) {
				if (!reachableDecs.contains(node)) {
					boolean skip = true;
					for (final IASTDeclarator d : node.getDeclarators()) {
						if (reachableDecs.contains(d)) {
							skip = false;
						}
					}
					if (reachableDecs.contains(node.getDeclSpecifier())) {
						skip = false;
					}
					if (skip) {
						return new SkipResult();
					}
				}
			}
		}

		final ILocation loc = LocationFactory.createCLocation(node);
		if (node.getDeclSpecifier() == null) {
			final String msg = "This statement can be removed!";
			main.warn(loc, msg);
			return new SkipResult();
		}

		// enum case
		if (node.getDeclSpecifier() instanceof IASTEnumerationSpecifier) {
			handleEnumDeclaration(main, node);
		}

		final Result r = main.dispatch(node.getDeclSpecifier());
		assert r instanceof SkipResult || r instanceof TypesResult;
		if (r instanceof SkipResult) {
			return r;
		}
		if (r instanceof TypesResult) {
			final TypesResult resType = (TypesResult) r;
			Result result = new SkipResult(); // Skip will be overwritten in
												// case of a global or a local
												// initialized variable

			final CStorageClass storageClass = scConstant2StorageClass(node.getDeclSpecifier().getStorageClass());

			mCurrentDeclaredTypes.push(resType);
			/**
			 * Christian: C allows several declarations of "similar" types in one go. For instance:
			 * <code>int a, b[2];</code> Here <code>a</code> has type <code>int</code> and <code>b</code> has type
			 * <code>int[]</code>. To solve this, the declaration items are visited one after another.
			 */
			for (final IASTDeclarator d : node.getDeclarators()) {
				// if (d instanceof IASTFieldDeclarator)
				// throw new UnsupportedSyntaxException(loc, "bitfields are not supported at the moment");

				final DeclaratorResult declResult = (DeclaratorResult) main.dispatch(d);

				final CDeclaration cDec = declResult.getDeclaration();
				cDec.setStorageClass(storageClass);

				// are we in prerun mode?
				if (main instanceof PRDispatcher) {
					// all unions should be on heap
					if (cDec.getType() instanceof CUnion && storageClass != CStorageClass.TYPEDEF) {
						((PRDispatcher) main).getVariablesOnHeap().add(d);
					}
				}

				///////////////////
				// update symbol table

				// functions keep their cId, and their declaration is not stored
				// in the symbolTable but in
				// FunctionHandler.procedures.
				if (cDec.getType() instanceof CFunction && storageClass != CStorageClass.TYPEDEF) {
					// update functionHandler.procedures instead of symbol table
					mFunctionHandler.handleFunctionDeclarator(main, LocationFactory.createCLocation(d), mContract,
							cDec);
					continue;
				}

				// if the same variable is declared multiple times (within the same scope), we only keep one declaration
				// if one of them has an initializer, we keep that one.
				// if we are inside a struct declaration however, this does not apply, we proceed as normal, as the
				// result
				// is needed to build the struct type
				if (!mTypeHandler.isStructDeclaration() && mSymbolTable.existsInCurrentScope(cDec.getName())) {
					if (cDec.hasInitializer()) {
						// undo the effects of the old declaration
						if (mFunctionHandler.noCurrentProcedure() && !mTypeHandler.isStructDeclaration()) {
							mDeclarationsGlobalInBoogie.remove(mSymbolTable.get(cDec.getName(), loc).getBoogieDecl());
						}
						// local variable may not be a problem, because symboltable will overwrite at put
						// .. or are they not allowed in C?... TODO --> should look it up in standard
						// if that is the case, then this code section may be simplified, probably..
					} else {
						// this variable has already been declared, and the current declaration does not have an
						// initializer
						// --> skip the current declaration
						continue;
					}
				}

				final boolean onHeap = cDec.isOnHeap();
				final String bId = mNameHandler.getUniqueIdentifier(node, cDec.getName(), mSymbolTable.getCompoundCounter(),
						onHeap, cDec.getType());
				if (onHeap) {
					mBoogieIdsOfHeapVars.add(bId);
				}

				Declaration boogieDec = null;
				boolean globalInBoogie = false;

				// this .put() is only to have a minimal symbolTableEntry
				// (containing boogieID) for
				// translation of the initializer
				mSymbolTable.put(cDec.getName(), new SymbolTableValue(bId, boogieDec, cDec, globalInBoogie, d));
				cDec.translateInitializer(main);

				ASTType translatedType = null;
				if (onHeap) {
					translatedType = mTypeHandler.constructPointerType(loc);
				} else {
					translatedType = mTypeHandler.ctype2asttype(loc, cDec.getType());
				}

				if (storageClass == CStorageClass.TYPEDEF) {
					boogieDec = new TypeDeclaration(loc, new Attribute[0], false, bId, new String[0], translatedType);
					mTypeHandler.addDefinedType(bId,
							new TypesResult(new NamedType(loc, cDec.getName(), null), false, false, cDec.getType()));
					// TODO: add a sizeof-constant for the type??
					globalInBoogie = true;
					mDeclarationsGlobalInBoogie.put(boogieDec, cDec);
				} else if (storageClass == CStorageClass.STATIC && !mFunctionHandler.noCurrentProcedure()) {
					// we have a local static variable -> special treatment
					// global static variables are treated like normal global variables..
					boogieDec = new VariableDeclaration(loc, new Attribute[0],
							new VarList[] { new VarList(loc, new String[] { bId }, translatedType) });
					globalInBoogie = true;
					mDeclarationsGlobalInBoogie.put(boogieDec, cDec);
				} else {
					/**
					 * For Variable length arrays we have a "non-real" initializer which just initializes the aux var
					 * for the array's size. We do not want to treat this like other initializers (call initVar and so).
					 */
					final boolean hasRealInitializer = cDec.hasInitializer() && !(cDec.getType() instanceof CArray
							&& !(cDec.getInitializer() instanceof ExpressionListRecResult));

					if (!hasRealInitializer && !mFunctionHandler.noCurrentProcedure()
							&& !mTypeHandler.isStructDeclaration()) {
						// in case of a local variable declaration without an
						// initializer, we need to insert a
						// havoc statement (because otherwise the variable is
						// always the same within a loop which
						// may lead to unsoundness)
						// ..except if OnHeap. Then it is malloced instead.
						// (--> this is done below this ite-branching by
						// memoryHandler.addVariableToBeMallocedAndFreed(...))
						assert result instanceof SkipResult || result instanceof ExpressionResult;

						if (result instanceof SkipResult) {
							result = new ExpressionResult((LRValue) null);
						}

						final VariableLHS lhs = new VariableLHS(loc, bId);

						if (cDec.hasInitializer()) { // must be a non-real initializer for variable length array size
														// --> need to pass this on
							((ExpressionResult) result).decl.addAll(cDec.getInitializer().decl);
							((ExpressionResult) result).stmt.addAll(cDec.getInitializer().stmt);
							((ExpressionResult) result).auxVars.putAll(cDec.getInitializer().auxVars);
						}

						// no initializer --> essentially needs to be havoced f.i. in each loop iteration
						if (!onHeap) {
							((ExpressionResult) result).stmt.add(new HavocStatement(loc, new VariableLHS[] { lhs }));
						} else {
							final LocalLValue llVal = new LocalLValue(lhs, cDec.getType());
							// old solution: havoc via an auxvar, new solution (below):
							// just malloc at the right place (much shorter for arrays and structs..)
							((ExpressionResult) result).stmt
									.add(mMemoryHandler.getMallocCall(main, mFunctionHandler, llVal, loc));
							mMemoryHandler.addVariableToBeFreed(main,
									new LocalLValueILocationPair(llVal, LocationFactory.createIgnoreLocation(loc)));
						}
					} else if (hasRealInitializer && !mFunctionHandler.noCurrentProcedure()
							&& !mTypeHandler.isStructDeclaration()) {
						// in case of a local variable declaration with an initializer, the statements and delcs
						// necessary for the initialization are the result
						assert result instanceof SkipResult || result instanceof ExpressionResult;
						final VariableLHS lhs = new VariableLHS(loc, bId);
						final ExpressionResult initRex = mInitHandler.initVar(loc, main, lhs, cDec.getType(),
								cDec.getInitializer());
						if (result instanceof SkipResult) {
							result = new ExpressionResult((LRValue) null);
						}

						if (onHeap) {
							final LocalLValue llVal = new LocalLValue(lhs, cDec.getType());
							mMemoryHandler.addVariableToBeFreed(main, new LocalLValueILocationPair(llVal, loc));
							((ExpressionResult) result).stmt
									.add(mMemoryHandler.getMallocCall(main, mFunctionHandler, llVal, loc));
						}

						((ExpressionResult) result).stmt.addAll(initRex.stmt);
						((ExpressionResult) result).stmt.addAll(createHavocsForAuxVars(initRex.auxVars));
						((ExpressionResult) result).decl.addAll(initRex.decl);
						((ExpressionResult) result).overappr.addAll(initRex.overappr);
					} else {
						// in case of global variables, the result is the
						// declaration, initialization is
						// done in the postProcessor
						// in case this simpleDeclaration is part of a struct
						// definition, we also need the
						// Declarations as a result
						assert result instanceof SkipResult || result instanceof DeclarationResult;
						if (result instanceof SkipResult) {
							result = new DeclarationResult();
						}
						((DeclarationResult) result).addDeclaration(cDec);
					}
					boogieDec = new VariableDeclaration(loc, new Attribute[0],
							new VarList[] { new VarList(loc, new String[] { bId }, translatedType) });
					globalInBoogie |= mFunctionHandler.noCurrentProcedure();
				}

				mSymbolTable.put(cDec.getName(), new SymbolTableValue(bId, boogieDec, cDec, globalInBoogie, d));
			}
			mCurrentDeclaredTypes.pop();

			// Matthias 19-09-2015: I commented the following. Havoc'ing here is
			// too early.
			// if (result instanceof ExpressionResult)
			// ((ExpressionResult) result).stmt.addAll(
			// createHavocsForAuxVars(((ExpressionResult) result).auxVars));
			return result;
		}
		final String msg = "Unknown result type: " + r.getClass();
		throw new UnsupportedSyntaxException(loc, msg);
	}

	@Override
	public Result visit(Dispatcher main, IASTParameterDeclaration node) {
		final TypesResult resType = (TypesResult) main.dispatch(node.getDeclSpecifier());

		mCurrentDeclaredTypes.push(resType);
		final DeclaratorResult declResult = (DeclaratorResult) main.dispatch(node.getDeclarator());
		mCurrentDeclaredTypes.pop();
		return declResult;
	}

	@Override
	public Result visit(Dispatcher main, IASTDeclarator node) {
		final ILocation loc = LocationFactory.createCLocation(node);
		final TypesResult resType = mCurrentDeclaredTypes.peek();
		final TypesResult newResType = new TypesResult(resType);

		newResType.isOnHeap |= main instanceof MainDispatcher
				? ((MainDispatcher) main).getVariablesForHeap().contains(node) : false; // in this case we are in the
																						// PRDispatcher

		final IASTPointerOperator[] pointerOps = node.getPointerOperators();
		for (int i = 0; i < pointerOps.length; i++) {
			newResType.cType = new CPointer(newResType.cType);
		}
		final ExpressionResult variableLengthArrayAuxVarInitializer = null;

		if (node instanceof IASTArrayDeclarator) {
			final IASTArrayDeclarator arrDecl = (IASTArrayDeclarator) node;

			final ArrayList<RValue> size = new ArrayList<RValue>();
			// expression results of from array modifiers
			final ArrayList<ExpressionResult> expressionResults = new ArrayList<ExpressionResult>();

			for (final IASTArrayModifier am : arrDecl.getArrayModifiers()) {
				final RValue sizeFactor;
				if (am.getConstantExpression() != null) {
					// case where we have a number between the brackets,
					// e.g., a[23] or a[n+1]
					ExpressionResult er = (ExpressionResult) main.dispatch(am.getConstantExpression());
					er = er.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
					// FIXME: 2015-10-25 Matthias: uncomment once the simplification of Boogie expressions is
					// implemented
					mExpressionTranslation.convertIntToInt(loc, er,
							mExpressionTranslation.getCTypeOfPointerComponents());
					expressionResults.add(er);
					sizeFactor = (RValue) er.lrVal;
				} else if (am.getConstantExpression() == null
						&& arrDecl.getArrayModifiers()[arrDecl.getArrayModifiers().length - 1] == am) {
					// the innermost array modifier may be empty, if there is an initializer; like int a[1][2][] = {...}
					final int intSizeFactor;
					if (arrDecl.getInitializer() != null) {
						assert arrDecl.getInitializer() instanceof IASTEqualsInitializer;
						final IASTEqualsInitializer eqInit = ((IASTEqualsInitializer) arrDecl.getInitializer());
						assert eqInit.getInitializerClause() instanceof IASTInitializerList;
						final IASTInitializerList initList = (IASTInitializerList) eqInit.getInitializerClause();
						intSizeFactor = initList.getSize();
					} else {
						// we have an incomplete array type without an initializer --
						// this may happen in a function parameter..
						intSizeFactor = -1234567;
					}
					final CPrimitive ctype = mExpressionTranslation.getCTypeOfPointerComponents();
					final Expression sizeExpression = mExpressionTranslation.constructLiteralForIntegerType(loc, ctype,
							BigInteger.valueOf(intSizeFactor));
					sizeFactor = new RValue(sizeExpression, ctype, false, false);

				} else {
					throw new IncorrectSyntaxException(loc, "wrong array type in declaration");
				}
				size.add(sizeFactor);
			}
			final ExpressionResult allResults = ExpressionResult.copyStmtDeclAuxvarOverapprox(
					expressionResults.toArray(new ExpressionResult[expressionResults.size()]));
			if (!allResults.decl.isEmpty() || !allResults.stmt.isEmpty() || !allResults.auxVars.isEmpty()) {
				throw new AssertionError("passing these results is not yet implemented");
			}
			final CArray arrayType = new CArray(size.toArray(new RValue[size.size()]), newResType.cType);
			newResType.cType = arrayType;

		} else if (node instanceof CASTFunctionDeclarator) {
			final CASTFunctionDeclarator funcDecl = (CASTFunctionDeclarator) node;

			final IASTParameterDeclaration[] paramDecls = funcDecl.getParameters();
			CDeclaration[] paramsParsed = new CDeclaration[paramDecls.length];
			for (int i = 0; i < paramDecls.length; i++) {
				final DeclaratorResult decl = (DeclaratorResult) main.dispatch(paramDecls[i]);
				if (decl.getDeclaration().getName() == "" && decl.getDeclaration().getType() instanceof CPrimitive
						&& ((CPrimitive) decl.getDeclaration().getType()).getType().equals(PRIMITIVE.VOID)) {
					assert paramDecls.length == 1;
					paramsParsed = new CDeclaration[0];
					break;
				}
				paramsParsed[i] = decl.getDeclaration();
			}
			final CFunction funcType = new CFunction(newResType.cType, paramsParsed, funcDecl.takesVarArgs());
			newResType.cType = funcType;
		} else if (node instanceof CASTDeclarator) {
			/* nothing */
		} else {
			throw new UnsupportedSyntaxException(loc, "Unknown Declarator " + node.getClass());
		}
		if (node.getNestedDeclarator() != null) {
			mCurrentDeclaredTypes.push(newResType);
			DeclaratorResult result = (DeclaratorResult) main.dispatch(node.getNestedDeclarator());
			mCurrentDeclaredTypes.pop();
			if (node.getInitializer() != null) {
				final CDeclaration cdec = result.getDeclaration();
				result = new DeclaratorResult(new CDeclaration(cdec.getType(), cdec.getName(), node.getInitializer(),
						variableLengthArrayAuxVarInitializer, cdec.isOnHeap(), CStorageClass.UNSPECIFIED));
			}
			return result;
		} else {
			final DeclaratorResult result = new DeclaratorResult(
					new CDeclaration(newResType.cType, node.getName().toString(), node.getInitializer(),
							variableLengthArrayAuxVarInitializer, newResType.isOnHeap, CStorageClass.UNSPECIFIED));
			return result;
		}
	}

	@Override
	public Result visit(Dispatcher main, IASTLiteralExpression node) {
		return mExpressionTranslation.translateLiteral(main, node);
	}

	@Override
	public Result visit(Dispatcher main, IASTIdExpression node) {
		final ILocation loc = LocationFactory.createCLocation(node);
		final String cId = node.getName().toString();

		// deal with builtin constants
		if (cId.equals("NULL")) {
			return new ExpressionResult(new RValue(mExpressionTranslation.constructNullPointer(loc),
					new CPointer(new CPrimitive(PRIMITIVE.VOID))));
		} else if (cId.equals("NAN") || cId.equals("INFINITY") || cId.equals("inf")) {
			final ExpressionResult result = mExpressionTranslation.createNanOrInfinity(loc, cId);
			return result;
		} else if (node.getName().toString().equals("__func__")) {
			final CType cType = new CPointer(new CPrimitive(PRIMITIVE.CHAR));
			final String tId = mNameHandler.getTempVarUID(SFO.AUXVAR.NONDET, cType);
			final VariableDeclaration tVarDecl = new VariableDeclaration(loc, new Attribute[0],
					new VarList[] { new VarList(loc, new String[] { tId }, mTypeHandler.constructPointerType(loc)) });
			final RValue rvalue = new RValue(new IdentifierExpression(loc, tId), cType);
			final ArrayList<Declaration> decls = new ArrayList<Declaration>();
			decls.add(tVarDecl);
			final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>();
			auxVars.put(tVarDecl, loc);
			return new ExpressionResult(new ArrayList<Statement>(), rvalue, decls, auxVars);
		}

		final String bId;
		final CType cType;
		final boolean useHeap;
		final boolean intFromPtr;

		if (mSymbolTable.containsCSymbol(cId)) {
			// we have a normal variable
			bId = mSymbolTable.get(cId, loc).getBoogieName();
			cType = mSymbolTable.get(cId, loc).getCVariable();
			useHeap = isHeapVar(bId);
			intFromPtr = mSymbolTable.get(cId, loc).isIntFromPointer;
		} else if (mFunctionHandler.getProcedures().keySet().contains(cId)) {
			// C11 6.3.2.1.4 says: A function designator is an expression that
			// has function type.
			final CFunction cFunction = mFunctionHandler.getCFunctionType(cId);
			cType = cFunction;
			bId = SFO.FUNCTION_ADDRESS + cId;
			useHeap = true;
			intFromPtr = false;
		} else if (main.getFunctionToIndex().containsKey(cId)) {
			throw new AssertionError("function not known to function handler");
		} else {
			throw new UnsupportedSyntaxException(loc,
					"identifier is not declared (neither a variable nor a function name): " + cId);
		}

		LRValue lrVal = null;
		if (useHeap) {
			final IdentifierExpression idExp = new IdentifierExpression(loc, bId);
			// convention: the ctype in the symbol table of something that we put on the heap
			// is the same as it would be if we did not put it on heap
			lrVal = new HeapLValue(idExp, cType, intFromPtr);
		} else {
			final VariableLHS idLhs = new VariableLHS(loc, bId);
			lrVal = new LocalLValue(idLhs, cType, false, intFromPtr);
		}
		return new ExpressionResult(lrVal);
	}

	@Override
	public Result visit(Dispatcher main, IASTUnaryExpression node) {
		final ExpressionResult o = (ExpressionResult) main.dispatch(node.getOperand());
		final ILocation loc = LocationFactory.createCLocation(node);

		// for the cases we know that it's an RValue..
		// ResultExpression rop = o.switchToRValueIfNecessary(main,
		// memoryHandler, structHandler, loc);

		CType oType = o.lrVal.getCType();
		if (oType instanceof CNamed) {
			oType = ((CNamed) oType).getUnderlyingType();
		}

		switch (node.getOperator()) {
		case IASTUnaryExpression.op_minus:
		case IASTUnaryExpression.op_not:
		case IASTUnaryExpression.op_plus:
		case IASTUnaryExpression.op_tilde: {
			final ExpressionResult rop = o.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
			return handleUnaryArithmeticOperators(main, loc, node.getOperator(), rop);
		}
		case IASTUnaryExpression.op_postFixIncr:
		case IASTUnaryExpression.op_postFixDecr: {
			return handlePostfixIncrementAndDecrement(main, loc, node.getOperator(), o);
		}
		case IASTUnaryExpression.op_prefixDecr:
		case IASTUnaryExpression.op_prefixIncr: {
			return handlePrefixIncrementAndDecrement(main, node.getOperator(), loc, o);
		}
		case IASTUnaryExpression.op_bracketedPrimary:
			return o;
		case IASTUnaryExpression.op_sizeof:
			final Map<VariableDeclaration, ILocation> emptyAuxVars = new LinkedHashMap<VariableDeclaration, ILocation>(0);
			return new ExpressionResult(
					new RValue(mMemoryHandler.calculateSizeOf(loc, oType), new CPrimitive(PRIMITIVE.INT)),
					emptyAuxVars);
		case IASTUnaryExpression.op_star: {
			return handleIndirectionOperator(main, o, loc);
		}
		case IASTUnaryExpression.op_amper: {
			return handleAddressOfOperator(main, o, loc);
		}
		case IASTUnaryExpression.op_alignOf:
		default:
			final String msg = "Unknown or unsupported unary operation: " + node.getOperator();
			throw new UnsupportedSyntaxException(loc, msg);
		}
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
	private Result handlePrefixIncrementAndDecrement(Dispatcher main, int prefixOp, ILocation loc,
			ExpressionResult exprRes) {
		assert !exprRes.lrVal.isBoogieBool();
		final LRValue modifiedLValue = exprRes.lrVal;
		exprRes = exprRes.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
		final ExpressionResult result = ExpressionResult.copyStmtDeclAuxvarOverapprox(exprRes);

		// In this case we need a temporary variable for the new value
		final String tmpName = mNameHandler.getTempVarUID(SFO.AUXVAR.PRE_MOD, exprRes.lrVal.getCType());
		final ASTType tmpIType = mTypeHandler.ctype2asttype(loc, exprRes.lrVal.getCType());
		final VariableDeclaration tmpVar = SFO.getTempVarVariableDeclaration(tmpName, tmpIType, loc);
		result.auxVars.put(tmpVar, loc);
		result.decl.add(tmpVar);

		final int op;
		if (prefixOp == IASTUnaryExpression.op_prefixIncr) {
			op = IASTBinaryExpression.op_plus;
		} else if (prefixOp == IASTUnaryExpression.op_prefixDecr) {
			op = IASTBinaryExpression.op_minus;
		} else {
			throw new AssertionError("no prefix");
		}

		final CType oType = exprRes.lrVal.getCType().getUnderlyingType();
		// in-/decremented value
		final Expression valueXcremented = constructXcrementedValue(main, loc, result, oType, op,
				exprRes.lrVal.getValue());

		// assign the old value to the temporary variable
		final AssignmentStatement assignStmt;
		{
			final LeftHandSide[] tmpAsLhs = new LeftHandSide[] { new VariableLHS(loc, tmpName) };
			final Expression[] newValue = new Expression[] { valueXcremented };
			assignStmt = new AssignmentStatement(loc, tmpAsLhs, newValue);
		}
		result.stmt.add(assignStmt);

		final RValue rhs = new RValue(valueXcremented, oType, false, false);
		final ExpressionResult assign = makeAssignment(loc, result.stmt, modifiedLValue, rhs, result.decl,
				result.auxVars, result.overappr);

		final RValue tmpRValue = new RValue(new IdentifierExpression(loc, tmpName), oType);
		assign.lrVal = tmpRValue;
		return assign;
	}

	/**
	 * Handle postfix increment and decrement operators according to Section 6.5.2.4 of C11. We translate the expression
	 * <code>LV++</code> to an auxiliary variable <code>t~post</code> and add to the resulting {@link ExpressionResult}
	 * the two assignments <code>t~post := LV</code> and <code>LV := t~post + 1</code>. Hence the auxiliary variable
	 * <code>t~post</code> stores the old value of the object to which the lvalue <code>LV</code> refers.
	 */
	private Result handlePostfixIncrementAndDecrement(Dispatcher main, ILocation loc, int postfixOp,
			ExpressionResult exprRes) {
		assert !exprRes.lrVal.isBoogieBool();
		final LRValue modifiedLValue = exprRes.lrVal;
		exprRes = exprRes.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
		final ExpressionResult result = ExpressionResult.copyStmtDeclAuxvarOverapprox(exprRes);

		// In this case we need a temporary variable for the old value
		final String tmpName = mNameHandler.getTempVarUID(SFO.AUXVAR.POST_MOD, exprRes.lrVal.getCType());
		final ASTType tmpIType = mTypeHandler.ctype2asttype(loc, exprRes.lrVal.getCType());
		final VariableDeclaration tmpVar = SFO.getTempVarVariableDeclaration(tmpName, tmpIType, loc);
		result.auxVars.put(tmpVar, loc);
		result.decl.add(tmpVar);

		// assign the old value to the temporary variable
		final AssignmentStatement assignStmt;
		{
			final LeftHandSide[] tmpAsLhs = new LeftHandSide[] { new VariableLHS(loc, tmpName) };
			final Expression[] oldValue = new Expression[] { exprRes.lrVal.getValue() };
			assignStmt = new AssignmentStatement(loc, tmpAsLhs, oldValue);
		}
		result.stmt.add(assignStmt);
		final CType oType = exprRes.lrVal.getCType().getUnderlyingType();
		final RValue tmpRValue = new RValue(new IdentifierExpression(loc, tmpName), oType);

		final int op;
		if (postfixOp == IASTUnaryExpression.op_postFixIncr) {
			op = IASTBinaryExpression.op_plus;
		} else if (postfixOp == IASTUnaryExpression.op_postFixDecr) {
			op = IASTBinaryExpression.op_minus;
		} else {
			throw new AssertionError("no postfix");
		}

		// in-/decremented value
		final Expression valueXcremented = constructXcrementedValue(main, loc, result, oType, op, tmpRValue.getValue());

		final RValue rhs = new RValue(valueXcremented, oType, false, false);
		final ExpressionResult assign = makeAssignment(loc, result.stmt, modifiedLValue, rhs, result.decl,
				result.auxVars, result.overappr);
		assign.lrVal = tmpRValue;
		return assign;
	}

	/**
	 * Increment or decrement an expression. Construct expression that represents the value of the input expression but
	 * is incremented or decremented by one. If op is IASTBinaryExpression.op_plus we increment, if op is
	 * IASTBinaryExpression.op_minus we decrement. If ctype is CPrimitive, we increment/decrement by one and also call
	 * the method that adds (depending on the settings) an overflow check. If ctype is CPointer, we increment/decrement
	 * by the size of the pointsToType and call the method that adds (depending on the settings) an check if the pointer
	 * arithmetic was legal.
	 */
	private Expression constructXcrementedValue(Dispatcher main, ILocation loc, final ExpressionResult result,
			final CType ctype, final int op, final Expression value) {
		assert (op == IASTBinaryExpression.op_plus
				|| op == IASTBinaryExpression.op_minus) : "has to be either minus or plus";
		final Expression valueIncremented;
		if (ctype instanceof CPointer) {
			final CPointer cPointer = (CPointer) ctype;
			final Expression oneEpr = mExpressionTranslation.constructLiteralForIntegerType(loc,
					mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ONE);
			final CPrimitive oneType = mExpressionTranslation.getCTypeOfPointerComponents();
			final RValue one = new RValue(oneEpr, oneType);
			valueIncremented = mMemoryHandler.doPointerArithmetic(op, loc, value, one, cPointer.pointsToType);
			addOffsetInBoundsCheck(main, loc, valueIncremented, result);
		} else if (ctype instanceof CPrimitive) {
			final CPrimitive cPrimitive = (CPrimitive) ctype;
			final Expression one = mExpressionTranslation.constructLiteralForIntegerType(loc, cPrimitive, BigInteger.ONE);
			addIntegerBoundsCheck(main, loc, result, cPrimitive, op, value, one);
			valueIncremented = mExpressionTranslation.constructArithmeticExpression(loc, op, value, cPrimitive, one,
					cPrimitive);
		} else {
			throw new IllegalArgumentException("input has to be CPointer or CPrimitive");
		}
		return valueIncremented;
	}

	/**
	 * Handle the address operator according to Section 6.5.3.2 of C11.
	 */
	private Result handleAddressOfOperator(Dispatcher main, ExpressionResult er, ILocation loc) throws AssertionError {
		final RValue ad;
		if (er.lrVal instanceof HeapLValue) {
			ad = new RValue(((HeapLValue) er.lrVal).getAddress(), new CPointer(er.lrVal.getCType()));
		} else if (er.lrVal instanceof LocalLValue) {
			if (main instanceof PRDispatcher) {
				// We are in the prerun mode.
				// As a workaround, we (incorrectly) return the value
				// instead of the address. But we add variables to the
				// heapVars and hence in the non-prerun mode the input
				// will be a HeapLValue instead of a LocalLValue.
				final Expression expr = er.lrVal.getValue();
				if (expr instanceof IdentifierExpression) {
					final IdentifierExpression idExpr = (IdentifierExpression) expr;
					((PRDispatcher) main).moveIdOnHeap(loc, idExpr);
				} else {
					((PRDispatcher) main).moveArrayAndStructIdsOnHeap(loc, expr, er.auxVars);
				}
				ad = new RValue(expr, new CPointer(er.lrVal.getCType()));
			} else {
				throw new AssertionError("cannot take address of LocalLValue: this is a on-heap/off-heap bug");
			}
		} else if (er.lrVal instanceof RValue) {
			throw new AssertionError("cannot take address of RValue");
		} else {
			throw new AssertionError("Unknown value");
		}
		final ExpressionResult result = ExpressionResult.copyStmtDeclAuxvarOverapprox(er);
		result.lrVal = ad;
		return result;
	}

	/**
	 * Handle the indirection operator according to Section 6.5.3.2 of C11. (The indirection operator is the star for
	 * pointer dereference.)
	 */
	private Result handleIndirectionOperator(Dispatcher main, ExpressionResult er, ILocation loc) {
		final ExpressionResult rop = er.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
		final RValue rValue = (RValue) rop.lrVal;
		if (!(rValue.getCType().getUnderlyingType() instanceof CPointer)) {
			throw new IllegalArgumentException("dereference needs pointer but got " + rValue.getCType());
		}
		final CPointer pointer = (CPointer) rValue.getCType().getUnderlyingType();
		final CType pointedType = pointer.pointsToType;
		if (pointedType.isIncomplete()) {
			throw new IncorrectSyntaxException(loc, "Pointer dereference of incomplete type");
		}

		return new ExpressionResult(rop.stmt, new HeapLValue(rValue.getValue(), pointedType), rop.decl, rop.auxVars,
				rop.overappr);
	}

	/**
	 * Handle unary arithmetic operators according to Section 6.5.3.3 of C11. Assumes that left (resp. right) are the
	 * results from handling the operands. Requires that the {@link LRValue} of operands is an {@link RValue} (i.e.,
	 * switchToRValueIfNecessary was applied if needed).
	 */
	ExpressionResult handleUnaryArithmeticOperators(Dispatcher main, ILocation loc, int op, ExpressionResult operand) {
		assert (operand.lrVal instanceof RValue) : "no RValue";
		final CType inputType = operand.lrVal.getCType().getUnderlyingType();

		switch (op) {
		case IASTUnaryExpression.op_not: {
			if (!inputType.isScalarType()) {
				throw new IllegalArgumentException("scalar type required");
			}
			final Expression negated;
			if (operand.lrVal.isBoogieBool()) {
				// in Boogie already represented by bool, we only negate
				negated = ExpressionFactory.newUnaryExpression(loc, UnaryExpression.Operator.LOGICNEG,
						operand.lrVal.getValue());
			} else {
				final Expression rhsOfComparison;
				if (inputType instanceof CPointer) {
					rhsOfComparison = mExpressionTranslation.constructNullPointer(loc);
				} else if (inputType instanceof CEnum) {
					final CPrimitive intType = new CPrimitive(PRIMITIVE.INT);
					rhsOfComparison = mExpressionTranslation.constructLiteralForIntegerType(loc, intType,
							BigInteger.ZERO);
				} else if (inputType instanceof CPrimitive) {
					final CPrimitive inputPrimitive = (CPrimitive) inputType;
					if (inputPrimitive.getGeneralType() == GENERALPRIMITIVE.INTTYPE) {
						rhsOfComparison = mExpressionTranslation.constructLiteralForIntegerType(loc, inputPrimitive,
								BigInteger.ZERO);
					} else if (inputPrimitive.getGeneralType() == GENERALPRIMITIVE.FLOATTYPE) {
						rhsOfComparison = mExpressionTranslation.constructLiteralForFloatingType(loc, inputPrimitive,
								BigInteger.ZERO);
					} else {
						throw new AssertionError("illegal case");
					}
				} else {
					throw new AssertionError("illegal case");
				}
				negated = mExpressionTranslation.constructBinaryEqualityExpression(loc, IASTBinaryExpression.op_equals,
						operand.lrVal.getValue(), inputType, rhsOfComparison, inputType);

			}
			final ExpressionResult result = ExpressionResult.copyStmtDeclAuxvarOverapprox(operand);
			// C11 6.5.3.3.5 The result has type int.
			final CPrimitive resultType = new CPrimitive(PRIMITIVE.INT);
			// type of Operator.COMPEQ expression is bool
			final boolean isBoogieBool = true;
			final RValue rval = new RValue(negated, resultType, isBoogieBool);
			result.lrVal = rval;
			return result;
		}
		case IASTUnaryExpression.op_plus: {
			if (!inputType.isArithmeticType()) {
				throw new UnsupportedOperationException("arithmetic type required");
			}
			if (inputType.isArithmeticType()) {
				operand.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
				mExpressionTranslation.doIntegerPromotion(loc, operand);
			}
			return operand;
		}
		case IASTUnaryExpression.op_minus:
		case IASTUnaryExpression.op_tilde:
			if (!inputType.isArithmeticType()) {
				throw new UnsupportedOperationException("arithmetic type required");
			}
			operand.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			mExpressionTranslation.doIntegerPromotion(loc, operand);
			final CPrimitive resultType = (CPrimitive) operand.lrVal.getCType();
			final ExpressionResult result = ExpressionResult.copyStmtDeclAuxvarOverapprox(operand);
			if (op == IASTUnaryExpression.op_minus && resultType.isIntegerType()) {
				addIntegerBoundsCheck(main, loc, result, resultType, op, operand.lrVal.getValue());
			}
			final Expression bwexpr = mExpressionTranslation.constructUnaryExpression(loc, op, operand.lrVal.getValue(),
					resultType);
			final RValue rval = new RValue(bwexpr, resultType, false);
			result.lrVal = rval;
			return result;
		default:
			throw new IllegalArgumentException("not a unary arithmetic operator " + op);
		}
	}

	@Override
	public Result visit(Dispatcher main, IASTBinaryExpression node) {
		final ArrayList<Declaration> decl = new ArrayList<Declaration>();
		final ArrayList<Statement> stmt = new ArrayList<Statement>();
		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>();
		final ILocation loc = LocationFactory.createCLocation(node);
		final List<Overapprox> overappr = new ArrayList<Overapprox>();

		final ExpressionResult l = (ExpressionResult) main.dispatch(node.getOperand1());
		final ExpressionResult r = (ExpressionResult) main.dispatch(node.getOperand2());

		final ExpressionResult rl = l.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
		final ExpressionResult rr = r.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);

		final CType lType = l.lrVal.getCType().getUnderlyingType();
		final CType rType = r.lrVal.getCType().getUnderlyingType();

		switch (node.getOperator()) {
		case IASTBinaryExpression.op_assign: {
			stmt.addAll(l.stmt);
			decl.addAll(l.decl);
			auxVars.putAll(l.auxVars);
			overappr.addAll(l.overappr);

			if (lType instanceof CPointer && rType instanceof CArray) {
				// array must be on heap --> just take the address

				stmt.addAll(r.stmt);
				decl.addAll(r.decl);
				auxVars.putAll(r.auxVars);
				overappr.addAll(r.overappr);

				RValue address = null;
				if (r.lrVal instanceof HeapLValue) {
					address = new RValue(((HeapLValue) r.lrVal).getAddress(),
							new CPointer(((CArray) rType).getValueType()));
				} else {
					address = new RValue(r.lrVal.getValue(), new CPointer(((CArray) rType).getValueType()));
				}
				return makeAssignment(loc, stmt, l.lrVal, address, decl, auxVars, overappr);
			} else {
				stmt.addAll(rr.stmt);
				decl.addAll(rr.decl);
				auxVars.putAll(rr.auxVars);
				overappr.addAll(rr.overappr);
				rr.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
				return makeAssignment(loc, stmt, l.lrVal, (RValue) rr.lrVal, decl, auxVars, overappr,
						l.unionFieldIdToCType);
			}
		}
		case IASTBinaryExpression.op_equals:
		case IASTBinaryExpression.op_notequals: {
			rr.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			rl.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			return handleEqualityOperators(main, loc, node.getOperator(), rl, rr);
		}
		case IASTBinaryExpression.op_greaterEqual:
		case IASTBinaryExpression.op_greaterThan:
		case IASTBinaryExpression.op_lessEqual:
		case IASTBinaryExpression.op_lessThan: {
			return handleRelationalOperators(main, loc, node.getOperator(), rl, rr);
		}

		case IASTBinaryExpression.op_logicalAnd: {
			rl.rexIntToBoolIfNecessary(loc, mExpressionTranslation, mMemoryHandler);
			rr.rexIntToBoolIfNecessary(loc, mExpressionTranslation, mMemoryHandler);

			stmt.addAll(rl.stmt);
			// NOTE: no rr.stmt
			decl.addAll(rl.decl);
			decl.addAll(rr.decl);
			auxVars.putAll(rl.auxVars);
			auxVars.putAll(rr.auxVars);
			overappr.addAll(rl.overappr);
			overappr.addAll(rr.overappr);

			if (rr.stmt.isEmpty()) {
				// no statements in right operands, hence no side effects in
				// operand
				// we can directly combine operands with LOGICAND
				final RValue newRVal = new RValue(
						ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND,
								rl.lrVal.getValue(), rr.lrVal.getValue()),
						new CPrimitive(CPrimitive.PRIMITIVE.INT), true);

				return new ExpressionResult(stmt, newRVal, decl, auxVars, overappr);
			}
			// create and add tmp var #t~AND~UID
			final CPrimitive intType = new CPrimitive(PRIMITIVE.INT);
			final String resName = mNameHandler.getTempVarUID(SFO.AUXVAR.SHORTCIRCUIT, intType);
			final VarList tempVar = new VarList(loc, new String[] { resName }, new PrimitiveType(loc, SFO.BOOL));
			final VariableDeclaration tmpVar = new VariableDeclaration(loc, new Attribute[0], new VarList[] { tempVar });
			auxVars.put(tmpVar, loc);
			decl.add(tmpVar);
			final VariableLHS lhs = new VariableLHS(loc, resName);
			final RValue tmpRval = new RValue(new IdentifierExpression(loc, resName), intType, true);
			final RValue resRval = tmpRval;
			// #t~AND~UID = left

			final AssignmentStatement aStat = new AssignmentStatement(loc, new LeftHandSide[] { lhs },
					new Expression[] { rl.lrVal.getValue() });
			Map<String, IAnnotations> annots = aStat.getPayload().getAnnotations();
			for (final Overapprox overapprItem : overappr) {
				annots.put(Overapprox.getIdentifier(), overapprItem);
			}
			stmt.add(aStat);
			// if (#t~AND~UID) {#t~AND~UID = right;}
			final ArrayList<Statement> outerThenPart = new ArrayList<Statement>();
			outerThenPart.addAll(rr.stmt);

			outerThenPart.add(
					new AssignmentStatement(loc, new LeftHandSide[] { lhs }, new Expression[] { rr.lrVal.getValue() }));
			final IfStatement ifStatement = new IfStatement(loc, tmpRval.getValue(), outerThenPart.toArray(new Statement[0]),
					new Statement[0]);
			annots = ifStatement.getPayload().getAnnotations();
			// for (Overapprox overapprItem : overappr) {
			// annots.put(Overapprox.getIdentifier(), overapprItem);
			// }
			stmt.add(ifStatement);
			return new ExpressionResult(stmt, resRval, decl, auxVars, overappr);
		}
		case IASTBinaryExpression.op_logicalOr: {
			rl.rexIntToBoolIfNecessary(loc, mExpressionTranslation, mMemoryHandler);
			rr.rexIntToBoolIfNecessary(loc, mExpressionTranslation, mMemoryHandler);

			stmt.addAll(rl.stmt);
			// NOTE: no rr.stmt
			decl.addAll(rl.decl);
			decl.addAll(rr.decl);
			auxVars.putAll(rl.auxVars);
			auxVars.putAll(rr.auxVars);
			overappr.addAll(rl.overappr);
			overappr.addAll(rr.overappr);

			if (rr.stmt.isEmpty()) {
				// no auxVar in operands, hence no side effects in operands
				// we can directly combine operands with LOGICOR
				return new ExpressionResult(stmt,
						new RValue(
								ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICOR,
										rl.lrVal.getValue(), rr.lrVal.getValue()),
								new CPrimitive(CPrimitive.PRIMITIVE.INT), true),
						decl, auxVars, overappr);
			}
			// create and add tmp var #t~OR~UID
			final CPrimitive intType = new CPrimitive(PRIMITIVE.INT);
			final String resName = mNameHandler.getTempVarUID(SFO.AUXVAR.SHORTCIRCUIT, intType);
			final VarList tempVar = new VarList(loc, new String[] { resName }, new PrimitiveType(loc, SFO.BOOL));
			final VariableDeclaration tmpVar = new VariableDeclaration(loc, new Attribute[0], new VarList[] { tempVar });
			auxVars.put(tmpVar, loc);
			decl.add(tmpVar);
			final VariableLHS lhs = new VariableLHS(loc, resName);
			final RValue tmpRval = new RValue(new IdentifierExpression(loc, resName), intType, true);
			final RValue resRval = tmpRval;
			// #t~OR~UID = left
			final AssignmentStatement aStat = new AssignmentStatement(loc, new LeftHandSide[] { lhs },
					new Expression[] { rl.lrVal.getValue() });
			Map<String, IAnnotations> annots = aStat.getPayload().getAnnotations();
			for (final Overapprox overapproxItem : overappr) {
				annots.put(Overapprox.getIdentifier(), overapproxItem);
			}
			stmt.add(aStat);
			// if (#t~OR~UID) {} else {#t~OR~UID = right;}
			final ArrayList<Statement> outerElsePart = new ArrayList<Statement>();
			outerElsePart.addAll(rr.stmt);

			outerElsePart.add(
					new AssignmentStatement(loc, new LeftHandSide[] { lhs }, new Expression[] { rr.lrVal.getValue() }));
			final IfStatement ifStatement = new IfStatement(loc, tmpRval.getValue(), new Statement[0],
					outerElsePart.toArray(new Statement[0]));
			annots = ifStatement.getPayload().getAnnotations();
			for (final Overapprox overapprItem : overappr) {
				annots.put(Overapprox.getIdentifier(), overapprItem);
			}
			stmt.add(ifStatement);
			return new ExpressionResult(stmt, resRval, decl, auxVars, overappr);
		}
		case IASTBinaryExpression.op_modulo:
		case IASTBinaryExpression.op_multiply:
		case IASTBinaryExpression.op_divide: {
			rl.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			rr.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			return handleMultiplicativeOperation(main, loc, null, node.getOperator(), rl, rr);
		}
		case IASTBinaryExpression.op_moduloAssign:
		case IASTBinaryExpression.op_multiplyAssign:
		case IASTBinaryExpression.op_divideAssign: {
			rl.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			rr.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			return handleMultiplicativeOperation(main, loc, l.lrVal, node.getOperator(), rl, rr);
		}
		case IASTBinaryExpression.op_plus:
		case IASTBinaryExpression.op_minus: {
			rl.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			rr.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			return handleAdditiveOperation(main, loc, null, node.getOperator(), rl, rr);
		}
		case IASTBinaryExpression.op_plusAssign:
		case IASTBinaryExpression.op_minusAssign: {
			rl.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			rr.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			return handleAdditiveOperation(main, loc, l.lrVal, node.getOperator(), rl, rr);
		}
		case IASTBinaryExpression.op_binaryAnd:
		case IASTBinaryExpression.op_binaryOr:
		case IASTBinaryExpression.op_binaryXor: {
			rl.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			rr.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			return handleBitwiseArithmeticOperation(main, loc, null, node.getOperator(), rl, rr);
		}
		case IASTBinaryExpression.op_binaryAndAssign:
		case IASTBinaryExpression.op_binaryOrAssign:
		case IASTBinaryExpression.op_binaryXorAssign: {
			rl.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			rr.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			return handleBitwiseArithmeticOperation(main, loc, l.lrVal, node.getOperator(), rl, rr);
		}
		case IASTBinaryExpression.op_shiftLeft:
		case IASTBinaryExpression.op_shiftRight: {
			rl.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			rr.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			return handleBitshiftOperation(main, loc, null, node.getOperator(), rl, rr);

		}
		case IASTBinaryExpression.op_shiftLeftAssign:
		case IASTBinaryExpression.op_shiftRightAssign: {
			rl.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			rr.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
			return handleBitshiftOperation(main, loc, l.lrVal, node.getOperator(), rl, rr);
		}

		default:
			final String msg = "Unknown or unsupported unary operation";
			throw new UnsupportedSyntaxException(loc, msg);
		}
	}

	/**
	 * Handle relational operators according to Section 6.5.8 of C11. Assumes that left (resp. right) are the results
	 * from handling the operands. Requires that the {@link LRValue} of operands is an {@link RValue} (i.e.,
	 * switchToRValueIfNecessary was applied if needed).
	 */
	ExpressionResult handleRelationalOperators(Dispatcher main, ILocation loc, int op, ExpressionResult left,
			ExpressionResult right) {
		assert (left.lrVal instanceof RValue) : "no RValue";
		assert (right.lrVal instanceof RValue) : "no RValue";
		left.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
		right.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
		final CType lType = left.lrVal.getCType().getUnderlyingType();
		final CType rType = right.lrVal.getCType().getUnderlyingType();

		final ExpressionResult result = ExpressionResult.copyStmtDeclAuxvarOverapprox(left, right);
		final Expression expr;
		if (lType instanceof CPrimitive && rType instanceof CPrimitive) {
			assert lType.isRealType() && rType.isRealType() : "no real type";
			mExpressionTranslation.usualArithmeticConversions(loc, left, right);
			expr = mExpressionTranslation.constructBinaryComparisonExpression(loc, op, left.lrVal.getValue(),
					(CPrimitive) left.lrVal.getCType(), right.lrVal.getValue(), (CPrimitive) right.lrVal.getCType());
		} else if (lType instanceof CPointer && rType instanceof CPointer) {
			final Expression baseEquality = constructPointerComponentRelation(loc, IASTBinaryExpression.op_equals,
					left.lrVal.getValue(), right.lrVal.getValue(), SFO.POINTER_BASE);
			final Expression offsetRelation = constructPointerComponentRelation(loc, op, left.lrVal.getValue(),
					right.lrVal.getValue(), SFO.POINTER_OFFSET);
			switch (mMemoryHandler.getPointerSubtractionAndComparisonValidityCheckMode()) {
			case ASSERTandASSUME:
				final Statement assertStm = new AssertStatement(loc, baseEquality);
				final Check chk = new Check(Spec.ILLEGAL_POINTER_ARITHMETIC);
				chk.addToNodeAnnot(assertStm);
				result.stmt.add(assertStm);
				expr = offsetRelation;
				break;
			case ASSUME:
				final Statement assumeStm = new AssumeStatement(loc, baseEquality);
				result.stmt.add(assumeStm);
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
			throw new UnsupportedOperationException("unsupported " + rType + ", " + lType);
		}
		// The result has type int (C11 6.5.8.6)
		final CPrimitive typeOfResult = new CPrimitive(PRIMITIVE.INT);
		final RValue rval = new RValue(expr, typeOfResult, true, false);
		result.lrVal = rval;
		return result;
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
	private Expression constructPointerComponentRelation(ILocation loc, int op, Expression leftPointer,
			Expression rightPointer, String component) {
		assert component.equals(SFO.POINTER_BASE) || component.equals(SFO.POINTER_OFFSET) : "unknown pointer component";
		final StructAccessExpression leftComponent = new StructAccessExpression(loc, leftPointer, component);
		final StructAccessExpression rightComponent = new StructAccessExpression(loc, rightPointer, component);
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
	 * Handle multiplicative operators according to Sections 6.5.5 of C11. Assumes that left (resp. right) are the
	 * results from handling the operands. Requires that the {@link LRValue} of operands is an {@link RValue} (i.e.,
	 * switchToRValueIfNecessary was applied if needed). requires that the Boogie expressions in left (resp. right) are
	 * a non-boolean representation of these results (i.e., rexBoolToIntIfNecessary() has already been applied if
	 * needed).
	 * 
	 * @param lhs
	 *            is non-null iff we haven an assignment
	 */
	ExpressionResult handleMultiplicativeOperation(Dispatcher main, ILocation loc, LRValue lhs, int op,
			ExpressionResult left, ExpressionResult right) {
		assert (left.lrVal instanceof RValue) : "no RValue";
		assert (right.lrVal instanceof RValue) : "no RValue";
		final CType lType = left.lrVal.getCType().getUnderlyingType();
		final CType rType = right.lrVal.getCType().getUnderlyingType();
		if (!rType.isArithmeticType() || !lType.isArithmeticType()) {
			throw new UnsupportedOperationException("operands have to have integer types");
		}
		if (op == IASTBinaryExpression.op_divide || op == IASTBinaryExpression.op_modulo) {
			addDivisionByZeroCheck(main, loc, right);
		}
		mExpressionTranslation.usualArithmeticConversions(loc, left, right);
		final CPrimitive typeOfResult = (CPrimitive) left.lrVal.getCType();
		assert typeOfResult.equals(right.lrVal.getCType());

		ExpressionResult result = ExpressionResult.copyStmtDeclAuxvarOverapprox(left, right);
		switch (op) {
		case IASTBinaryExpression.op_multiply:
		case IASTBinaryExpression.op_divide:
		case IASTBinaryExpression.op_multiplyAssign:
		case IASTBinaryExpression.op_divideAssign: {
			addIntegerBoundsCheck(main, loc, result, typeOfResult, op, left.lrVal.getValue(), right.lrVal.getValue());
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

		final Expression expr = mExpressionTranslation.constructArithmeticExpression(loc, op, left.lrVal.getValue(),
				typeOfResult, right.lrVal.getValue(), typeOfResult);
		final RValue rval = new RValue(expr, typeOfResult, false, false);

		switch (op) {
		case IASTBinaryExpression.op_multiply:
		case IASTBinaryExpression.op_divide:
		case IASTBinaryExpression.op_modulo: {
			assert lhs == null : "no assignment";
			result.lrVal = rval;
			return result;
		}
		case IASTBinaryExpression.op_multiplyAssign:
		case IASTBinaryExpression.op_divideAssign:
		case IASTBinaryExpression.op_moduloAssign: {
			result = makeAssignment(loc, result.stmt, lhs, rval, result.decl, result.auxVars, result.overappr);
			return result;
		}
		default:
			throw new AssertionError("no multiplicative " + op);
		}
	}

	/**
	 * Add to divisorExpRes a check if divisior is zero.
	 */
	private void addDivisionByZeroCheck(Dispatcher main, ILocation loc, ExpressionResult divisorExpRes) {
		final Expression divisor = divisorExpRes.lrVal.getValue();
		final CPrimitive divisorType = (CPrimitive) divisorExpRes.lrVal.getCType();
		if (main.getTranslationSettings().getDivisionByZero() == POINTER_CHECKMODE.IGNORE) {
			return;
		} else if (divisorType.isRealFloatingType()) {
			// division by zero is defined for real floating types
			return;
		} else {
			final Expression zero;
			if (divisorType.isIntegerType()) {
				zero = mExpressionTranslation.constructLiteralForIntegerType(loc, divisorType, BigInteger.ZERO);
			} else if (divisorType.isRealFloatingType()) {
				throw new AssertionError("case should have been handled before");
			} else {
				throw new UnsupportedOperationException("unsupported " + divisorType);
			}
			final Expression divisorNotZero = mExpressionTranslation.constructBinaryEqualityExpression(loc,
					IASTBinaryExpression.op_notequals, divisor, divisorType, zero, divisorType);
			final Statement additionalStatement;
			if (main.getTranslationSettings().getDivisionByZero() == POINTER_CHECKMODE.ASSUME) {
				additionalStatement = new AssumeStatement(loc, divisorNotZero);
			} else if (main.getTranslationSettings().getDivisionByZero() == POINTER_CHECKMODE.ASSERTandASSUME) {
				additionalStatement = new AssertStatement(loc, divisorNotZero);
				final Check check = new Check(Check.Spec.DIVISION_BY_ZERO);
				check.addToNodeAnnot(additionalStatement);
			} else {
				throw new AssertionError("illegal");
			}
			divisorExpRes.stmt.add(additionalStatement);
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
	ExpressionResult handleAdditiveOperation(Dispatcher main, ILocation loc, LRValue lhs, int op, ExpressionResult left,
			ExpressionResult right) {
		assert (left.lrVal instanceof RValue) : "no RValue";
		assert (right.lrVal instanceof RValue) : "no RValue";
		final CType lType = left.lrVal.getCType().getUnderlyingType();
		final CType rType = right.lrVal.getCType().getUnderlyingType();
		ExpressionResult result;
		final Expression expr;
		final CType typeOfResult;
		if (lType.isArithmeticType() && rType.isArithmeticType()) {
			mExpressionTranslation.usualArithmeticConversions(loc, left, right);
			typeOfResult = left.lrVal.getCType();
			assert typeOfResult.equals(right.lrVal.getCType());
			result = ExpressionResult.copyStmtDeclAuxvarOverapprox(left, right);
			addIntegerBoundsCheck(main, loc, result, (CPrimitive) typeOfResult, op, left.lrVal.getValue(),
					right.lrVal.getValue());
			expr = mExpressionTranslation.constructArithmeticExpression(loc, op, left.lrVal.getValue(),
					(CPrimitive) typeOfResult, right.lrVal.getValue(), (CPrimitive) typeOfResult);
		} else if ((lType instanceof CPointer) && rType.isArithmeticType()) {
			typeOfResult = left.lrVal.getCType();
			final CType pointsToType = ((CPointer) typeOfResult).pointsToType;
			result = ExpressionResult.copyStmtDeclAuxvarOverapprox(left, right);
			final ExpressionResult re = doPointerArithmeticWithConversion(main, op, loc, left.lrVal.getValue(),
					(RValue) right.lrVal, pointsToType);
			result.addAll(re);
			expr = re.lrVal.getValue();
			addOffsetInBoundsCheck(main, loc, expr, result);
		} else if (lType.isArithmeticType() && (rType instanceof CPointer)) {
			if (op != IASTBinaryExpression.op_plus && op != IASTBinaryExpression.op_plusAssign) {
				throw new AssertionError("lType arithmetic, rType CPointer only legal if op is plus");
			}
			typeOfResult = right.lrVal.getCType();
			final CType pointsToType = ((CPointer) typeOfResult).pointsToType;
			result = ExpressionResult.copyStmtDeclAuxvarOverapprox(left, right);
			final ExpressionResult re = doPointerArithmeticWithConversion(main, op, loc, right.lrVal.getValue(),
					(RValue) left.lrVal, pointsToType);
			result.addAll(re);
			expr = re.lrVal.getValue();
			addOffsetInBoundsCheck(main, loc, expr, result);
		} else if ((lType instanceof CPointer) && (rType instanceof CPointer)) {
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
			result = ExpressionResult.copyStmtDeclAuxvarOverapprox(left, right);
			CType pointsToType;
			{
				final CType leftPointsToType = ((CPointer) lType).pointsToType;
				final CType rightPointsToType = ((CPointer) rType).pointsToType;
				if (!leftPointsToType.equals(rightPointsToType)) {
					// TODO: Matthias 2015-09-08: Maybe this is too strict and we
					// have to check leftPointsToType.isCompatibleWith(rightPointsToType)
					throw new UnsupportedOperationException(
							"incompatible pointers: pointsto " + leftPointsToType + " " + rightPointsToType);
				}
				pointsToType = leftPointsToType;
			}
			addBaseEqualityCheck(main, loc, left.lrVal.getValue(), right.lrVal.getValue(), result);
			expr = doPointerSubtraction(main, loc, left.lrVal.getValue(), right.lrVal.getValue(), pointsToType);
		} else {
			throw new UnsupportedOperationException("non-standard case of pointer arithmetic");
		}
		final RValue rval = new RValue(expr, typeOfResult, false, false);

		switch (op) {
		case IASTBinaryExpression.op_plus:
		case IASTBinaryExpression.op_minus: {
			assert lhs == null : "no assignment";
			result.lrVal = rval;
			return result;
		}
		case IASTBinaryExpression.op_plusAssign:
		case IASTBinaryExpression.op_minusAssign: {
			result = makeAssignment(loc, result.stmt, lhs, rval, result.decl, result.auxVars, result.overappr);
			return result;
		}
		default:
			throw new AssertionError("no additive operation " + op);
		}
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
	 * @param result
	 *            {@link ExpressionResult} to which the additional statements are added.
	 */
	private void addBaseEqualityCheck(Dispatcher main, ILocation loc, Expression leftPtr, Expression rightPtr,
			ExpressionResult result) {
		if (mMemoryHandler.getPointerSubtractionAndComparisonValidityCheckMode() == POINTER_CHECKMODE.IGNORE) {
			// do not check anything
			return;
		}
		final Expression baseEquality = constructPointerComponentRelation(loc, IASTBinaryExpression.op_equals, leftPtr,
				rightPtr, SFO.POINTER_BASE);
		switch (mMemoryHandler.getPointerSubtractionAndComparisonValidityCheckMode()) {
		case ASSERTandASSUME:
			final Statement assertStm = new AssertStatement(loc, baseEquality);
			final Check chk = new Check(Spec.ILLEGAL_POINTER_ARITHMETIC);
			chk.addToNodeAnnot(assertStm);
			result.stmt.add(assertStm);
			break;
		case ASSUME:
			final Statement assumeStm = new AssumeStatement(loc, baseEquality);
			result.stmt.add(assumeStm);
			break;
		case IGNORE:
			throw new AssertionError("case handled before");
		default:
			throw new AssertionError("unknown value");
		}
	}

	/**
	 * Subtract two pointers.
	 * 
	 * @param leftPtr
	 *            Boogie {@link Expression} that represents the left pointer.
	 * @param rightPtr
	 *            Boogie {@link Expression} that represents the right pointer.
	 * @param pointsToType
	 *            {@link CType} of the objects to which the pointers point.
	 * @return An {@link Expression} that represents the difference of two Pointers according to C11 6.5.6.9.
	 */
	private Expression doPointerSubtraction(Dispatcher main, ILocation loc, Expression ptr1, Expression ptr2,
			CType pointsToType) {
		final Expression ptr1Offset = new StructAccessExpression(loc, ptr1, SFO.POINTER_OFFSET);
		final Expression ptr2Offset = new StructAccessExpression(loc, ptr2, SFO.POINTER_OFFSET);
		final Expression offsetDifference = mExpressionTranslation.constructArithmeticExpression(loc,
				IASTBinaryExpression.op_minus, ptr1Offset, mExpressionTranslation.getCTypeOfPointerComponents(),
				ptr2Offset, mExpressionTranslation.getCTypeOfPointerComponents());
		final Expression typesize = mMemoryHandler.calculateSizeOf(loc, pointsToType);
		final CPrimitive typesizeType = new CPrimitive(PRIMITIVE.INT);
		// TODO: typesizeType and .getCTypeOfPointerComponents() might be
		// different then one expression has to be converted into the type of
		// the other
		final Expression offsetDifferenceDividedByTypesize = mExpressionTranslation.constructArithmeticExpression(loc,
				IASTBinaryExpression.op_divide, offsetDifference, mExpressionTranslation.getCTypeOfPointerComponents(),
				typesize, typesizeType);
		return offsetDifferenceDividedByTypesize;
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
	 * @param result
	 *            {@link ExpressionResult} to which the additional statements are added.
	 */
	private void addOffsetInBoundsCheck(Dispatcher main, ILocation loc, Expression ptr, ExpressionResult result) {
		// TODO: Matthias 2015-09-08 implement this
		// maybe additional parameters are required.
	}

	/**
	 * Handle equality operators according to Section 6.5.9 of C11. Assumes that left (resp. right) are the results from
	 * handling the operands. Requires that the {@link LRValue} of operands is an {@link RValue} (i.e.,
	 * switchToRValueIfNecessary was applied if needed). requires that the Boogie expressions in left (resp. right) are
	 * a non-boolean representation of these results (i.e., rexBoolToIntIfNecessary() has already been applied if
	 * needed).
	 */
	ExpressionResult handleEqualityOperators(Dispatcher main, ILocation loc, int op, ExpressionResult left,
			ExpressionResult right) {
		assert (left.lrVal instanceof RValue) : "no RValue";
		assert (right.lrVal instanceof RValue) : "no RValue";
		{
			final CType lType = left.lrVal.getCType().getUnderlyingType();
			final CType rType = right.lrVal.getCType().getUnderlyingType();
			// FIXME Matthias 2015-09-05: operation only legal if both have type
			// CPointer I guess the following implicit casts are a workaround
			// for arrays (or structs or union?)
			if (lType instanceof CPointer || rType instanceof CPointer) {
				if (!(lType instanceof CPointer)) {
					// throw new AssertionError("illegal case");
					// FIXME: the following is a workaround for the null pointer
					convert(loc, left, new CPointer(new CPrimitive(PRIMITIVE.VOID)));
				}
				if (!(rType instanceof CPointer)) {
					// throw new AssertionError("illegal case");
					// FIXME: the following is a workaround for the null pointer
					convert(loc, right, new CPointer(new CPrimitive(PRIMITIVE.VOID)));
				}
			} else if (lType.isArithmeticType() && rType.isArithmeticType()) {
				mExpressionTranslation.usualArithmeticConversions(loc, left, right);
			} else {
				throw new UnsupportedOperationException("unsupported " + rType + ", " + lType);
			}
		}
		// The result has type int (C11 6.5.9.1)
		final CPrimitive typeOfResult = new CPrimitive(PRIMITIVE.INT);
		final Expression expr = mExpressionTranslation.constructBinaryEqualityExpression(loc, op, left.lrVal.getValue(),
				left.lrVal.getCType(), right.lrVal.getValue(), right.lrVal.getCType());
		final RValue rval = new RValue(expr, typeOfResult, true, false);
		final ExpressionResult result = ExpressionResult.copyStmtDeclAuxvarOverapprox(left, right);
		result.lrVal = rval;
		return result;
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
	ExpressionResult handleBitshiftOperation(Dispatcher main, ILocation loc, LRValue lhs, int op, ExpressionResult left,
			ExpressionResult right) {
		assert (left.lrVal instanceof RValue) : "no RValue";
		assert (right.lrVal instanceof RValue) : "no RValue";
		final CType lType = left.lrVal.getCType().getUnderlyingType();
		final CType rType = right.lrVal.getCType().getUnderlyingType();
		if (!rType.isIntegerType() || !lType.isIntegerType()) {
			throw new UnsupportedOperationException("operands have to have integer types");
		}
		mExpressionTranslation.doIntegerPromotion(loc, left);
		final CPrimitive typeOfResult = (CPrimitive) left.lrVal.getCType();
		convert(loc, right, typeOfResult);
		final Expression expr = mExpressionTranslation.constructBinaryBitwiseExpression(loc, op, left.lrVal.getValue(),
				typeOfResult, right.lrVal.getValue(), typeOfResult);
		final RValue rval = new RValue(expr, typeOfResult, false, false);
		switch (op) {
		case IASTBinaryExpression.op_shiftLeft:
		case IASTBinaryExpression.op_shiftRight: {
			assert lhs == null : "no assignment";
			final ExpressionResult result = ExpressionResult.copyStmtDeclAuxvarOverapprox(left, right);
			result.lrVal = rval;
			return result;
		}
		case IASTBinaryExpression.op_shiftLeftAssign:
		case IASTBinaryExpression.op_shiftRightAssign: {
			final ExpressionResult copy = ExpressionResult.copyStmtDeclAuxvarOverapprox(left, right);
			final ExpressionResult result = makeAssignment(loc, copy.stmt, lhs, rval, copy.decl, copy.auxVars,
					copy.overappr);
			return result;
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
	ExpressionResult handleBitwiseArithmeticOperation(Dispatcher main, ILocation loc, LRValue lhs, int op,
			ExpressionResult left, ExpressionResult right) {
		assert (left.lrVal instanceof RValue) : "no RValue";
		assert (right.lrVal instanceof RValue) : "no RValue";
		final CType lType = left.lrVal.getCType().getUnderlyingType();
		final CType rType = right.lrVal.getCType().getUnderlyingType();
		if (!rType.isIntegerType() || !lType.isIntegerType()) {
			throw new UnsupportedOperationException("operands have to have integer types");
		}
		mExpressionTranslation.usualArithmeticConversions(loc, left, right);
		final CPrimitive typeOfResult = (CPrimitive) left.lrVal.getCType();
		assert typeOfResult.equals(left.lrVal.getCType());
		final Expression expr = mExpressionTranslation.constructBinaryBitwiseExpression(loc, op, left.lrVal.getValue(),
				typeOfResult, right.lrVal.getValue(), typeOfResult);
		final RValue rval = new RValue(expr, typeOfResult, false, false);
		switch (op) {
		case IASTBinaryExpression.op_binaryAnd:
		case IASTBinaryExpression.op_binaryXor:
		case IASTBinaryExpression.op_binaryOr: {
			assert lhs == null : "no assignment";
			final ExpressionResult result = ExpressionResult.copyStmtDeclAuxvarOverapprox(left, right);
			result.lrVal = rval;
			return result;
		}
		case IASTBinaryExpression.op_binaryAndAssign:
		case IASTBinaryExpression.op_binaryXorAssign:
		case IASTBinaryExpression.op_binaryOrAssign: {
			final ExpressionResult copy = ExpressionResult.copyStmtDeclAuxvarOverapprox(left, right);
			final ExpressionResult result = makeAssignment(loc, copy.stmt, lhs, rval, copy.decl, copy.auxVars,
					copy.overappr);
			return result;
		}
		default:
			throw new AssertionError("no bitwise arithmetic operation " + op);
		}
	}

	/**
	 * Add checks for integer overflows. Construct arithmetic operation and add an assert statement that checks if the
	 * result is in the range of the corresponding C data type (i.e. check for overflow wrt. max and min value). Note
	 * that we do not check if a given expression is in the range. We explicitly construct a new expression for the
	 * arithmetic operation in this check because we possibly have to adjust the data type used in boogie. E.g., if we
	 * use 32bit bitvectors in Boogie we are unable to express an overflow check for a 32bit integer addition in C.
	 * Instead, we have to use a 33bit bit bitvector in Boogie.
	 */
	private void addIntegerBoundsCheck(Dispatcher main, ILocation loc, ExpressionResult rex, CPrimitive resultType,
			int operation, Expression... operands) {
		if (main.getPreferences().getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_SIGNED_INTEGER_BOUNDS)
				&& resultType.isIntegerType() && !resultType.isUnsigned()) {
			final Check check = new Check(Spec.INTEGER_OVERFLOW);
			final Expression operationResult;
			if (operands.length == 1) {
				operationResult = mExpressionTranslation.constructUnaryExpression(loc, operation, operands[0],
						resultType);
			} else if (operands.length == 2) {
				operationResult = mExpressionTranslation.constructArithmeticExpression(loc, operation, operands[0],
						resultType, operands[1], resultType);
			} else {
				throw new AssertionError("no such operation");
			}
			final AssertStatement smallerMaxInt = new AssertStatement(loc, ExpressionFactory.newBinaryExpression(loc,
					BinaryExpression.Operator.COMPLT, operationResult,
					new IntegerLiteral(loc, main.getTypeSizes().getMaxValueOfPrimitiveType(resultType).toString())));
			check.addToNodeAnnot(smallerMaxInt);
			final AssertStatement biggerMinInt = new AssertStatement(loc, ExpressionFactory.newBinaryExpression(loc,
					BinaryExpression.Operator.COMPGEQ, operationResult,
					new IntegerLiteral(loc, main.getTypeSizes().getMinValueOfPrimitiveType(resultType).toString())));
			check.addToNodeAnnot(biggerMinInt);
			rex.stmt.add(smallerMaxInt);
			rex.stmt.add(biggerMinInt);
		}
	}

	@Override
	public Result visit(Dispatcher main, IASTEqualsInitializer node) {
		return main.dispatch(node.getInitializerClause());
	}

	@Override
	public Result visit(Dispatcher main, IASTDeclarationStatement node) {
		return main.dispatch(node.getDeclaration());
	}

	@Override
	public Result visit(Dispatcher main, IASTReturnStatement node) {
		return mFunctionHandler.handleReturnStatement(main, mMemoryHandler, mStructHandler, node);
	}

	@Override
	public Result visit(Dispatcher main, IASTExpressionStatement node) {
		final Result r = main.dispatch(node.getExpression());
		if (r instanceof ExpressionResult) {
			final ExpressionResult rExp = (ExpressionResult) r;
			// if (!rExp.stmt.isEmpty()) {
			final ArrayList<Statement> stmt = new ArrayList<Statement>(rExp.stmt);
			final ArrayList<Declaration> decl = new ArrayList<Declaration>(rExp.decl);
			final List<Overapprox> overappr = new ArrayList<Overapprox>();
			// assert (isAuxVarMapcomplete(main, rExp.decl, rExp.auxVars));
			stmt.addAll(createHavocsForAuxVars(rExp.auxVars));
			overappr.addAll(rExp.overappr);
			final Map<VariableDeclaration, ILocation> emptyAuxVars = new LinkedHashMap<VariableDeclaration, ILocation>(0);
			return new ExpressionResult(stmt, rExp.lrVal, decl, emptyAuxVars, overappr);
			// } else {
			// String msg = "This statement has no effect and will be dropped: " + node.getRawSignature();
			// main.warn(LocationFactory.createCLocation(node), msg);
			// return new SkipResult();
			// }
		} else if (r instanceof ExpressionListResult) {
			final ArrayList<Statement> stmt = new ArrayList<Statement>();
			final ArrayList<Declaration> decl = new ArrayList<Declaration>();
			final List<Overapprox> overappr = new ArrayList<Overapprox>();
			final Map<VariableDeclaration, ILocation> emptyAuxVars = new LinkedHashMap<VariableDeclaration, ILocation>(0);
			for (final ExpressionResult res : ((ExpressionListResult) r).list) {
				if (!res.stmt.isEmpty()) {
					stmt.addAll(res.stmt);
					decl.addAll(res.decl);
					// assert (isAuxVarMapcomplete(main, res.decl, res.auxVars));
					stmt.addAll(createHavocsForAuxVars(res.auxVars));
					overappr.addAll(res.overappr);
				}
			}

			return new ExpressionResult(stmt, null, decl, emptyAuxVars, overappr);
		} else if (r instanceof SkipResult) {
			return r;
		}
		final String msg = "We always convert to AssignmentStatement, other options raise this error!";
		final ILocation loc = LocationFactory.createCLocation(node);
		throw new UnsupportedSyntaxException(loc, msg);
	}

	@Override
	public Result visit(Dispatcher main, IASTIfStatement node) {
		final ILocation loc = LocationFactory.createCLocation(node);
		final ArrayList<Declaration> decl = new ArrayList<Declaration>();
		final ArrayList<Statement> stmt = new ArrayList<Statement>();
		final List<Overapprox> overappr = new ArrayList<Overapprox>();
		final Map<VariableDeclaration, ILocation> emptyAuxVars = new LinkedHashMap<VariableDeclaration, ILocation>();

		ExpressionResult condResult = (ExpressionResult) main.dispatch(node.getConditionExpression());
		condResult = condResult.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
		condResult.rexIntToBoolIfNecessary(loc, mExpressionTranslation, mMemoryHandler);
		final RValue cond = (RValue) condResult.lrVal;
		decl.addAll(condResult.decl);
		stmt.addAll(condResult.stmt);
		overappr.addAll(condResult.overappr);
		final List<HavocStatement> havocs = createHavocsForAuxVars(condResult.auxVars);

		final Result thenResult = main.dispatch(node.getThenClause());
		final List<Statement> thenStmt = new ArrayList<Statement>();
		thenStmt.addAll(havocs);
		if (thenResult instanceof ExpressionResult) {
			final ExpressionResult re = (ExpressionResult) thenResult;
			decl.addAll(re.decl);
			thenStmt.addAll(re.stmt);
		} else if (thenResult instanceof Result) {
			if (thenResult.node instanceof Body) {
				final Body thenPart = (Body) (thenResult.node);
				thenStmt.addAll(Arrays.asList(thenPart.getBlock()));
				decl.addAll(Arrays.asList(thenPart.getLocalVars()));
			} else if (thenResult instanceof SkipResult) {
				// add no statements or declarations
			} else {
				final String msg = "Error: unexpected dispatch result";
				throw new IncorrectSyntaxException(loc, msg);
			}
		}

		final List<Statement> elseStmt = new ArrayList<Statement>();
		elseStmt.addAll(havocs);
		if (node.getElseClause() != null) {
			final Result elseResult = main.dispatch(node.getElseClause());
			if (elseResult instanceof ExpressionResult) {
				final ExpressionResult re = (ExpressionResult) elseResult;
				decl.addAll(re.decl);
				elseStmt.addAll(re.stmt);
			} else if (elseResult instanceof Result) {
				if (elseResult.node instanceof Body) {
					final Body elsePart = (Body) (elseResult.node);
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
		final IfStatement ifStmt = new IfStatement(loc, cond.getValue(), thenStmt.toArray(new Statement[0]),
				elseStmt.toArray(new Statement[0]));
		final Map<String, IAnnotations> annots = ifStmt.getPayload().getAnnotations();
		for (final Overapprox overapprItem : overappr) {
			annots.put(Overapprox.getIdentifier(), overapprItem);
		}
		stmt.add(ifStmt);
		return new ExpressionResult(stmt, null, decl, emptyAuxVars, overappr);
	}

	@Override
	public Result visit(Dispatcher main, IASTWhileStatement node) {
		final ExpressionResult condResult = (ExpressionResult) main.dispatch(node.getCondition());
		final String loopLabel = mNameHandler.getGloballyUniqueIdentifier(SFO.LOOPLABEL);
		mInnerMostLoopLabel.push(loopLabel);
		final Result bodyResult = main.dispatch(node.getBody());
		mInnerMostLoopLabel.pop();
		return handleLoops(main, node, bodyResult, condResult, loopLabel);
	}

	@Override
	public Result visit(Dispatcher main, IASTForStatement node) {
		final String loopLabel = mNameHandler.getGloballyUniqueIdentifier(SFO.LOOPLABEL);
		return handleLoops(main, node, null, null, loopLabel);
	}

	@Override
	public Result visit(Dispatcher main, IASTDoStatement node) {
		final ExpressionResult condResult = (ExpressionResult) main.dispatch(node.getCondition());
		final String loopLabel = mNameHandler.getGloballyUniqueIdentifier(SFO.LOOPLABEL);
		mInnerMostLoopLabel.push(loopLabel);
		final Result bodyResult = main.dispatch(node.getBody());
		mInnerMostLoopLabel.pop();
		return handleLoops(main, node, bodyResult, condResult, loopLabel);
	}

	@Override
	public Result visit(Dispatcher main, IASTContinueStatement cs) {
		final ILocation loc = LocationFactory.createCLocation(cs);
		final ArrayList<Statement> stmt = new ArrayList<Statement>();
		stmt.add(new GotoStatement(loc, new String[] { mInnerMostLoopLabel.peek() }));
		final ExpressionResult contResult = new ExpressionResult(stmt, null);
		return contResult;
	}

	@Override
	public Result visit(Dispatcher main, IASTExpressionList node) {
		final ExpressionListResult result = new ExpressionListResult();
		for (final IASTExpression expr : node.getExpressions()) {
			final Result r = main.dispatch(expr);
			assert r instanceof ExpressionResult;
			result.list.add((ExpressionResult) r);
		}
		return result;
	}

	@Override
	public Result visit(Dispatcher main, IASTInitializerList node) {
		final ILocation loc = LocationFactory.createCLocation(node);
		if (node.getClauses().length != node.getSize()) {
			throw new IllegalArgumentException("You might have parsed your code with "
					+ "ITranslationUnit.AST_SKIP_TRIVIAL_EXPRESSIONS_IN_AGGREGATE_INITIALIZERS!");
		}
		final ExpressionListRecResult result = new ExpressionListRecResult();
		for (final IASTInitializerClause i : node.getClauses()) {
			final Result r = main.dispatch(i);
			if (r instanceof ExpressionListRecResult) {
				result.list.add((ExpressionListRecResult) r);
			} else if (r instanceof ExpressionResult) {
				ExpressionResult rex = (ExpressionResult) r;
				rex = rex.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
				result.list.add(new ExpressionListRecResult(rex.stmt, rex.lrVal, rex.decl, rex.auxVars, rex.overappr));
				// result.auxVars.putAll(((ResultExpression) r).auxVars);//what for??
			} else {
				final String msg = "Unexpected result";
				throw new UnsupportedSyntaxException(loc, msg);
			}
		}
		return result;
	}

	@Override
	public Result visit(Dispatcher main, CASTDesignatedInitializer node) {
		return mStructHandler.handleDesignatedInitializer(main, mMemoryHandler, mStructHandler, node);
	}

	@Override
	public Result visit(Dispatcher main, IASTFunctionCallExpression node) {
		final Check check = new Check(Check.Spec.PRE_CONDITION);
		final ILocation loc = LocationFactory.createCLocation(node, check);
		final IASTExpression functionName = node.getFunctionNameExpression();
		if (functionName instanceof IASTIdExpression) {
			final Result standardFunction = mFunctionHandler.handleStandardFunctions(main, mMemoryHandler, mStructHandler,
					loc, ((IASTIdExpression) functionName).getName().toString(), node.getArguments());
			if (standardFunction != null) {
				return standardFunction;
			}
		}
		return mFunctionHandler.handleFunctionCallExpression(main, mMemoryHandler, mStructHandler, loc, functionName,
				node.getArguments());
	}

	@Override
	public Result visit(Dispatcher main, IASTBreakStatement node) {
		final ArrayList<Statement> stmt = new ArrayList<Statement>();
		stmt.add(new BreakStatement(LocationFactory.createCLocation(node)));
		return new ExpressionResult(stmt, null);
	}

	@Override
	public Result visit(Dispatcher main, IASTNullStatement node) {
		return new SkipResult();
	}

	/**
	 * Translate a switch statement as described in C99: 6.8.4.2
	 */
	@Override
	public Result visit(Dispatcher main, IASTSwitchStatement node) {
		final ILocation loc = LocationFactory.createCLocation(node);
		ArrayList<Statement> stmt = new ArrayList<Statement>();
		final ArrayList<Declaration> decl = new ArrayList<Declaration>();
		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>();
		final List<Overapprox> overappr = new ArrayList<Overapprox>();

		// dispatch the controlling expression, convert it to int
		final Result switchParam = main.dispatch(node.getControllerExpression());
		assert switchParam instanceof ExpressionResult;
		final ExpressionResult l = ((ExpressionResult) switchParam).switchToRValueIfNecessary(main, mMemoryHandler,
				mStructHandler, loc);
		// 6.8.4.2-1: "The controlling expression of a switch statement shall have integer type."
		// note that this does not mean that it has "int" type, it may be long or char, for instance
		assert l.lrVal.getCType().isIntegerType();
		// 6.8.4.2-5: "The integer promotions are performed on the controlling expression."
		mExpressionTranslation.doIntegerPromotion(loc, l);

		stmt.addAll(l.stmt);
		decl.addAll(l.decl);
		auxVars.putAll(l.auxVars);
		overappr.addAll(l.overappr);
		final Expression switchArg = l.lrVal.getValue();

		final CPrimitive intType = new CPrimitive(PRIMITIVE.INT);
		final String breakLabelName = mNameHandler.getGloballyUniqueIdentifier("SWITCH~BREAK~");
		final String switchFlag = mNameHandler.getTempVarUID(SFO.AUXVAR.SWITCH, intType);
		final ASTType flagType = new PrimitiveType(loc, SFO.BOOL);

		final VariableDeclaration switchAuxVarDec = SFO.getTempVarVariableDeclaration(switchFlag, flagType, loc);
		decl.add(switchAuxVarDec);
		auxVars.put(switchAuxVarDec, loc);

		boolean isFirst = true;
		boolean firstCond = true;
		Expression cond = null;
		ILocation locC = null;

		ArrayList<Statement> ifBlock = new ArrayList<Statement>();
		beginScope();
		for (final IASTNode child : node.getBody().getChildren()) {
			if (isFirst && !(child instanceof IASTCaseStatement || child instanceof IASTDefaultStatement)) {
				// declarations in the beginning of a switch body (i.e. before the first case/default) are used,
				// statements are dropped
				// see example 6.8.4.2-7

				// we need to dispatch the child in order to fill the symbol table with declarations accordingly
				// the result can only contain statements, which we drop.
				main.dispatch(child);

				continue;
			}
			isFirst = false;

			checkForACSL(main, ifBlock, decl, child, null);
			if (child instanceof IASTCaseStatement || child instanceof IASTDefaultStatement) {
				final ExpressionResult caseExpression = (ExpressionResult) main.dispatch(child);
				if (locC != null) {
					final IfStatement ifStmt = new IfStatement(locC, new IdentifierExpression(locC, switchFlag),
							ifBlock.toArray(new Statement[0]), new Statement[0]);
					final Map<String, IAnnotations> annots = ifStmt.getPayload().getAnnotations();

					for (final Overapprox overapprItem : caseExpression.overappr) {
						annots.put(Overapprox.getIdentifier(), overapprItem);
					}

					if (firstCond) {
						stmt.add(new AssignmentStatement(locC, new LeftHandSide[] { new VariableLHS(locC, switchFlag) },
								new Expression[] { cond }));
						firstCond = false;
					} else {
						stmt.add(new AssignmentStatement(locC, new LeftHandSide[] { new VariableLHS(locC, switchFlag) },
								new Expression[] { ExpressionFactory.newBinaryExpression(locC, Operator.LOGICOR,
										new IdentifierExpression(locC, switchFlag), cond) }));
					}
					stmt.add(ifStmt);
				}

				ifBlock = new ArrayList<Statement>();
				locC = LocationFactory.createCLocation(child);

				if (child instanceof IASTCaseStatement) {
					// 6.8.4.2-5: "The constant expression in each case label is converted to the promoted type of the
					// controlling expression"
					mExpressionTranslation.convertIntToInt(locC, caseExpression, (CPrimitive) l.lrVal.getCType());
					cond = ExpressionFactory.newBinaryExpression(locC, Operator.COMPEQ, switchArg,
							caseExpression.lrVal.getValue());
					decl.addAll(caseExpression.decl);
					stmt.addAll(caseExpression.stmt);
					auxVars.putAll(caseExpression.auxVars);
					overappr.addAll(caseExpression.overappr);
				} else {
					// default statement
					cond = caseExpression.lrVal.getValue();
				}

				/*
				 * for (Statement s : res.stmt) if (s instanceof BreakStatement) ifBlock.add(new GotoStatement(locC, new
				 * String[] { breakLabelName })); else ifBlock.add(s);
				 */
			} else {
				final Result r = main.dispatch(child);

				if (r instanceof ExpressionResult) {
					final ExpressionResult res = (ExpressionResult) r;
					decl.addAll(res.decl);
					auxVars.putAll(res.auxVars);
					overappr.addAll(res.overappr);
					for (final Statement s : res.stmt) {
						if (s instanceof BreakStatement) {
							ifBlock.add(new GotoStatement(locC, new String[] { breakLabelName }));
						} else {
							ifBlock.add(s);
						}
					}
				}
				if (r.node != null && r.node instanceof Body) {
					// we already have a unique naming for variables! -> unfold
					final Body b = ((Body) r.node);
					decl.addAll(Arrays.asList(b.getLocalVars()));
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
		assert cond != null;
		if (locC != null) {
			final IfStatement ifStmt = new IfStatement(locC, new IdentifierExpression(locC, switchFlag),
					ifBlock.toArray(new Statement[0]), new Statement[0]);
			final Map<String, IAnnotations> annots = ifStmt.getPayload().getAnnotations();
			for (final Overapprox overapprItem : overappr) {
				annots.put(Overapprox.getIdentifier(), overapprItem);
			}

			if (firstCond) {
				stmt.add(new AssignmentStatement(locC, new LeftHandSide[] { new VariableLHS(locC, switchFlag) },
						new Expression[] { cond }));
				firstCond = false;
			} else {
				stmt.add(new AssignmentStatement(locC, new LeftHandSide[] { new VariableLHS(locC, switchFlag) },
						new Expression[] { ExpressionFactory.newBinaryExpression(locC, Operator.LOGICOR,
								new IdentifierExpression(locC, switchFlag), cond) }));
			}
			stmt.add(ifStmt);
		}
		checkForACSL(main, stmt, decl, null, node);

		stmt.add(new Label(loc, breakLabelName));
		stmt.addAll(createHavocsForAuxVars(auxVars));

		stmt = updateStmtsAndDeclsAtScopeEnd(main, decl, stmt);
		endScope();

		return new ExpressionResult(stmt, null, decl, new LinkedHashMap<VariableDeclaration, ILocation>(), overappr);
	}

	/**
	 * Translate a case statement for use inside a switch statement. C99:6.8.4.2-3: "The expression of each case label
	 * shall be an integer constant expression and no two of the case constant expressions in the same switch statement
	 * shall have the same value after conversion."
	 * 
	 */
	@Override
	public Result visit(Dispatcher main, IASTCaseStatement node) {
		final ILocation loc = LocationFactory.createCLocation(node);
		ExpressionResult c = (ExpressionResult) main.dispatch(node.getExpression());
		c = c.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, LocationFactory.createCLocation(node));
		mExpressionTranslation.convertIntToInt(loc, c, new CPrimitive(PRIMITIVE.INT));
		return c;
	}

	@Override
	public Result visit(Dispatcher main, IASTDefaultStatement node) {
		final ArrayList<Statement> stmt = new ArrayList<Statement>();
		final ArrayList<Declaration> decl = new ArrayList<Declaration>();
		final Map<VariableDeclaration, ILocation> emptyAuxVars = new LinkedHashMap<VariableDeclaration, ILocation>(0);
		final List<Overapprox> overappr = new ArrayList<Overapprox>();
		return new ExpressionResult(stmt, new RValue(new BooleanLiteral(LocationFactory.createCLocation(node), true),
				new CPrimitive(PRIMITIVE.INT)), decl, emptyAuxVars, overappr);
	}

	@Override
	public Result visit(Dispatcher main, IASTLabelStatement node) {
		final ILocation loc = LocationFactory.createCLocation(node);
		final ArrayList<Statement> stmt = new ArrayList<Statement>();
		final ArrayList<Declaration> decl = new ArrayList<Declaration>();
		final Map<VariableDeclaration, ILocation> emptyAuxVars = new LinkedHashMap<VariableDeclaration, ILocation>(0);
		final List<Overapprox> overappr = new ArrayList<Overapprox>();
		final String label = node.getName().toString();
		if (mErrorLabelWarning && label.equals("ERROR")) {
			final String longDescription = "The label \"ERROR\" does not have a special meaning in the translation mode you selected. You might want to change your settings and use the SV-COMP translation mode.";
			main.warn(loc, longDescription);
		}
		stmt.add(new Label(loc, label));
		final Result r = main.dispatch(node.getNestedStatement());
		if (r instanceof ExpressionResult) {
			final ExpressionResult res = (ExpressionResult) r;
			decl.addAll(res.decl);
			stmt.addAll(res.stmt);
			overappr.addAll(res.overappr);
			return new ExpressionResult(stmt, res.lrVal, decl, emptyAuxVars, overappr);
		} else if (r instanceof SkipResult) {
			return new ExpressionResult(stmt, null, decl, emptyAuxVars);
		} else { // r instanceof Result ...
			RValue expr = null;
			if (r.node instanceof Statement) {
				stmt.add((Statement) r.node);
			} else if (r.node instanceof Declaration) {
				decl.add((Declaration) r.node);
			} else if (r.node instanceof Expression) {
				expr = new RValue((Expression) r.node, null);// FIXME ??
			} else if (r.node instanceof Body) {
				// we already have a unique naming for variables! --> unfold
				final Body b = ((Body) r.node);
				decl.addAll(Arrays.asList(b.getLocalVars()));
				stmt.addAll(Arrays.asList(b.getBlock()));
			} else {
				final String msg = "Unexpected boogie AST node type: " + r.node.getClass();
				throw new UnsupportedSyntaxException(loc, msg);
			}
			return new ExpressionResult(stmt, expr, decl, emptyAuxVars);
		}
	}

	@Override
	public Result visit(Dispatcher main, IASTGotoStatement node) {
		final ArrayList<Statement> stmt = new ArrayList<Statement>();
		final String[] name = new String[] { node.getName().toString() };
		stmt.add(new GotoStatement(LocationFactory.createCLocation(node), name));
		return new ExpressionResult(stmt, null);
	}

	@Override
	public Result visit(Dispatcher main, IASTCastExpression node) {
		final ILocation loc = LocationFactory.createCLocation(node);

		// TODO: check validity of cast?

		final TypesResult resTypes = (TypesResult) main.dispatch(node.getTypeId().getDeclSpecifier());

		mCurrentDeclaredTypes.push(resTypes);
		final DeclaratorResult declResult = (DeclaratorResult) main.dispatch(node.getTypeId().getAbstractDeclarator());
		final CType newCType = declResult.getDeclaration().getType();
		mCurrentDeclaredTypes.pop();

		ExpressionResult expr = (ExpressionResult) main.dispatch(node.getOperand());
		if (expr.lrVal.getCType().getUnderlyingType() instanceof CArray
				&& newCType.getUnderlyingType() instanceof CPointer) {
			final CType valueType = ((CArray) expr.lrVal.getCType().getUnderlyingType()).getValueType().getUnderlyingType();
			if (expr.lrVal instanceof HeapLValue) {
				expr.lrVal = new RValue(((HeapLValue) expr.lrVal).getAddress(), new CPointer(valueType));
			} else {
				expr.lrVal = new RValue(expr.lrVal.getValue(), new CPointer(valueType));
			}
		} else {
			expr = expr.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
		}

		if (POINTER_CAST_IS_UNSUPPORTED_SYNTAX && newCType instanceof CPointer
				&& expr.lrVal.getCType() instanceof CPointer) {
			final CType newPointsToType = ((CPointer) newCType).pointsToType;
			final CType exprPointsToType = ((CPointer) expr.lrVal.getCType()).pointsToType;
			if (newPointsToType instanceof CPrimitive && exprPointsToType instanceof CPrimitive) {
				if (((CPrimitive) newPointsToType).getGeneralType() == GENERALPRIMITIVE.INTTYPE
						&& ((CPrimitive) exprPointsToType).getGeneralType() == GENERALPRIMITIVE.INTTYPE) {
					if ((((CPrimitive) newPointsToType).isUnsigned() && !((CPrimitive) exprPointsToType).isUnsigned())
							|| !(((CPrimitive) newPointsToType).isUnsigned()
									&& ((CPrimitive) exprPointsToType).isUnsigned())) {
						throw new UnsupportedSyntaxException(loc, "unsupported cast: " + exprPointsToType
								+ " pointer  to " + newPointsToType + " pointer");
					}

				} else if (((CPrimitive) newPointsToType).getGeneralType() == GENERALPRIMITIVE.VOID
						&& ((CPrimitive) exprPointsToType).getGeneralType() == GENERALPRIMITIVE.INTTYPE
						|| ((CPrimitive) newPointsToType).getGeneralType() == GENERALPRIMITIVE.INTTYPE
								&& ((CPrimitive) exprPointsToType).getGeneralType() == GENERALPRIMITIVE.VOID) {
					throw new UnsupportedSyntaxException(loc,
							"unsupported cast: " + exprPointsToType + " pointer  to " + newPointsToType + " pointer");
				}
			}
		}

		expr.rexBoolToIntIfNecessary(loc, mExpressionTranslation);
		convert(loc, expr, newCType);

		// String msg = "Ignored cast! At line: "
		// + node.getFileLocation().getStartingLineNumber();
		// Dispatcher.unsoundnessWarning(loc, msg,
		// "Ignored cast!");
		return expr;
	}

	@Override
	public Result visit(Dispatcher main, IASTConditionalExpression node) {
		final ILocation loc = LocationFactory.createCLocation(node);
		assert node.getChildren().length == 3;
		final Result resLocCond = main.dispatch(node.getLogicalConditionExpression());
		assert resLocCond instanceof ExpressionResult;
		ExpressionResult reLocCond = (ExpressionResult) resLocCond;
		reLocCond = reLocCond.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
		reLocCond.rexIntToBoolIfNecessary(loc, mExpressionTranslation, mMemoryHandler);

		final Result rPositive = main.dispatch(node.getPositiveResultExpression());
		assert rPositive instanceof ExpressionResult;
		ExpressionResult rePositive = (ExpressionResult) rPositive;
		rePositive = rePositive.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
		rePositive.rexBoolToIntIfNecessary(loc, mExpressionTranslation);

		final Result rNegative = main.dispatch(node.getNegativeResultExpression());
		assert rNegative instanceof ExpressionResult;
		ExpressionResult reNegative = (ExpressionResult) rNegative;
		reNegative = reNegative.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
		reNegative.rexBoolToIntIfNecessary(loc, mExpressionTranslation);

		if (rePositive.lrVal.getCType().isArithmeticType() && reNegative.lrVal.getCType().isArithmeticType()) {
			// C11 6.5.15.5: If 2nd and 3rd operand have arithmetic type,
			// the result type is determined by the usual arithmetic conversions.
			mExpressionTranslation.usualArithmeticConversions(loc, rePositive, reNegative);
		}

		if ((rePositive.lrVal.getCType().getUnderlyingType() instanceof CPointer)
				&& reNegative.lrVal.getCType().getUnderlyingType().isIntegerType()) {
			mExpressionTranslation.convertIntToPointer(loc, reNegative,
					(CPointer) rePositive.lrVal.getCType().getUnderlyingType());
		}
		if ((reNegative.lrVal.getCType().getUnderlyingType() instanceof CPointer)
				&& rePositive.lrVal.getCType().getUnderlyingType().isIntegerType()) {
			mExpressionTranslation.convertIntToPointer(loc, rePositive,
					(CPointer) reNegative.lrVal.getCType().getUnderlyingType());
		}

		final ArrayList<Statement> stmt = new ArrayList<Statement>();
		final ArrayList<Declaration> decl = new ArrayList<Declaration>();
		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>(0);
		final List<Overapprox> overappr = new ArrayList<Overapprox>();

		decl.addAll(reLocCond.decl);
		auxVars.putAll(reLocCond.auxVars);
		stmt.addAll(reLocCond.stmt);
		overappr.addAll(reLocCond.overappr);

		final String tmpName = mNameHandler.getTempVarUID(SFO.AUXVAR.ITE, new CPrimitive(PRIMITIVE.INT));
		final ASTType tmpType = mTypeHandler.ctype2asttype(loc, rePositive.lrVal.getCType());
		final VariableDeclaration tmpVar = SFO.getTempVarVariableDeclaration(tmpName, tmpType, loc);

		decl.add(tmpVar);
		auxVars.put(tmpVar, loc);

		final RValue condition = (RValue) reLocCond.lrVal;
		final List<Statement> ifStatements = new ArrayList<Statement>();
		{
			ifStatements.addAll(rePositive.stmt);
			final LeftHandSide[] lhs = { new VariableLHS(loc, tmpName) };
			final Expression assignedVal = rePositive.lrVal.getValue();
			if (assignedVal != null) {
				final AssignmentStatement assignStmt = new AssignmentStatement(loc, lhs,
						new Expression[] { rePositive.lrVal.getValue() });
				final Map<String, IAnnotations> annots = assignStmt.getPayload().getAnnotations();
				for (final Overapprox overapprItem : overappr) {
					annots.put(Overapprox.getIdentifier(), overapprItem);
				}
				ifStatements.add(assignStmt);
			}
			decl.addAll(rePositive.decl);
			auxVars.putAll(rePositive.auxVars);
			overappr.addAll(rePositive.overappr);
		}

		final List<Statement> elseStatements = new ArrayList<Statement>();
		{
			elseStatements.addAll(reNegative.stmt);
			final LeftHandSide[] lhs = { new VariableLHS(loc, tmpName) };
			final Expression assignedVal = reNegative.lrVal.getValue();
			if (assignedVal != null) { // if we call a void function, we have to
										// skip this assignment
				final AssignmentStatement assignStmt = new AssignmentStatement(loc, lhs, new Expression[] { assignedVal });
				final Map<String, IAnnotations> annots = assignStmt.getPayload().getAnnotations();
				for (final Overapprox overapprItem : overappr) {
					annots.put(Overapprox.getIdentifier(), overapprItem);
				}
				elseStatements.add(assignStmt);
			}
			decl.addAll(reNegative.decl);
			auxVars.putAll(reNegative.auxVars);
			overappr.addAll(reNegative.overappr);
		}
		final Statement ifStatement = new IfStatement(loc, condition.getValue(), ifStatements.toArray(new Statement[0]),
				elseStatements.toArray(new Statement[0]));
		final Map<String, IAnnotations> annots = ifStatement.getPayload().getAnnotations();
		for (final Overapprox overapprItem : overappr) {
			annots.put(Overapprox.getIdentifier(), overapprItem);
		}
		stmt.add(ifStatement);

		final IdentifierExpression tmpExpr = new IdentifierExpression(loc, tmpName);
		return new ExpressionResult(stmt, new RValue(tmpExpr, rePositive.lrVal.getCType()), decl, auxVars, overappr);
	}

	@Override
	public Result visit(Dispatcher main, IASTArraySubscriptExpression node) {
		return mArrayHandler.handleArraySubscriptExpression(main, mMemoryHandler, mStructHandler, node);
	}

	@Override
	public Result visit(Dispatcher main, IASTInitializerClause node) {
		assert node.getChildren().length == 1;
		final Result r = main.dispatch(node.getChildren()[0]);
		assert r instanceof ExpressionResult;
		final ExpressionResult rex = (ExpressionResult) r;
		return rex.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler,
				LocationFactory.createCLocation(node));
	}

	@Override
	public Result visit(Dispatcher main, IASTFieldReference node) {
		return mStructHandler.handleFieldReference(main, node);
	}

	@Override
	public Result visit(Dispatcher main, IASTPointer node) {
		// TODO : implement pointer IASTPointer? When is this required?!
		throw new UnsupportedOperationException("This should have been handled before ...");
	}

	@Override
	public Result visit(Dispatcher main, IASTProblemStatement node) {
		final String msg = "Syntax error (statement problem) in C program: " + node.getProblem().getMessage();
		final ILocation loc = LocationFactory.createCLocation(node);
		throw new IncorrectSyntaxException(loc, msg);
	}

	@Override
	public Result visit(Dispatcher main, IASTProblemDeclaration node) {
		final String msg = "Syntax error (declaration problem) in C program: " + node.getProblem().getMessage();
		final ILocation loc = LocationFactory.createCLocation(node);
		throw new IncorrectSyntaxException(loc, msg);
	}

	@Override
	public Result visit(Dispatcher main, IASTProblemExpression node) {
		final String msg = "Syntax error (expression problem) in C program: " + node.getProblem().getMessage();
		final ILocation loc = LocationFactory.createCLocation(node);
		throw new IncorrectSyntaxException(loc, msg);
	}

	@Override
	public Result visit(Dispatcher main, IASTProblem node) {
		final String msg = "Syntax error in C program: " + node.getMessage();
		final ILocation loc = LocationFactory.createCLocation(node);
		throw new IncorrectSyntaxException(loc, msg);
	}

	@Override
	public Result visit(Dispatcher main, IASTProblemTypeId node) {
		final String msg = "Syntax error (type ID problem) in C program: " + node.getProblem().getMessage();
		final ILocation loc = LocationFactory.createCLocation(node);
		throw new IncorrectSyntaxException(loc, msg);
	}

	@Override
	public Result visit(Dispatcher main, IASTTypeIdExpression node) {
		final ILocation loc = LocationFactory.createCLocation(node);
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

			return new ExpressionResult(new RValue(mMemoryHandler.calculateSizeOf(loc, dr.getDeclaration().getType()),
					new CPrimitive(PRIMITIVE.INT)));
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

	@Override
	public Result visit(Dispatcher main, IGNUASTCompoundStatementExpression node) {
		// ArrayList<Statement> stmt = new ArrayList<>();
		// ArrayList<Declaration> decl = new ArrayList<>();
		// Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();
		// ArrayList<Overapprox> overApp = new ArrayList<>();
		//
		// LRValue finalResult = null;

		// CompoundStatementExpressionResult childRes = (CompoundStatementExpressionResult)
		// main.dispatch(node.getCompoundStatement());
		return main.dispatch(node.getCompoundStatement());
		// stmt.addAll(childRes.stmt);
		// decl.addAll(childRes.decl);

		// return new ExpressionResult(stmt, childRes.lrVal, decl, Collections.<VariableDeclaration,
		// ILocation>emptyMap(), Collections.<Overapprox>emptyList());
		// return new ExpressionResult(stmt, finalResult, decl, auxVars, overApp);
	}

	/**
	 * Create a havoc statement for each variable in auxVars. (Does not modify this auxVars map). We insert havocs for
	 * auxvars after the translation of a _statement_. This means that the Expressions carry the auxVarMap outside (via
	 * the ResultExpression they return), and that map is used for calling this procedure once we reach a (basic)
	 * statement.
	 */
	public static List<HavocStatement> createHavocsForAuxVars(Map<VariableDeclaration, ILocation> allAuxVars) {
		// LinkedHashMap<VariableDeclaration, ILocation> allAuxVars = new LinkedHashMap<>();
		// //TODO: is this for-loop/are these asserts necessary? -> probably no..
		// for (Entry<VariableDeclaration, ILocation> e : auxVars.entrySet()) {
		// assert e.getKey().getVariables().length == 1
		// && e.getKey().getVariables()[0].getIdentifiers().length == 1
		// : "we always define only one auxvar at once, right?";
		// allAuxVars.put(e.getKey(), e.getValue());
		// }

		final ArrayList<HavocStatement> result = new ArrayList<HavocStatement>();
		for (final VariableDeclaration varDecl : allAuxVars.keySet()) {
			final VarList[] varLists = varDecl.getVariables();
			for (final VarList varList : varLists) {
				for (final String varId : varList.getIdentifiers()) {
					final ILocation originloc = allAuxVars.get(varDecl);
					result.add(new HavocStatement(originloc, new VariableLHS[] { new VariableLHS(originloc, varId) }));
				}
			}
		}
		return result;
	}

	/**
	 * Returns true iff all auxvars in decls are contained in auxVars
	 */
	public static boolean isAuxVarMapcomplete(INameHandler nameHandler, List<Declaration> decls,
			Map<VariableDeclaration, ILocation> auxVars) {
		boolean result = true;
		for (final Declaration rExprdecl : decls) {
			assert (rExprdecl instanceof VariableDeclaration);
			final VariableDeclaration varDecl = (VariableDeclaration) rExprdecl;

			assert varDecl
					.getVariables().length == 1 : "there are never two auxvars declared in one declaration, right??";
			final VarList vl = varDecl.getVariables()[0];
			assert vl.getIdentifiers().length == 1 : "there are never two auxvars declared in one declaration, right??";
			final String id = vl.getIdentifiers()[0];

			if (nameHandler.isTempVar(id)) {
				// malloc auxvars do not need to be havocced in some cases (alloca)
				// result &= auxVars.containsKey(varDecl) || id.contains(SFO.MALLOC);
				result &= auxVars.containsKey(varDecl);
			}
		}
		return result;
	}

	public ExpressionResult makeAssignment(ILocation loc, ArrayList<Statement> stmt, LRValue lrVal, RValue rVal,
			ArrayList<Declaration> decl, Map<VariableDeclaration, ILocation> auxVars, List<Overapprox> overappr) {
		return makeAssignment(loc, stmt, lrVal, rVal, decl, auxVars, overappr, null);
	}

	public ExpressionResult makeAssignment(ILocation loc, ArrayList<Statement> stmtOld, LRValue lrVal, RValue rVal,
			ArrayList<Declaration> declOld, Map<VariableDeclaration, ILocation> auxVarsOld,
			List<Overapprox> overapprOld, Map<StructLHS, CType> unionFieldsToCType) {
		// we do not want to edit the stmt and so on we are given --> make copies
		final ArrayList<Statement> stmt = new ArrayList<>(stmtOld);
		final ArrayList<Declaration> decl = new ArrayList<>(declOld);
		final LinkedHashMap<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>(auxVarsOld);
		final ArrayList<Overapprox> overappr = new ArrayList<>(overapprOld);

		// do implicit cast -- assume the types are compatible
		final ExpressionResult rExp = new ExpressionResult(stmt, rVal, decl, auxVars, overappr);
		convert(loc, rExp, lrVal.getCType());
		final RValue rightHandSide = (RValue) rExp.lrVal;

		// for wraparound --> and avoiding it for ints that store pointers
		if (rightHandSide.isIntFromPointer()) {
			if (lrVal instanceof HeapLValue) {
				final Expression address = ((HeapLValue) lrVal).getAddress();
				if (address instanceof IdentifierExpression) {
					final String lId = ((IdentifierExpression) ((HeapLValue) lrVal).getAddress()).getIdentifier();
					mSymbolTable.get(mSymbolTable.getCID4BoogieID(lId, loc), loc).isIntFromPointer = true;
				} else {
					// TODO
				}
			} else if (lrVal instanceof LocalLValue) {
				String lId = null;
				final LeftHandSide value = ((LocalLValue) lrVal).getLHS();
				if (value instanceof VariableLHS) {
					lId = ((VariableLHS) value).getIdentifier();
					mSymbolTable.get(mSymbolTable.getCID4BoogieID(lId, loc), loc).isIntFromPointer = true;
				} else {
					// TODO
				}
			}
		}

		if (lrVal instanceof HeapLValue) {
			final HeapLValue hlv = (HeapLValue) lrVal;

			stmt.addAll(mMemoryHandler.getWriteCall(loc, hlv, rightHandSide.getValue(), rightHandSide.getCType()));

			return new ExpressionResult(stmt, rightHandSide, decl, auxVars, overappr);
		} else if (lrVal instanceof LocalLValue) {
			final LocalLValue lValue = (LocalLValue) lrVal;
			final AssignmentStatement assignStmt = new AssignmentStatement(loc, new LeftHandSide[] { lValue.getLHS() },
					new Expression[] { rightHandSide.getValue() });
			final Map<String, IAnnotations> annots = assignStmt.getPayload().getAnnotations();
			for (final Overapprox overapprItem : overappr) {
				annots.put(Overapprox.getIdentifier(), overapprItem);
			}
			stmt.add(assignStmt);

			// add havocs if we have a write to a union (which is not on heap,
			// otherwise the heap model should deal with everything)
			if (unionFieldsToCType != null) {

				// boolean unionIsFixedSize = true;
				// for (Entry<StructLHS, CType> en : unionFieldsToCType.entrySet())
				// unionIsFixedSize &= mMemoryHandler.calculateSizeOf(rVal.cType, loc) instanceof IntegerLiteral;
				//
				// Expression lrValSize = mMemoryHandler.calculateSizeOf(lrVal.cType, loc);
				// unionIsFixedSize &= lrValSize instanceof IntegerLiteral;

				for (final Entry<StructLHS, CType> en : unionFieldsToCType.entrySet()) {

					// do not havoc when the type of the field is "compatible"
					if (rightHandSide.getCType().equals(en.getValue())
							|| (rightHandSide.getCType().getUnderlyingType() instanceof CPrimitive
									&& en.getValue() instanceof CPrimitive
									&& ((CPrimitive) rightHandSide.getCType().getUnderlyingType()).getGeneralType()
											.equals(((CPrimitive) en.getValue()).getGeneralType())
									&& (mMemoryHandler.calculateSizeOf(loc, rightHandSide.getCType()) == mMemoryHandler
											.calculateSizeOf(loc, en.getValue())))) {
						stmt.add(new AssignmentStatement(loc, new LeftHandSide[] { en.getKey() },
								new Expression[] { rightHandSide.getValue() }));
						// } else if (rightHandSide.cType.getUnderlyingType() instanceof CStruct && unionIsFixedSize) {
						// CStruct structType = (CStruct) rightHandSide.cType.getUnderlyingType();
						//
						// int lrValSizeInt = Integer.parseInt(((IntegerLiteral) lrValSize).getValue());
						// int currOffset = 0;
						// for (String fId : structType.getFieldIds()) {
						// CType fType = structType.getFieldType(fId).getUnderlyingType();
						//
						// if (currOffset > lrValSizeInt)
						// break;
						//
						// currOffset += mMemoryHandler.calculateSizeOfWithGivenTypeSizes(loc, fType);
						//
						//
						// String tmpId = mNameHandler.getTempVarUID(SFO.AUXVAR.UNION);
						// VariableDeclaration tVarDec = new VariableDeclaration(loc, new Attribute[0], new VarList[] {
						// new VarList(loc,
						// new String[] { tmpId }, mTypeHandler.ctype2asttype(loc, en.getValue())) });
						// decl.add(tVarDec);
						// auxVars.put(tVarDec, loc); //ensures that the variable will be havoced (necessary only when
						// we are inside a loop)
						//
						// stmt.add(new AssignmentStatement(loc, new LeftHandSide[] { en.getKey() },
						// new Expression[] { new IdentifierExpression(loc, tmpId) }));
						// }

					} else { // otherwise we consider the value undefined, thus havoc it
						// TODO: maybe not use auxiliary variables so lavishly
						final String tmpId = mNameHandler.getTempVarUID(SFO.AUXVAR.UNION, en.getValue());
						final VariableDeclaration tVarDec = new VariableDeclaration(loc, new Attribute[0],
								new VarList[] { new VarList(loc, new String[] { tmpId },
										mTypeHandler.ctype2asttype(loc, en.getValue())) });
						decl.add(tVarDec);
						auxVars.put(tVarDec, loc); // ensures that the variable will be havoced (necessary only when we
													// are inside a loop)

						stmt.add(new AssignmentStatement(loc, new LeftHandSide[] { en.getKey() },
								new Expression[] { new IdentifierExpression(loc, tmpId) }));
					}
				}
			}

			if (!mFunctionHandler.noCurrentProcedure()) {
				mFunctionHandler.checkIfModifiedGlobal(getSymbolTable(), BoogieASTUtil.getLHSId(lValue.getLHS()), loc);
			}
			return new ExpressionResult(stmt, lValue, decl, auxVars, overappr);
		} else {
			throw new AssertionError("Type error: trying to assign to an RValue in Statement" + loc.toString());
		}
	}

	/**
	 * Checks ACSL for the next element and whether it must be added at the place where this method is called.
	 * 
	 * @param main
	 *            the main dispatcher.
	 * @param stmt
	 *            the statement list where the acsl should be appended - this is assumed to be <code>null</code> when
	 *            called from within the <i>translation unit</i>.
	 * @param next
	 *            the current child node of a translation unit of compound statement that will be added next. Should be
	 *            <code>null</code> when called at the end of <i>compound statement</i>.
	 * @param parent
	 *            the parent node of the current ACSL node. This should only be set if called at the end of a
	 *            <i>compound statement</i> and <code>null</code> otherwise.
	 */
	private void checkForACSL(Dispatcher main, ArrayList<Statement> stmt, ArrayList<Declaration> decl, IASTNode next,
			IASTNode parent) {
		if (mAcsl != null) {
			if (next instanceof IASTTranslationUnit) {
				for (final ACSLNode globAcsl : mAcsl.mAcsl) {
					if (globAcsl instanceof GlobalLTLInvariant) {
						final LTLExpressionExtractor extractor = new LTLExpressionExtractor();
						extractor.run(globAcsl);
						mGlobAcslExtractors.add(extractor);
						// mLogger.info(extractor.getLTLFormatString());
						// Map<String, de.uni_freiburg.informatik.ultimate.model.acsl.ast.Expression> expMap =
						// extractor.getAP2SubExpressionMap();
						// Map<String, Expression> boogieExpMap = new LinkedHashMap<String, Expression>();
						// for (Entry<String, de.uni_freiburg.informatik.ultimate.model.acsl.ast.Expression> en :
						// expMap.entrySet()) {
						// Result r = main.dispatch(en.getValue());
						// boogieExpMap.put(en.getKey(), null);
						// }
						try {
							mAcsl = main.nextACSLStatement();
						} catch (final ParseException e1) {
							final String msg = "Skipped a ACSL node due to: " + e1.getMessage();
							final ILocation loc = LocationFactory.createCLocation(parent);
							main.unsupportedSyntax(loc, msg);
						}
					}
				} // TODO: deal with other global ACSL stuff
			} else if (mAcsl.mSuccessorCNode == null) {
				if (parent != null && stmt != null && next == null) {
					// ACSL at the end of a function or at the end of the last statement in a switch that is not
					// terminated by a break
					// TODO: the latter case needs fixing, the ACSL is inserted outside the corresponding if-scope right
					// now
					// example: int s = 1; switch (s) { case 0: s++; //@ assert \false; } will yield a unsafe boogie
					// program
					for (final ACSLNode acslNode : mAcsl.mAcsl) {
						if (parent.getFileLocation().getEndingLineNumber() <= acslNode.getStartingLineNumber()) {
							return;// handle later ...
						} else if (parent.getFileLocation().getEndingLineNumber() >= acslNode.getEndingLineNumber()
								&& parent.getFileLocation().getStartingLineNumber() <= acslNode
										.getStartingLineNumber()) {
							final Result acslResult = main.dispatch(acslNode);
							if (acslResult instanceof ExpressionResult) {
								decl.addAll(((ExpressionResult) acslResult).decl);
								stmt.addAll(((ExpressionResult) acslResult).stmt);
								stmt.addAll(createHavocsForAuxVars(((ExpressionResult) acslResult).auxVars));
								try {
									mAcsl = main.nextACSLStatement();
								} catch (final ParseException e1) {
									final String msg = "Skipped a ACSL node due to: " + e1.getMessage();
									final ILocation loc = LocationFactory.createCLocation(parent);
									main.unsupportedSyntax(loc, msg);
								}
							} else {
								final String msg = "Unexpected ACSL comment: " + acslResult.node.getClass();
								final ILocation loc = LocationFactory.createCLocation(parent);
								throw new IncorrectSyntaxException(loc, msg);
							}
						}
					}
				}

				// ELSE:
				// ACSL for next compound statement -> handle it next call
				// or in case of translation unit, ACSL in an unexpected
				// location!
			} else if (mAcsl.mSuccessorCNode.equals(next)) {
				assert mContract.isEmpty();
				for (final ACSLNode acslNode : mAcsl.mAcsl) {
					if (stmt != null) {
						// this means we are in a compound statement
						if (acslNode instanceof Contract || acslNode instanceof LoopAnnot) {
							// Loop contract
							mContract.add(acslNode);
						} else if (acslNode instanceof CodeAnnot) {
							final Result acslResult = main.dispatch(acslNode);
							if (acslResult instanceof ExpressionResult) {
								// thrax93
								final ExpressionResult re = (ExpressionResult) acslResult;
								stmt.addAll(re.stmt);
								decl.addAll(re.decl);
							} else {
								stmt.add((Statement) acslResult.node);
							}
						} else {
							final String msg = "Unexpected ACSL comment: " + acslNode.getClass();
							final ILocation loc = LocationFactory.createCLocation(next);
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
					final ILocation loc = LocationFactory.createCLocation(parent);
					main.unsupportedSyntax(loc, msg);
				}

			}
		}
	}

	@Override
	public TypesResult checkForPointer(Dispatcher main, IASTPointerOperator[] pointerOps, TypesResult resType,
			boolean putOnHeap) {
		if (putOnHeap || pointerOps.length != 0) {
			// TODO : not sure, if this is enough!
			// There could be multiple PointerOperators (i.e.
			// IASTPointer) - what does that mean for the translation?
			// String typeId = resType.cvar.toString();
			final ASTType t = mTypeHandler.constructPointerType(null);
			final CType cvar = new CPointer(resType.cType);
			return new TypesResult(t, resType.isConst, resType.isVoid, cvar);
		}
		return resType;
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

	/**
	 * Like {@link CHandler#doPointerArithmetic(int, ILocation, Expression, RValue, CType)} but additionally the integer
	 * operand is converted to the same type that we use to represent pointer components. As a consequence we have to
	 * return an ExpressionResult.
	 */
	public ExpressionResult doPointerArithmeticWithConversion(Dispatcher main, int operator, ILocation loc,
			Expression ptrAddress, RValue integer, CType valueType) {
		final ExpressionResult eres = new ExpressionResult(integer);
		final AExpressionTranslation exprTrans = ((CHandler) main.mCHandler).getExpressionTranslation();
		exprTrans.convertIntToInt(loc, eres, exprTrans.getCTypeOfPointerComponents());
		final Expression resultExpression = mMemoryHandler.doPointerArithmetic(operator, loc, ptrAddress, (RValue) eres.lrVal,
				valueType);
		eres.lrVal = new RValue(resultExpression, mExpressionTranslation.getCTypeOfPointerComponents());
		return eres;
	}

	/**
	 * Method that handles loops (for, while, do/while). Each of corresponding visit methods will call this method.
	 * 
	 * @param main
	 *            the main dispatcher
	 * @param node
	 *            the node to visit
	 * @param bodyResult
	 *            the body component of the corresponding loop
	 * @param condResult
	 *            the condition of the loop
	 * @param loopLabel
	 * @return a result object holding the translated loop (i.e. a while loop)
	 */
	private Result handleLoops(Dispatcher main, IASTStatement node, Result bodyResult, ExpressionResult condResult,
			String loopLabel) {
		final int scopeDepth = mSymbolTable.getActiveScopeNum();
		assert node instanceof IASTWhileStatement || node instanceof IASTDoStatement
				|| node instanceof IASTForStatement;

		final ILocation loc = LocationFactory.createCLocation(node);

		final ArrayList<Statement> stmt = new ArrayList<Statement>();
		final ArrayList<Declaration> decl = new ArrayList<Declaration>();
		final List<Overapprox> overappr = new ArrayList<Overapprox>();
		final Map<VariableDeclaration, ILocation> emptyAuxVars = new LinkedHashMap<VariableDeclaration, ILocation>(0);

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
					stmt.addAll(rExp.stmt);
					decl.addAll(rExp.decl);
					overappr.addAll(rExp.overappr);
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
				condResult = new ExpressionResult(
						new RValue((new BooleanLiteral(loc, true)), new CPrimitive(PRIMITIVE.BOOL), true),
						new LinkedHashMap<VariableDeclaration, ILocation>(0));
			}

			mInnerMostLoopLabel.push(loopLabel);
			bodyResult = main.dispatch(forStmt.getBody());
			mInnerMostLoopLabel.pop();
		}
		assert (isAuxVarMapcomplete(mNameHandler, condResult.decl, condResult.auxVars));

		ArrayList<Statement> bodyBlock = new ArrayList<Statement>();
		if (bodyResult instanceof ExpressionResult) {
			final ExpressionResult re = (ExpressionResult) bodyResult;
			decl.addAll(re.decl);
			overappr.addAll(re.overappr);
			bodyBlock.addAll(re.stmt);
		} else if (bodyResult instanceof Result) {
			if (bodyResult.node instanceof Body) {
				final Body body = (Body) (bodyResult.node);
				bodyBlock.addAll(Arrays.asList(body.getBlock()));
				decl.addAll(Arrays.asList(body.getLocalVars()));
			} else if (bodyResult instanceof SkipResult) {
				// do nothing - this is the special case where the loop does
				// not have a body.
			} else {
				final String msg = "Error: unexpected dispatch result" + bodyResult.getClass();
				throw new UnsupportedSyntaxException(loc, msg);
			}
		}

		if (node instanceof IASTForStatement && iterator != null) {
			bodyBlock.add(new Label(loc, loopLabel));
			// add iterator statements of this for loop
			if (iterator instanceof ExpressionListResult) {
				for (final ExpressionResult el : ((ExpressionListResult) iterator).list) {
					bodyBlock.addAll(el.stmt);
					decl.addAll(el.decl);
					// assert (isAuxVarMapcomplete(main, el.decl, el.auxVars));
					bodyBlock.addAll(createHavocsForAuxVars(el.auxVars));
				}
			} else if (iterator instanceof ExpressionResult) {
				final ExpressionResult iteratorRE = (ExpressionResult) iterator;
				bodyBlock.addAll(iteratorRE.stmt);
				decl.addAll(iteratorRE.decl);
				overappr.addAll(iteratorRE.overappr);
				// 2015-11-08 Matthias: assert seems to be wrong here
				// auxVars have already been havoced
				// assert (isAuxVarMapcomplete(main, iteratorRE.decl, iteratorRE.auxVars));
				bodyBlock.addAll(createHavocsForAuxVars(iteratorRE.auxVars));
			} else {
				final String msg = "Uninplemented type of loop iterator: " + iterator.getClass();
				throw new UnsupportedSyntaxException(loc, msg);
			}
		}

		condResult = condResult.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
		condResult.rexIntToBoolIfNecessary(loc, mExpressionTranslation, mMemoryHandler);
		decl.addAll(condResult.decl);
		final RValue condRVal = (RValue) condResult.lrVal;
		IfStatement ifStmt;
		{
			final Expression cond = ExpressionFactory.newUnaryExpression(loc, UnaryExpression.Operator.LOGICNEG,
					condRVal.getValue());
			final ArrayList<Statement> thenStmt = new ArrayList<Statement>(createHavocsForAuxVars(condResult.auxVars));
			thenStmt.add(new BreakStatement(loc));
			final Statement[] elseStmt = createHavocsForAuxVars(condResult.auxVars).toArray(new Statement[0]);
			ifStmt = new IfStatement(loc, cond, thenStmt.toArray(new Statement[0]), elseStmt);
		}

		if (node instanceof IASTWhileStatement || node instanceof IASTForStatement) {
			bodyBlock.add(0, ifStmt);
			bodyBlock.addAll(0, condResult.stmt);
			if (node instanceof IASTWhileStatement) {
				bodyBlock.add(0, new Label(loc, loopLabel));
			}
		} else if (node instanceof IASTDoStatement) {
			bodyBlock.add(new Label(loc, loopLabel));
			bodyBlock.addAll(condResult.stmt);
			bodyBlock.add(ifStmt);
		}

		LoopInvariantSpecification[] spec;
		if (mContract == null) {
			spec = new LoopInvariantSpecification[0];
		} else {
			final List<LoopInvariantSpecification> specList = new ArrayList<LoopInvariantSpecification>();
			if (node instanceof IASTForStatement) {
				for (int i = 0; i < mContract.size(); i++) {
					// retranslate ACSL specification needed e.g., in cases
					// where ids of function parameters differ from is in ACSL
					// expression
					final Result retranslateRes = main.dispatch(mContract.get(i));
					if (retranslateRes instanceof ContractResult) {
						final ContractResult resContr = (ContractResult) retranslateRes;
						assert resContr.specs.length == 1;
						for (final Specification cSpec : resContr.specs) {
							specList.add((LoopInvariantSpecification) cSpec);
						}
					} else {
						specList.add((LoopInvariantSpecification) retranslateRes.node);
					}
				}
			}
			spec = specList.toArray(new LoopInvariantSpecification[0]);
			clearContract(); // take care for behavior and completeness
		}

		if (node instanceof IASTForStatement) {
			if (((IASTForStatement) node).getInitializerStatement() != null) {
				bodyBlock = updateStmtsAndDeclsAtScopeEnd(main, decl, bodyBlock);

				endScope();
			}
		}

		final ILocation ignoreLocation = LocationFactory.createIgnoreCLocation(node);
		final WhileStatement whileStmt = new WhileStatement(ignoreLocation, new BooleanLiteral(ignoreLocation, true), spec,
				bodyBlock.toArray(new Statement[0]));
		final Map<String, IAnnotations> annots = whileStmt.getPayload().getAnnotations();
		for (final Overapprox overapprItem : overappr) {
			annots.put(Overapprox.getIdentifier(), overapprItem);
		}
		stmt.add(whileStmt);

		assert (mSymbolTable.getActiveScopeNum() == scopeDepth);
		return new ExpressionResult(stmt, null, decl, emptyAuxVars, overappr);
	}

	@Override
	public boolean isHeapVar(String boogieId) {
		final CStorageClass c;
		return mBoogieIdsOfHeapVars.contains(boogieId);
	}

	protected CStorageClass scConstant2StorageClass(int storageClass) {
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
	 * Handles the declaration of an enum type (-d variable).
	 * 
	 * @param main
	 *            a reference to the main dispatcher.
	 * @param node
	 *            the node holding the enum declaration.
	 * @return the translation of this declaration.
	 */
	protected void handleEnumDeclaration(Dispatcher main, IASTSimpleDeclaration node) {
		final Result r = main.dispatch(node.getDeclSpecifier());
		assert r instanceof TypesResult;
		final TypesResult rt = (TypesResult) r;
		assert rt.cType instanceof CEnum;
		final CEnum cEnum = (CEnum) rt.cType;
		final ILocation loc = LocationFactory.createCLocation(node);
		final CPrimitive intType = new CPrimitive(PRIMITIVE.INT);
		final ASTType at = mTypeHandler.ctype2asttype(loc, intType);
		final String enumId = cEnum.getIdentifier();
		Expression oldValue = null;
		final Expression[] enumDomain = new Expression[cEnum.getFieldCount()];

		// C standard says: "The identifiers in an enumerator list are declared
		// as constants that have type int ..."
		final CPrimitive typeOfEnumIdentifiers = new CPrimitive(CPrimitive.PRIMITIVE.INT);

		// ResultDeclaration result = new ResultDeclaration();
		for (int i = 0; i < cEnum.getFieldCount(); i++) {
			final String fId = cEnum.getFieldIds()[i];
			final String bId = enumId + "~" + fId;
			final VarList vl = new VarList(loc, new String[] { bId }, at);
			final ConstDeclaration cd = new ConstDeclaration(loc, new Attribute[0], false, vl, null, false);
			mDeclarationsGlobalInBoogie.put(cd, new CDeclaration(cEnum, fId));
			final Expression l = new IdentifierExpression(loc, bId);
			Expression newValue = oldValue;
			if (oldValue == null && cEnum.getFieldValue(fId) == null) {
				final Expression zero = mExpressionTranslation.constructLiteralForIntegerType(loc, typeOfEnumIdentifiers,
						BigInteger.ZERO);
				newValue = zero;
			} else if (cEnum.getFieldValue(fId) == null) {
				final Expression one = mExpressionTranslation.constructLiteralForIntegerType(loc, typeOfEnumIdentifiers,
						BigInteger.ONE);
				newValue = mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_plus,
						oldValue, typeOfEnumIdentifiers, one, typeOfEnumIdentifiers);
			} else {
				newValue = cEnum.getFieldValue(fId);
			}
			oldValue = newValue;
			enumDomain[i] = newValue;
			mAxioms.add(new Axiom(loc, new Attribute[0],
					ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, l, newValue)));
			mSymbolTable
					.put(fId,
							new SymbolTableValue(bId, cd,
									new CDeclaration(typeOfEnumIdentifiers, fId,
											scConstant2StorageClass(node.getDeclSpecifier().getStorageClass())),
									true, node)); // FIXME ??
		}
		// return result;
	}

	public Result handleLabelCommonCode(Dispatcher main, IASTLabelStatement node, ILocation loc) {

		final ArrayList<Statement> stmt = new ArrayList<Statement>();
		final ArrayList<Declaration> decl = new ArrayList<Declaration>();
		final Map<VariableDeclaration, ILocation> emptyAuxVars = new LinkedHashMap<VariableDeclaration, ILocation>(0);
		final List<Overapprox> overappr = new ArrayList<Overapprox>();
		final String label = node.getName().toString();
		stmt.add(new Label(loc, label));
		final Result r = main.dispatch(node.getNestedStatement());
		if (r instanceof ExpressionResult) {
			final ExpressionResult res = (ExpressionResult) r;
			decl.addAll(res.decl);
			stmt.addAll(res.stmt);
			overappr.addAll(res.overappr);
			return new ExpressionResult(stmt, res.lrVal, decl, emptyAuxVars, overappr);
		} else if (r instanceof SkipResult) {
			return new ExpressionResult(stmt, null, decl, emptyAuxVars, overappr);
		} else { // r instanceof Result ...
			RValue expr = null;
			if (r.node instanceof Statement) {
				stmt.add((Statement) r.node);
			} else if (r.node instanceof Declaration) {
				decl.add((Declaration) r.node);
			} else if (r.node instanceof Expression) {
				expr = new RValue((Expression) r.node, null); // FIXME ??
			} else if (r.node instanceof Body) {
				// we already have a unique naming for variables! --> unfold
				final Body b = ((Body) r.node);
				decl.addAll(Arrays.asList(b.getLocalVars()));
				stmt.addAll(Arrays.asList(b.getBlock()));
			} else {
				final String msg = "Unexpected boogie AST node type: " + r.node.getClass();
				throw new UnsupportedSyntaxException(loc, msg);
			}
			return new ExpressionResult(stmt, expr, decl, emptyAuxVars, overappr);
		}
	}

	/**
	 * mdeclarationsGlobalInBoogie may contain type declarations that stem from typedefs using an incomplete struct
	 * type. This method is called when the struct type is completed.
	 * 
	 * @param cvar
	 * @param incompleteStruct
	 */
	public void completeTypeDeclaration(CType incompleteStruct, CType cvar) {
		assert incompleteStruct.getClass().equals(cvar.getClass());
		assert incompleteStruct.isIncomplete();
		TypeDeclaration oldDec = null;
		CDeclaration oldCDec = null;
		TypeDeclaration newDec = null;
		for (final Entry<Declaration, CDeclaration> en : mDeclarationsGlobalInBoogie.entrySet()) {
			if (en.getValue().getType().toString().equals(incompleteStruct.toString())) {
				oldDec = (TypeDeclaration) en.getKey();
				oldCDec = en.getValue();
				newDec = new TypeDeclaration(oldDec.getLocation(), oldDec.getAttributes(), oldDec.isFinite(),
						oldDec.getIdentifier(), oldDec.getTypeParams(),
						mTypeHandler.ctype2asttype(oldDec.getLocation(), cvar));
				break; // the if should be entered only once, anyway
			}
		}
		if (oldDec != null) {
			mDeclarationsGlobalInBoogie.remove(oldDec);
			mDeclarationsGlobalInBoogie.put(newDec, oldCDec);
		}
	}

	/**
	 * @param bId
	 *            Boogie ID
	 */
	public void addBoogieIdsOfHeapVars(String bId) {
		mBoogieIdsOfHeapVars.add(bId);
	}

	@Override
	public void clearContract() {
		mContract.clear();
	}

	public static Expression convertLHSToExpression(LeftHandSide lhs) {
		if (lhs instanceof VariableLHS) {
			return new IdentifierExpression(lhs.getLocation(), ((VariableLHS) lhs).getIdentifier());
		} else if (lhs instanceof ArrayLHS) {
			final ArrayLHS alhs = (ArrayLHS) lhs;
			final Expression array = convertLHSToExpression(alhs.getArray());
			return new ArrayAccessExpression(alhs.getLocation(), alhs.getType(), array, alhs.getIndices());
		} else if (lhs instanceof StructLHS) {
			final StructLHS slhs = (StructLHS) lhs;
			final Expression struct = convertLHSToExpression(slhs.getStruct());
			return new StructAccessExpression(slhs.getLocation(), slhs.getType(), struct, slhs.getField());
		} else {
			throw new AssertionError("Strange LeftHandSide " + lhs);
		}
	}

	@Override
	public void beginScope() {
		mTypeHandler.beginScope();
		mSymbolTable.beginScope();
		mMemoryHandler.getVariablesToBeMalloced().beginScope();
		mMemoryHandler.getVariablesToBeFreed().beginScope();
	}

	@Override
	public void endScope() {
		mTypeHandler.endScope();
		mSymbolTable.endScope();
		mMemoryHandler.getVariablesToBeMalloced().endScope();
		mMemoryHandler.getVariablesToBeFreed().endScope();
	}

	/**
	 * Handle conversions according to Section 6.3 of C11.
	 * 
	 * @param loc
	 * @param rexp
	 * @param newTypeRaw
	 */
	@Override
	public void convert(ILocation loc, ExpressionResult rexp, CType newTypeRaw) {
		final RValue rValIn = (RValue) rexp.lrVal;
		final CType newType = newTypeRaw.getUnderlyingType();
		final CType oldType = rValIn.getCType().getUnderlyingType();
		if (oldType.equals(newType)) {
			return;
		}

		if (newType instanceof CPrimitive) {
			final CPrimitive cPrimitive = (CPrimitive) newType;
			if (cPrimitive.isIntegerType()) {
				convertToIntegerType(loc, rexp, (CPrimitive) newType);
			} else if (cPrimitive.isRealFloatingType()) {
				convertToFloatingType(loc, rexp, (CPrimitive) newType);
			} else if (cPrimitive.getType().equals(PRIMITIVE.VOID)) {
				convertToVoid(loc, rexp, (CPrimitive) newType);
			} else {
				throw new AssertionError("unknown type " + newType);
			}
		} else if (newType instanceof CPointer) {
			convertToPointer(loc, rexp, (CPointer) newType);
		} else if (newType instanceof CEnum) {
			// C standard 6.4.4.3.2
			// An identifier declared as an enumeration constant has type int.
			convertToIntegerType(loc, rexp, new CPrimitive(PRIMITIVE.INT));
		} else if (newType instanceof CArray) {
			throw new AssertionError("cannot convert to CArray");
		} else if (newType instanceof CFunction) {
			throw new AssertionError("cannot convert to CFunction");
		} else if (newType instanceof CStruct) {
			throw new UnsupportedSyntaxException(loc, "conversion to CStruct not implemented.");
		} else {
			throw new AssertionError("unknown type " + newType);
		}
	}

	private void convertToIntegerType(ILocation loc, ExpressionResult rexp, CPrimitive newType) {
		assert (rexp.lrVal instanceof RValue) : "has to be converted to RValue";
		final CType oldType = rexp.lrVal.getCType().getUnderlyingType();
		if (oldType instanceof CPrimitive) {
			final CPrimitive cPrimitive = (CPrimitive) oldType;
			if (cPrimitive.isIntegerType()) {
				mExpressionTranslation.convertIntToInt(loc, rexp, newType);
			} else if (cPrimitive.isRealFloatingType()) {
				mExpressionTranslation.convertFloatToInt(loc, rexp, newType);
			} else if (cPrimitive.getType().equals(PRIMITIVE.VOID)) {
				throw new IncorrectSyntaxException(loc, "cannot convert from void");
			} else {
				throw new AssertionError("unknown type " + newType);
			}
		} else if (oldType instanceof CPointer) {
			mExpressionTranslation.convertPointerToInt(loc, rexp, newType);
		} else if (oldType instanceof CEnum) {
			mExpressionTranslation.convertIntToInt(loc, rexp, newType);
		} else if (oldType instanceof CArray) {
			throw new AssertionError("cannot convert from CArray");
		} else if (oldType instanceof CFunction) {
			throw new AssertionError("cannot convert from CFunction");
		} else if (oldType instanceof CStruct) {
			throw new UnsupportedSyntaxException(loc, "conversion from CStruct not implemented.");
		} else {
			throw new AssertionError("unknown type " + newType);
		}
	}

	private void convertToFloatingType(ILocation loc, ExpressionResult rexp, CPrimitive newType) {
		assert (rexp.lrVal instanceof RValue) : "has to be converted to RValue";
		final CType oldType = rexp.lrVal.getCType().getUnderlyingType();
		if (oldType instanceof CPrimitive) {
			final CPrimitive cPrimitive = (CPrimitive) oldType;
			if (cPrimitive.isIntegerType()) {
				mExpressionTranslation.convertIntToFloat(loc, rexp, newType);
			} else if (cPrimitive.isRealFloatingType()) {
				mExpressionTranslation.convertFloatToFloat(loc, rexp, newType);
			} else if (cPrimitive.getType().equals(PRIMITIVE.VOID)) {
				throw new IncorrectSyntaxException(loc, "cannot convert from void");
			} else {
				throw new AssertionError("unknown type " + newType);
			}
		} else if (oldType instanceof CPointer) {
			throw new IncorrectSyntaxException(loc, "cannot convert pointer to float");
		} else if (oldType instanceof CEnum) {
			mExpressionTranslation.convertIntToFloat(loc, rexp, newType);
		} else if (oldType instanceof CArray) {
			throw new AssertionError("cannot convert from CArray");
		} else if (oldType instanceof CFunction) {
			throw new AssertionError("cannot convert from CFunction");
		} else if (oldType instanceof CStruct) {
			throw new UnsupportedSyntaxException(loc, "conversion from CStruct not implemented.");
		} else {
			throw new AssertionError("unknown type " + newType);
		}
	}

	private void convertToVoid(ILocation loc, ExpressionResult rexp, CPrimitive newType) {
		assert (rexp.lrVal instanceof RValue) : "has to be converted to RValue";
		final CType oldType = rexp.lrVal.getCType().getUnderlyingType();
		if (oldType instanceof CPrimitive) {
			// ok
		} else if (oldType instanceof CPointer) {
			// ok
		} else if (oldType instanceof CEnum) {
			// ok
		} else if (oldType instanceof CArray) {
			throw new AssertionError("cannot convert from CArray");
		} else if (oldType instanceof CFunction) {
			throw new AssertionError("cannot convert from CFunction");
		} else if (oldType instanceof CStruct) {
			throw new UnsupportedSyntaxException(loc, "conversion from CStruct not implemented.");
		} else {
			throw new AssertionError("unknown type " + newType);
		}
		final RValue oldRValue = (RValue) rexp.lrVal;
		final RValue resultRvalue = new RValue(oldRValue.getValue(), newType, oldRValue.isBoogieBool(),
				oldRValue.isIntFromPointer());
		rexp.lrVal = resultRvalue;
	}

	private void convertToPointer(ILocation loc, ExpressionResult rexp, CPointer newType) {
		assert (rexp.lrVal instanceof RValue) : "has to be converted to RValue";
		final CType oldType = rexp.lrVal.getCType().getUnderlyingType();
		if (oldType instanceof CPrimitive) {
			final CPrimitive cPrimitive = (CPrimitive) oldType;
			if (cPrimitive.isIntegerType()) {
				mExpressionTranslation.convertIntToPointer(loc, rexp, newType);
			} else if (cPrimitive.isRealFloatingType()) {
				throw new IncorrectSyntaxException(loc, "cannot convert float to pointer");
			} else if (cPrimitive.getType().equals(PRIMITIVE.VOID)) {
				throw new IncorrectSyntaxException(loc, "cannot convert from void");
			} else {
				throw new AssertionError("unknown type " + newType);
			}
		} else if (oldType instanceof CPointer) {
			convertPointerToPointer(loc, rexp, newType);
		} else if (oldType instanceof CEnum) {
			mExpressionTranslation.convertIntToPointer(loc, rexp, newType);
		} else if (oldType instanceof CArray) {
			throw new AssertionError("cannot convert from CArray");
		} else if (oldType instanceof CFunction) {
			throw new AssertionError("cannot convert from CFunction");
		} else if (oldType instanceof CStruct) {
			throw new UnsupportedSyntaxException(loc, "conversion from CStruct not implemented.");
		} else {
			throw new AssertionError("unknown type " + newType);
		}
	}

	private void convertPointerToPointer(ILocation loc, ExpressionResult rexp, CPointer newType) {
		// TODO: check if types are compatible
		assert (rexp.lrVal instanceof RValue) : "has to be converted to RValue";
		final RValue oldRvalue = (RValue) rexp.lrVal;
		assert oldRvalue.getCType() instanceof CPointer : "has to be pointer";
		final RValue newRvalue = new RValue(oldRvalue.getValue(), newType);
		rexp.lrVal = newRvalue;
	}

	@Override
	@Deprecated
	/*
	 * Matthias 2015-09-21: "premature optimization is the root of all evil" I think, by now we should not use this
	 * method and better live with long expressions. However, I don't want to delete this method, we might want to use
	 * it in the future.
	 */
	public BigInteger computeConstantValue(Expression value) {
		if (value instanceof IntegerLiteral) {
			return new BigInteger(((IntegerLiteral) value).getValue());
		} else if (value instanceof UnaryExpression) {
			switch (((UnaryExpression) value).getOperator()) {
			case ARITHNEGATIVE:
				return computeConstantValue(((UnaryExpression) value).getExpr()).negate();
			default:
				throw new UnsupportedOperationException("could not compute constant value");
			}
		} else if (value instanceof BinaryExpression) {
			switch (((BinaryExpression) value).getOperator()) {
			case ARITHDIV:
				return computeConstantValue(((BinaryExpression) value).getLeft())
						.divide(computeConstantValue(((BinaryExpression) value).getRight()));
			case ARITHMINUS:
				return computeConstantValue(((BinaryExpression) value).getLeft())
						.subtract(computeConstantValue(((BinaryExpression) value).getRight()));
			case ARITHMOD:
				return computeConstantValue(((BinaryExpression) value).getLeft())
						.mod(computeConstantValue(((BinaryExpression) value).getRight()));
			case ARITHMUL:
				return computeConstantValue(((BinaryExpression) value).getLeft())
						.multiply(computeConstantValue(((BinaryExpression) value).getRight()));
			case ARITHPLUS:
				return computeConstantValue(((BinaryExpression) value).getLeft())
						.add(computeConstantValue(((BinaryExpression) value).getRight()));
			default:
				throw new UnsupportedOperationException("could not compute constant value");
			}
		} else {
			throw new UnsupportedOperationException("could not compute constant value");
		}
	}

	@Override
	public SymbolTable getSymbolTable() {
		return mSymbolTable;
	}

	@Override
	public FunctionHandler getFunctionHandler() {
		return mFunctionHandler;
	}

	@Override
	public UNSIGNED_TREATMENT getUnsignedTreatment() {
		return mUnsignedTreatment;
	}

	@Override
	public InitializationHandler getInitHandler() {
		return mInitHandler;
	}

	public MemoryHandler getMemoryHandler() {
		return mMemoryHandler;
	}

	public AExpressionTranslation getExpressionTranslation() {
		return mExpressionTranslation;
	}
}