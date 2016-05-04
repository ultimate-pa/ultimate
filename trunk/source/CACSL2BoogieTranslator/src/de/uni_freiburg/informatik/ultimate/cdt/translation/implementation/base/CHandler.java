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

import org.apache.log4j.Logger;
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
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.CodeAnnot;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Contract;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.GlobalLTLInvariant;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopAnnot;
import de.uni_freiburg.informatik.ultimate.model.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.model.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BreakStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.CACSL2BoogieBacktranslator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.LTLExpressionExtractor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.POINTER_CHECKMODE;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.POINTER_INTEGER_CONVERSION;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.UNSIGNED_TREATMENT;
import de.uni_freiburg.informatik.ultimate.result.Check;
import de.uni_freiburg.informatik.ultimate.result.Check.Spec;
import de.uni_freiburg.informatik.ultimate.result.LTLPropertyCheck;
import de.uni_freiburg.informatik.ultimate.result.LTLPropertyCheck.CheckableExpression;

/**
 * Class that handles translation of C nodes to Boogie nodes.
 * 
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @author Matthias Heizmann
 * @date 01.02.2012
 */
public class CHandler implements ICHandler {
	
	/**
	 * If set to true we say Unsupported Syntax if there is some cast of
	 * pointers.
	 * Right now we are unable to handle casts of pointers soundly. However
	 * these soundness errors occur seldom.
	 */
	private final static boolean s_PointerCastIsUnsupportedSyntax = false;

	//the CHandler knows all its different Handlers..
	protected ArrayHandler mArrayHandler;
	
	protected FunctionHandler mFunctionHandler;
	
	protected StructHandler mStructHandler;
	
	public MemoryHandler mMemoryHandler;
	
	protected PostProcessor mPostProcessor;

	protected final ITypeHandler mTypeHandler;
	protected final INameHandler mNameHandler;
	
	public InitializationHandler mInitHandler;

	/**
	 * Holds the next ACSL node in the decorator tree.
	 */
	private NextACSL mAcsl;
	/**
	 * Contract for next procedure
	 */
	protected List<ACSLNode> mContract;
	/**
	 * The symbol table for the translation.
	 */
	protected SymbolTable mSymbolTable;

	/**
	 * A set holding declarations of global variables required for variables,
	 * declared locally in C but required to be global in Boogie. e.g. constants
	 * for enums (in boogie constants may only be defined globally)
	 * or local static variables. Each declaration can have a set of
	 * initialization statements. So the procedure is: typeDeclarations: added
	 * to this map in IASTSimpleDeclaration, declared using this map in
	 * ITranslationUnit static variables: added to this map in
	 * IASTSimpleDeclaration, declared using this map in ITranslationUnit,
	 * initialized using this map in PostProcessor.createInit..() global
	 * variables: added to this map in IASTTranslationUnit, declared using this
	 * map in ITranslationUnit, initialized using this map in
	 * PostProcessor.createInit..()
	 */
	protected LinkedHashMap<Declaration, CDeclaration> mDeclarationsGlobalInBoogie;

	/**
	 * A collection of axioms generated during translation process.
	 */
	protected LinkedHashSet<Axiom> mAxioms;

	/**
	 * Translation from Boogie to C for traces and expressions.
	 */
	protected final CACSL2BoogieBacktranslator mBacktranslator;

	/**
	 * If set to true and the program contains an error label ULTIMATE shows a
	 * warning that suggests a different translation mode.
	 */
	protected final boolean mErrorLabelWarning;
	private LinkedHashSet<String> mBoogieIdsOfHeapVars;

	/**
	 * This is a stack containing the types of the things declared
	 * IASTDeclarator nodes. The last element on the stack corresponds to the
	 * type of the current (inner) declarator node. There may be several types
	 * on this stack if the declarators are nested, as in
	 * 
	 * <pre>
	 * int *(*a(int))[3]
	 * </pre>
	 * 
	 * which declares a function returning a pointer to an array of length three
	 * containing int pointers. There are three nested declarators: A
	 * PointerDeclarator contains an ArrayDeclarator contains a Pointer contains
	 * a function.
	 */
	protected ArrayDeque<TypesResult> mCurrentDeclaredTypes;

	/**
	 * Stores the labels of the loops we are currently inside. (For translation
	 * of a possible continue statement)
	 */
	Stack<String> mInnerMostLoopLabel;
	private Logger mLogger;
	
	CACSLPreferenceInitializer.UNSIGNED_TREATMENT mUnsignedTreatment;

	private ArrayList<LTLExpressionExtractor> mGlobAcslExtractors;

	protected final AExpressionTranslation m_ExpressionTranslation;

	protected final TypeSizeAndOffsetComputer mTypeSizeComputer;

	public AExpressionTranslation getExpressionTranslation() {
		return m_ExpressionTranslation;
	}

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
			Logger logger, ITypeHandler typeHandler, boolean bitvectorTranslation, 
			boolean overapproximateFloatingPointOperations, INameHandler nameHandler) {

		mLogger = logger;
		this.mTypeHandler = typeHandler;
		this.mNameHandler = nameHandler;

		
		this.mUnsignedTreatment = main.mPreferences.getEnum(CACSLPreferenceInitializer.LABEL_UNSIGNED_TREATMENT, 
				CACSLPreferenceInitializer.UNSIGNED_TREATMENT.class);

		this.mArrayHandler = new ArrayHandler();
		boolean checkPointerValidity = main.mPreferences.getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_POINTER_VALIDITY);
		
		this.mSymbolTable = new SymbolTable(main);
		
		this.mDeclarationsGlobalInBoogie = new LinkedHashMap<Declaration, CDeclaration>();
		this.mAxioms = new LinkedHashSet<Axiom>();
		this.mBacktranslator = backtranslator;
		this.mContract = new ArrayList<ACSLNode>();
		this.mErrorLabelWarning = errorLabelWarning;
		this.mInnerMostLoopLabel = new Stack<String>();

		this.mBoogieIdsOfHeapVars = new LinkedHashSet<String>();
		this.mCurrentDeclaredTypes = new ArrayDeque<TypesResult>();
		
		this.mGlobAcslExtractors = new ArrayList<>();
		
		POINTER_INTEGER_CONVERSION pointerIntegerConversion = main.mPreferences.getEnum(CACSLPreferenceInitializer.LABEL_POINTER_INTEGER_CONVERSION, 
				CACSLPreferenceInitializer.POINTER_INTEGER_CONVERSION.class);
		if (bitvectorTranslation) {
			m_ExpressionTranslation = new BitvectorTranslation(main.getTypeSizes(), 
					typeHandler, pointerIntegerConversion, overapproximateFloatingPointOperations);
		} else {
			boolean inRange = main.mPreferences.getBoolean(CACSLPreferenceInitializer.LABEL_ASSUME_NONDET_VALUES_IN_RANGE);
			m_ExpressionTranslation = new IntegerTranslation(main.getTypeSizes(), typeHandler, mUnsignedTreatment, inRange, pointerIntegerConversion);
		}
		this.mPostProcessor = new PostProcessor(main, mLogger, m_ExpressionTranslation);
		this.mTypeSizeComputer = new TypeSizeAndOffsetComputer((TypeHandler) mTypeHandler, m_ExpressionTranslation, main.getTypeSizes());
		this.mFunctionHandler = new FunctionHandler(m_ExpressionTranslation, mTypeSizeComputer);
		boolean smtBoolArraysWorkaround = main.mPreferences.getBoolean(CACSLPreferenceInitializer.LABEL_SMT_BOOL_ARRAYS_WORKAROUND);
		this.mMemoryHandler = new MemoryHandler(typeHandler, mFunctionHandler, checkPointerValidity, 
				mTypeSizeComputer, main.getTypeSizes(), m_ExpressionTranslation, bitvectorTranslation, 
				nameHandler, smtBoolArraysWorkaround);
		this.mStructHandler = new StructHandler(mMemoryHandler, mTypeSizeComputer, m_ExpressionTranslation);
		this.mInitHandler = new InitializationHandler(mFunctionHandler, mStructHandler, mMemoryHandler, m_ExpressionTranslation);
	}

	@Override
	public Result visit(Dispatcher main, IASTNode node) {
		String msg = "CHandler: Not yet implemented: \"" + node.getRawSignature() + "\" (Type: "
				+ node.getClass().getName() + ")";
		ILocation loc = LocationFactory.createCLocation(node);
		throw new UnsupportedSyntaxException(loc, msg);
	}

	@Override
	public Result visit(Dispatcher main, IASTASMDeclaration node) {
		String msg = "CHandler: Not yet implemented: \"" + node.getRawSignature() + "\" (Type: "
				+ node.getClass().getName() + ")";
		throw new UnsupportedSyntaxException(LocationFactory.createCLocation(node), msg);
	}
	

	/**
	 * @deprecated is not supported in this handler! Do not use!
	 */
	@Override
	public Result visit(Dispatcher main, ACSLNode node) {
		throw new UnsupportedOperationException("Implementation Error: Use ACSLHandler for: " + node.getClass());
	}

	@Override
	public Result visit(Dispatcher main, IASTTranslationUnit node) {

		for (IASTPreprocessorStatement preS : node.getAllPreprocessorStatements()) {
			Result r = main.dispatch(preS);
			if (!(r instanceof SkipResult)) {
				throw new UnsupportedOperationException("Not yet implemented " + preS.toString());
			}
		}
		ILocation loc = LocationFactory.createCLocation(node);
		try {
			mAcsl = main.nextACSLStatement();
		} catch (ParseException e1) {
			String msg = "Skipped a ACSL node due to: " + e1.getMessage();
			main.unsupportedSyntax(loc, msg);
		}
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		
		if (!((TypeHandler) mTypeHandler).useIntForAllIntegerTypes()) {
			decl.addAll(PostProcessor.declarePrimitiveDataTypeSynonyms(loc, main.getTypeSizes(), (TypeHandler) mTypeHandler));
			
			if (((TypeHandler) mTypeHandler).areFloatingTypesNeeded()) {
				decl.addAll(PostProcessor.declareFloatDataTypes(loc, main.getTypeSizes(), (TypeHandler) mTypeHandler));
			}
			
		}

		// TODO(thrax): Check if decl should be passed as null or not.
		checkForACSL(main, null, decl, node, null);
		
		// delayed processing of IASTFunctionDefinitions and structs
		// This is a workaround. Invariants my use global variables that
		// are not yet declared.
		// Better solution: obtain function signature in a first pass
		// process function body in a second pass
		final List<IASTNode> complexNodes = new ArrayList<>();
		for (IASTNode child : node.getChildren()) {
			String raw = child.getRawSignature();
			if (child instanceof IASTSimpleDeclaration) {
				IASTSimpleDeclaration simpleDecl = (IASTSimpleDeclaration) child;
				if (simpleDecl.getDeclSpecifier() instanceof IASTElaboratedTypeSpecifier
						|| simpleDecl.getDeclSpecifier() instanceof ICASTCompositeTypeSpecifier
						|| (simpleDecl.getDeclarators().length > 0 && simpleDecl.getDeclarators()[0] instanceof CASTFunctionDeclarator)
						|| simpleDecl.getDeclSpecifier() instanceof IASTNamedTypeSpecifier) {
					complexNodes.add(child);
				} else {
					processTUchild(main, decl, child);
				}
			} else if (child instanceof IASTFunctionDefinition) {
				complexNodes.add((IASTFunctionDefinition) child);
			} else {
				processTUchild(main, decl, child);
			}
		}
		for (IASTNode funcDef : complexNodes) {
			processTUchild(main, decl, funcDef);
		}

		//(alex:) new function pointers
		final BigInteger functionPointerPointerBaseValue = BigInteger.valueOf(-1);
		for (Entry<String, Integer> en : ((Dispatcher) main).getFunctionToIndex().entrySet()) {
			String funcId = SFO.FUNCTION_ADDRESS + en.getKey();
			VarList varList = new VarList(loc, new String[]{ funcId }, mTypeHandler.constructPointerType(loc));
			decl.add(new ConstDeclaration(loc, new Attribute[0], false, varList, null, false));//would unique make sense here?? -- would potentially add lots of axioms
			BigInteger offsetValue = BigInteger.valueOf(en.getValue());
			decl.add(new Axiom(loc, new Attribute[0], ExpressionFactory.newBinaryExpression(loc, 
					BinaryExpression.Operator.COMPEQ, 
					new IdentifierExpression(loc, funcId),
					m_ExpressionTranslation.constructPointerForIntegerValues(loc, functionPointerPointerBaseValue, offsetValue))));
		}

		for (Declaration d : mDeclarationsGlobalInBoogie.keySet()) {
			assert d instanceof ConstDeclaration || d instanceof VariableDeclaration || d instanceof TypeDeclaration;
			decl.add(d);
		}
		decl.addAll(mAxioms);
		String undeclaredFunction = mFunctionHandler.isEveryCalledProcedureDeclared();
		if (undeclaredFunction != null) {
			String msg = "Following method was called but never declared! " + undeclaredFunction;
			throw new IncorrectSyntaxException(loc, msg);
		}


		decl.addAll(0, mPostProcessor.postProcess(main, loc, mMemoryHandler, mArrayHandler, mFunctionHandler, mStructHandler, (TypeHandler) mTypeHandler,
				mTypeHandler.getUndefinedTypes(), mDeclarationsGlobalInBoogie, m_ExpressionTranslation));

		// this has to happen after postprocessing as pping may add sizeof
		// constants for initializations
		decl.addAll(mTypeSizeComputer.getConstants());
		decl.addAll(mTypeSizeComputer.getAxioms());
		decl.addAll(mMemoryHandler.declareMemoryModelInfrastructure(main, loc));
		
		// add type declarations introduced by the translation, e.g., $Pointer$
		decl.addAll(((TypeHandler) mTypeHandler).constructTranslationDefiniedDelarations(loc, m_ExpressionTranslation));

		//have to block this in prerun, because there, Memorymodel is not declared which may make probelms with the callgraph computation
		if (!(main instanceof PRDispatcher)) {
			// handle proc. declaration & resolve their transitive modified globals
			decl.addAll(mFunctionHandler.calculateTransitiveModifiesClause(main, mMemoryHandler));
		}

		Collection<FunctionDeclaration> declaredFunctions = 
				m_ExpressionTranslation.getFunctionDeclarations().getDeclaredFunctions().values();
		decl.addAll(declaredFunctions);
		
		//handle global ACSL stuff
		//TODO: do it!
		
		// TODO(thrax): Check if decl should be passed as null.
		checkForACSL(main, null, decl, node, null);

		//the overall translation result:
	    Unit boogieUnit = new Unit(loc, decl.toArray(new Declaration[0]));
		
	    //annotate the Unit with LTLPropertyChecks if applicable
		for (LTLExpressionExtractor ex : mGlobAcslExtractors) {
			Map<String, LTLPropertyCheck.CheckableExpression> checkableAtomicPropositions = new LinkedHashMap<String, LTLPropertyCheck.CheckableExpression>();

			for (Entry<String, de.uni_freiburg.informatik.ultimate.model.acsl.ast.Expression> en : ex.getAP2SubExpressionMap().entrySet()) {
				ExpressionResult r = (ExpressionResult) main.dispatch(en.getValue());
				//TODO: some switchToRValue and handling of sideeffects?
				checkableAtomicPropositions.put(en.getKey(), new CheckableExpression(r.lrVal.getValue(), null));
			}
			LTLPropertyCheck propCheck = new LTLPropertyCheck(ex.getLTLFormatString(), checkableAtomicPropositions, null);
			propCheck.annotate(boogieUnit);
		}
		
		return new Result(boogieUnit);
	}

	private void processTUchild(Dispatcher main, ArrayList<Declaration> decl, IASTNode child) {
		checkForACSL(main, null, decl, child, null);
		Result childRes = main.dispatch(child);

		if (childRes instanceof DeclarationResult) {
			// we have to add a global variable
			DeclarationResult rd = (DeclarationResult) childRes;
			for (CDeclaration cd : rd.getDeclarations()) {
				mDeclarationsGlobalInBoogie.put(mSymbolTable.getBoogieDeclOfCDecl(cd), cd);
			}
		} else {
			if (childRes instanceof SkipResult)
				return;
			assert childRes.getClass() == Result.class;
			assert childRes.node != null;
			decl.add((Declaration) childRes.node);
		}
	}

	@Override
	public Result visit(Dispatcher main, IASTFunctionDefinition node) {
		LinkedHashSet<IASTDeclaration> reachableDecs = ((Dispatcher) main).getReachableDeclarationsOrDeclarators();
		if (reachableDecs != null) {
			if (!reachableDecs.contains(node))
				return new SkipResult();
		}

		TypesResult resType = (TypesResult) main.dispatch(node.getDeclSpecifier());

		mCurrentDeclaredTypes.push(resType);
		DeclaratorResult declResult = (DeclaratorResult) main.dispatch(node.getDeclarator());
		mCurrentDeclaredTypes.pop();
		return mFunctionHandler.handleFunctionDefinition(main, mMemoryHandler, node, declResult.getDeclaration(),
				mContract);
	}

	@Override
	public Result visit(Dispatcher main, IASTCompoundStatement node) {
		ILocation loc = LocationFactory.createCLocation(node);
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		ArrayList<Statement> stmt = new ArrayList<Statement>();
		LRValue expr = null;
		IASTNode parent = node.getParent();

		if (isNewScopeRequired(parent)) {
			this.beginScope();
		}

		for (IASTNode child : node.getChildren()) {
			String raw = child.getRawSignature();
			checkForACSL(main, stmt, decl, child, null);
			Result r = main.dispatch(child);
			if (r instanceof ExpressionResult) {
				ExpressionResult res = (ExpressionResult) r;
				// assert (res.auxVars.isEmpty()) : "unhavoced auxvars";
				decl.addAll(res.decl);
				stmt.addAll(res.stmt);
				expr = res.lrVal;
			} else if (r instanceof CompoundStatementExpressionResult) {
				CompoundStatementExpressionResult res = (CompoundStatementExpressionResult) r;
				decl.addAll(res.decl);
				stmt.addAll(res.stmt);
				expr = res.lrVal;
			} else if (r.node != null && r.node instanceof Body) {
				assert false : "should not happen, as CompoundStatement now yields an "
						+ "ExpressionResult or a CompoundStatementExpressionResult";
				// already have a unique naming for variables! --> unfold
				Body b = ((Body) r.node);
				decl.addAll(Arrays.asList(b.getLocalVars()));
				stmt.addAll(Arrays.asList(b.getBlock()));
			} else if (r instanceof SkipResult) {
				//skip
			} else {
				assert false : "should not happen, as CompoundStatement now yields an "
						+ "ExpressionResult or a CompoundStatementExpressionResult";
			}
		}
		checkForACSL(main, stmt, decl, null, node);
		if (isNewScopeRequired(parent)) {
			stmt = updateStmtsAndDeclsAtScopeEnd(main, decl, stmt);

			this.endScope();
		}
//		return new Result(new Body(loc, decl.toArray(new VariableDeclaration[0]), stmt.toArray(new Statement[0])));
		return new CompoundStatementExpressionResult(stmt, expr, decl, new HashMap<VariableDeclaration, ILocation>(),
				new ArrayList<Overapprox>());
	}

	/**
	 * At the end of a scope, typically a C compound statement, we need to insert some mallocs and frees surrounding
	 * the stmt block, and we need to insert all the declarations that are needed for that block, according to the symbol table.
	 * (at the dispatch of a simple declaration, the declarations are stored in the symbol table)
	 */
	public ArrayList<Statement> updateStmtsAndDeclsAtScopeEnd(Dispatcher main, ArrayList<Declaration> decl,
			ArrayList<Statement> stmt) {
		stmt = mMemoryHandler.insertMallocs(main, stmt);
		for (SymbolTableValue stv : mSymbolTable.currentScopeValues()) {
			// there may be a null declaration in case of foo(void) -- therefore we need to check the second conjunct
			// (case where this is called from FunctionHandler.handleFunctionDefinition)
			if (!stv.isBoogieGlobalVar() && stv.getBoogieDecl() != null) {
				decl.add(stv.getBoogieDecl());
			}
		}
		return stmt;
	}

	/**
	 * Visit the SimpleDeclaration (which may be quite complex in fact..). The
	 * return value here may have different uses: - for global variables and
	 * declarations inside of struct definitions, it is a ResultDeclaration
	 * (containing the Boogie Declaration of the variable) - for local variables
	 * that have an initializer, a ResultExpression is returned which contains
	 * (Boogie) statements and declarations that make the initialization
	 * according to the initializer for local variables without an initializer,
	 * a havoc statement is inserted into the ResultExpression instead The
	 * declarations themselves of the local variables (and f.i. typedefs) are
	 * stored in the symbolTable and inserted into the Boogie code at the next
	 * endScope() Declarations of static variables are added to
	 * mDeclarationsGlobalInBoogie such that they can be declared and
	 * initialized globally. Variables/types that are global in Boogie but not
	 * in C are stored in the Symboltable to keep the association of BoogieId
	 * and CId.
	 */
	@Override
	public Result visit(Dispatcher main, IASTSimpleDeclaration node) {
		LinkedHashSet<IASTDeclaration> reachableDecs = ((Dispatcher) main).getReachableDeclarationsOrDeclarators();
		if (reachableDecs != null) {
			if (node.getParent() instanceof IASTTranslationUnit) {
				if (!reachableDecs.contains(node)) {
					boolean skip = true;
					for (IASTDeclarator d : node.getDeclarators())
						if (reachableDecs.contains(d))
							skip = false;
					if (reachableDecs.contains(node.getDeclSpecifier()))
						skip = false;
					if (skip)
						return new SkipResult();
				}
			}
		}

		ILocation loc = LocationFactory.createCLocation(node);
		if (node.getDeclSpecifier() == null) {
			String msg = "This statement can be removed!";
			main.warn(loc, msg);
			return new SkipResult();
		}

		// enum case
		if (node.getDeclSpecifier() instanceof IASTEnumerationSpecifier) {
			handleEnumDeclaration(main, node);
		}

		Result r = main.dispatch(node.getDeclSpecifier());
		assert r instanceof SkipResult || r instanceof TypesResult;
		if (r instanceof SkipResult)
			return r;
		if (r instanceof TypesResult) {
			TypesResult resType = (TypesResult) r;
			Result result = new SkipResult(); // Skip will be overwritten in
												// case of a global or a local
												// initialized variable

			CStorageClass storageClass = scConstant2StorageClass(node.getDeclSpecifier().getStorageClass());

			mCurrentDeclaredTypes.push(resType);
			/**
			 * Christian: C allows several declarations of "similar" types in
			 * one go. For instance: <code>int a, b[2];</code> Here
			 * <code>a</code> has type <code>int</code> and <code>b</code> has
			 * type <code>int[]</code>. To solve this, the declaration items are
			 * visited one after another.
			 */
			for (IASTDeclarator d : node.getDeclarators()) {
//				if (d instanceof IASTFieldDeclarator)
//					throw new UnsupportedSyntaxException(loc, "bitfields are not supported at the moment");
	
				DeclaratorResult declResult = (DeclaratorResult) main.dispatch(d);

				CDeclaration cDec = declResult.getDeclaration();
				cDec.setStorageClass(storageClass);
				
				
				// are we in prerun mode?
				if (main instanceof PRDispatcher) {
					// all unions should be on heap
					if (cDec.getType() instanceof CUnion 
							&& storageClass != CStorageClass.TYPEDEF) {
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
					mFunctionHandler.handleFunctionDeclarator(main, LocationFactory.createCLocation(d), mContract, cDec);
					continue;
				}
				
				// if the same variable is declared multiple times (within the same scope), we only keep one declaration
				// if one of them has an initializer, we keep that one.
				// if we are inside a struct declaration however, this does not apply, we proceed as normal, as the result
				// is needed to build the struct type
				if (!mTypeHandler.isStructDeclaration() && mSymbolTable.existsInCurrentScope(cDec.getName()) ) {
					if (cDec.hasInitializer()) {
						// undo the effects of the old declaration
						if (mFunctionHandler.noCurrentProcedure() && !mTypeHandler.isStructDeclaration()) {
							mDeclarationsGlobalInBoogie.remove(mSymbolTable.get(cDec.getName(), loc).getBoogieDecl());
						}
						//local variable may not be a problem, because symboltable will overwrite at put
						// .. or are they not allowed in C?... TODO --> should look it up in standard
						// if that is the case, then this code section may be simplified, probably..
					} else {
						// this variable has already been declared, and the current declaration does not have an initializer
						// --> skip the current declaration
						continue;
					}
				}
				
				

				boolean onHeap = cDec.isOnHeap();
				String bId = mNameHandler.getUniqueIdentifier(node, cDec.getName(),
						mSymbolTable.getCompoundCounter(), onHeap, cDec.getType());
				if (onHeap)
					mBoogieIdsOfHeapVars.add(bId);

				Declaration boogieDec = null;
				boolean globalInBoogie = false;

				// this .put() is only to have a minimal symbolTableEntry
				// (containing boogieID) for
				// translation of the initializer
				mSymbolTable.put(cDec.getName(),
						new SymbolTableValue(bId, boogieDec, cDec, globalInBoogie, d));
				cDec.translateInitializer(main);

				ASTType translatedType = null;
				if (onHeap)
					translatedType = mTypeHandler.constructPointerType(loc);
				else
					translatedType = mTypeHandler.ctype2asttype(loc, cDec.getType());

				if (storageClass == CStorageClass.TYPEDEF) {
					boogieDec = new TypeDeclaration(loc, new Attribute[0], false, bId, new String[0], translatedType);
					mTypeHandler.addDefinedType(bId, new TypesResult(new NamedType(loc, cDec.getName(), null),
							false, false, cDec.getType()));
					// TODO: add a sizeof-constant for the type??
					globalInBoogie = true;
					mDeclarationsGlobalInBoogie.put(boogieDec, cDec);
				} else if (storageClass == CStorageClass.STATIC && !mFunctionHandler.noCurrentProcedure()) {
					// we have a local static variable -> special treatment
					// global static variables are treated like normal global variables..
					boogieDec = new VariableDeclaration(loc, new Attribute[0],
							new VarList[] { new VarList(loc, new String[] {bId}, 
									translatedType) });
					globalInBoogie = true;
					mDeclarationsGlobalInBoogie.put(boogieDec, cDec);
				} else {
					/**
					 * For Variable length arrays we have a "non-real" initializer which just initializes the aux var for the array's
					 * size. We do not want to treat this like other initializers (call initVar and so).
					 */
					boolean hasRealInitializer = cDec.hasInitializer() && 
							!(cDec.getType() instanceof CArray && !(cDec.getInitializer() instanceof ExpressionListRecResult));

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

						if (result instanceof SkipResult)
							result = new ExpressionResult((LRValue) null);

						VariableLHS lhs = new VariableLHS(loc, bId);

						if (cDec.hasInitializer()) { //must be a non-real initializer for variable length array size --> need to pass this on
								((ExpressionResult) result).decl.addAll(cDec.getInitializer().decl);
								((ExpressionResult) result).stmt.addAll(cDec.getInitializer().stmt);
								((ExpressionResult) result).auxVars.putAll(cDec.getInitializer().auxVars);
						}
							
						//no initializer --> essentially needs to be havoced f.i. in each loop iteration
						if (!onHeap) {
							((ExpressionResult) result).stmt.add(
									new HavocStatement(loc, new VariableLHS[] { lhs }));
						} else {
							LocalLValue llVal = new LocalLValue(lhs, cDec.getType());
							//old solution: havoc via an auxvar, new solution (below): 
							//just malloc at the right place (much shorter for arrays and structs..)
							((ExpressionResult) result).stmt.add(mMemoryHandler.getMallocCall(main, mFunctionHandler, 
									llVal , loc));
							mMemoryHandler.addVariableToBeFreed(main, 
									new LocalLValueILocationPair(llVal, LocationFactory.createIgnoreLocation(loc)));
						}
					} else if (hasRealInitializer && !mFunctionHandler.noCurrentProcedure() && !mTypeHandler.isStructDeclaration()) { 
						//in case of a local variable declaration with an initializer, the statements and delcs
						// necessary for the initialization are the result
						assert result instanceof SkipResult || result instanceof ExpressionResult;
						VariableLHS lhs = new VariableLHS(loc, bId);
						ExpressionResult initRex = 
								mInitHandler.initVar(loc, main, 
										lhs, cDec.getType(),
										cDec.getInitializer());
						if (result instanceof SkipResult)
							result = new ExpressionResult((LRValue) null);
						
						if (onHeap) {
							LocalLValue llVal = new LocalLValue(lhs, cDec.getType());
							mMemoryHandler.addVariableToBeFreed(main, new LocalLValueILocationPair(llVal, loc));
							((ExpressionResult) result).stmt.add(mMemoryHandler.getMallocCall(main, mFunctionHandler,
									llVal, loc));
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
						if (result instanceof SkipResult)
							result = new DeclarationResult();
						((DeclarationResult) result).addDeclaration(cDec);
					}
					boogieDec = new VariableDeclaration(loc, new Attribute[0], new VarList[] { new VarList(loc,
							new String[] { bId }, translatedType) });
					globalInBoogie |= mFunctionHandler.noCurrentProcedure();
				}

				mSymbolTable.put(cDec.getName(), new SymbolTableValue(bId,
						boogieDec, cDec, globalInBoogie, d)); 
			}
			mCurrentDeclaredTypes.pop();
			
//			Matthias 19-09-2015: I commented the following. Havoc'ing here is
//			too early.			
//			if (result instanceof ExpressionResult)
//				((ExpressionResult) result).stmt.addAll(
//						createHavocsForAuxVars(((ExpressionResult) result).auxVars));
			return result;
		}
		String msg = "Unknown result type: " + r.getClass();
		throw new UnsupportedSyntaxException(loc, msg);
	}

	@Override
	public Result visit(Dispatcher main, IASTParameterDeclaration node) {
		TypesResult resType = (TypesResult) main.dispatch(node.getDeclSpecifier());

		mCurrentDeclaredTypes.push(resType);
		DeclaratorResult declResult = (DeclaratorResult) main.dispatch(node.getDeclarator());
		mCurrentDeclaredTypes.pop();
		return declResult;
	}

	@Override
	public Result visit(Dispatcher main, IASTDeclarator node) {
		ILocation loc = LocationFactory.createCLocation(node);
		TypesResult resType = mCurrentDeclaredTypes.peek();
		TypesResult newResType = new TypesResult(resType);

		newResType.isOnHeap |= main instanceof MainDispatcher 
				? ((MainDispatcher) main).getVariablesForHeap().contains(node)
						 : false; //in this case we are in the PRDispatcher

		IASTPointerOperator[] pointerOps = node.getPointerOperators();
		for (int i = 0; i < pointerOps.length; i++) {
			newResType.cType = new CPointer(newResType.cType);
		}
		ExpressionResult variableLengthArrayAuxVarInitializer = null;
		
		if (node instanceof IASTArrayDeclarator) {
			IASTArrayDeclarator arrDecl = (IASTArrayDeclarator) node;
			
			final ArrayList<RValue> size = new ArrayList<RValue>();
			// expression results of from array modifiers
			final ArrayList<ExpressionResult> expressionResults = new ArrayList<ExpressionResult>();
			
			for (IASTArrayModifier am : arrDecl.getArrayModifiers()) {
				final RValue sizeFactor;
				if (am.getConstantExpression() != null) {
					// case where we have a number between the brackets,
					// e.g., a[23] or a[n+1]
					ExpressionResult er = (ExpressionResult) main.dispatch(am.getConstantExpression());
					er = er.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
//					FIXME: 2015-10-25 Matthias: uncomment once the simplification of Boogie expressions is implemented
					m_ExpressionTranslation.convertIntToInt(loc, er, m_ExpressionTranslation.getCTypeOfPointerComponents());
					expressionResults.add(er);
					sizeFactor = (RValue) er.lrVal;
				} else if (am.getConstantExpression() == null && 
						arrDecl.getArrayModifiers()[arrDecl.getArrayModifiers().length - 1] == am) {
					//the innermost array modifier may be empty, if there is an initializer; like int a[1][2][] = {...}
					final int intSizeFactor;
					if (arrDecl.getInitializer() != null) {
						assert arrDecl.getInitializer() instanceof IASTEqualsInitializer;
						IASTEqualsInitializer eqInit = ((IASTEqualsInitializer) arrDecl.getInitializer());
						assert eqInit.getInitializerClause() instanceof IASTInitializerList;
						IASTInitializerList initList = (IASTInitializerList) eqInit.getInitializerClause();
						intSizeFactor = initList.getSize();
					} else { 
						// we have an incomplete array type without an initializer -- 
						// this may happen in a function parameter..
						intSizeFactor = -1234567;
					}
					CPrimitive ctype = m_ExpressionTranslation.getCTypeOfPointerComponents();
					Expression sizeExpression = m_ExpressionTranslation.constructLiteralForIntegerType(loc, ctype, BigInteger.valueOf(intSizeFactor));
					sizeFactor = new RValue(sizeExpression, ctype, false, false);

				} else {
					throw new IncorrectSyntaxException(loc, "wrong array type in declaration");
				}
				size.add(sizeFactor);
			}
			ExpressionResult allResults = ExpressionResult.copyStmtDeclAuxvarOverapprox(expressionResults.toArray(new ExpressionResult[expressionResults.size()]));
			if (!allResults.decl.isEmpty() || !allResults.stmt.isEmpty() || !allResults.auxVars.isEmpty()) {
				throw new AssertionError("passing these results is not yet implemented");
			}
			CArray arrayType = new CArray(size.toArray(new RValue[size.size()]), newResType.cType);
			newResType.cType = arrayType;

		} else if (node instanceof CASTFunctionDeclarator) {
			CASTFunctionDeclarator funcDecl = (CASTFunctionDeclarator) node;

			IASTParameterDeclaration[] paramDecls = funcDecl.getParameters();
			CDeclaration[] paramsParsed = new CDeclaration[paramDecls.length];
			for (int i = 0; i < paramDecls.length; i++) {
				DeclaratorResult decl = (DeclaratorResult) main.dispatch(paramDecls[i]);
				if (decl.getDeclaration().getName() == ""
						&& decl.getDeclaration().getType() instanceof CPrimitive
						&& ((CPrimitive) decl.getDeclaration().getType()).getType().equals(PRIMITIVE.VOID)) {
					assert paramDecls.length == 1;
					paramsParsed = new CDeclaration[0];
					break;
				}
				paramsParsed[i] = decl.getDeclaration();
			}
			CFunction funcType = new CFunction(newResType.cType, paramsParsed, funcDecl.takesVarArgs());
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
				CDeclaration cdec = result.getDeclaration();
				result = new DeclaratorResult(
						new CDeclaration(cdec.getType(), cdec.getName(),
						node.getInitializer(), variableLengthArrayAuxVarInitializer, cdec.isOnHeap(), CStorageClass.UNSPECIFIED));
			}
			return result;
		} else {
			DeclaratorResult result = new DeclaratorResult(
					new CDeclaration(newResType.cType, node.getName().toString(), node.getInitializer(),
							variableLengthArrayAuxVarInitializer, newResType.isOnHeap, CStorageClass.UNSPECIFIED));
			return result;
		}
	}

	@Override
	public Result visit(Dispatcher main, IASTLiteralExpression node) {
		return m_ExpressionTranslation.translateLiteral(main, node);
	}

	@Override
	public Result visit(Dispatcher main, IASTIdExpression node) {
		ILocation loc = LocationFactory.createCLocation(node);
		String cId = node.getName().toString();

		//deal with builtin constants
		if (cId.equals("NULL")) {
			return new ExpressionResult(new RValue(m_ExpressionTranslation.constructNullPointer(loc), 
					new CPointer(new CPrimitive(PRIMITIVE.VOID))));
		} else if (cId.equals("NAN") || cId.equals("INFINITY") || cId.equals("inf")) {			
			ExpressionResult result = m_ExpressionTranslation.createNanOrInfinity(loc, cId);
			return result;
		} else if (node.getName().toString().equals("__func__")){
			CType cType = new CPointer(new CPrimitive(PRIMITIVE.CHAR));
			String tId = mNameHandler.getTempVarUID(SFO.AUXVAR.NONDET, cType);
			VariableDeclaration tVarDecl = new VariableDeclaration(loc, new Attribute[0], new VarList[] { new VarList(
					loc, new String[] { tId }, mTypeHandler.constructPointerType(loc)) });
			RValue rvalue = new RValue(new IdentifierExpression(loc, tId), cType);
			ArrayList<Declaration> decls = new ArrayList<Declaration>();
			decls.add(tVarDecl);
			Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>();
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
			CFunction cFunction = mFunctionHandler.getCFunctionType(cId);
			cType = cFunction;
			bId = SFO.FUNCTION_ADDRESS + cId;
			useHeap = true;
			intFromPtr = false;
		} else if (main.getFunctionToIndex().containsKey(cId)) {
			throw new AssertionError("function not known to function handler");
		} else {
			throw new UnsupportedSyntaxException(loc, "identifier is not declared (neither a variable nor a function name): " + cId);
		}

		LRValue lrVal = null;
		if (useHeap) {
			IdentifierExpression idExp = new IdentifierExpression(loc, bId);
			//convention: the ctype in the symbol table of something that we put on the heap
			// is the same as it would be if we did not put it on heap
			lrVal = new HeapLValue(idExp, cType, intFromPtr);
		} else {
			VariableLHS idLhs = new VariableLHS(loc, bId);
			lrVal = new LocalLValue(idLhs, cType, false, intFromPtr);
		}
		return new ExpressionResult(lrVal);
	}

	@Override
	public Result visit(Dispatcher main, IASTUnaryExpression node) {
		ExpressionResult o = (ExpressionResult) main.dispatch(node.getOperand());
		ILocation loc = LocationFactory.createCLocation(node);

		// for the cases we know that it's an RValue..
		// ResultExpression rop = o.switchToRValueIfNecessary(main,
		// memoryHandler, structHandler, loc);

		CType oType = o.lrVal.getCType();
		if (oType instanceof CNamed)
			oType = ((CNamed) oType).getUnderlyingType();

		switch (node.getOperator()) {
		case IASTUnaryExpression.op_minus:
		case IASTUnaryExpression.op_not:
		case IASTUnaryExpression.op_plus:
		case IASTUnaryExpression.op_tilde: {
			ExpressionResult rop = o.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
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
			Map<VariableDeclaration, ILocation> emptyAuxVars = new LinkedHashMap<VariableDeclaration, ILocation>(0);
			return new ExpressionResult(new RValue(mMemoryHandler.calculateSizeOf(loc, oType), new CPrimitive(
					PRIMITIVE.INT)), emptyAuxVars);
		case IASTUnaryExpression.op_star: {
			return handleIndirectionOperator(main, o, loc);
		}
		case IASTUnaryExpression.op_amper: {
			return handleAddressOfOperator(main, o, loc);
		}
		case IASTUnaryExpression.op_alignOf:
		default:
			String msg = "Unknown or unsupported unary operation: " + node.getOperator();
			throw new UnsupportedSyntaxException(loc, msg);
		}
	}


	/**
	 * Handle prefix increment and decrement operators according to 
	 * Section 6.5.3.1 of C11.
	 * We translate the expression <code>++LV</code> to an auxiliary variable
	 * <code>t~pre</code> and add to the resulting {@link ExpressionResult}
	 * the two assignments <code>t~pre := LV+1</code> and 
	 * <code>LV := t~pre</code>.
	 * Hence, the auxiliary variable <code>t~pre</code> stores the new value of 
	 * the object to which the lvalue <code>LV</code> refers.
	 * 
	 * Question: Why are we doing this complicated replacement and do not replace
	 * <code>++LV</code> by <code>LV + 1</code> ?
	 * Answer: We want to be ready for dealing with cases where there are
	 * several pre/post increment/decrement operations in one expression.
	 * We might extend our implementation in a way where the 
	 * operation is done at a certain sequence point or all evaluation orders
	 * are considered.
	 */
	private Result handlePrefixIncrementAndDecrement(Dispatcher main,
			int prefixOp, ILocation loc, ExpressionResult exprRes) {
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
		final Expression valueXcremented = constructXcrementedValue(main, loc,
				result, oType, op, exprRes.lrVal.getValue());
		
		// assign the old value to the temporary variable 
		final AssignmentStatement assignStmt;
		{
			LeftHandSide[] tmpAsLhs = new LeftHandSide[] { new VariableLHS(loc, tmpName) };
			Expression[] newValue = new Expression[] { valueXcremented };
			assignStmt = new AssignmentStatement(loc, tmpAsLhs , newValue);
		}
		result.stmt.add(assignStmt);
		
		final RValue rhs = new RValue(valueXcremented, oType, false, false);
		final ExpressionResult assign = makeAssignment(loc, result.stmt, modifiedLValue, 
				rhs, result.decl, result.auxVars, result.overappr);
		
		final RValue tmpRValue = new RValue(new IdentifierExpression(loc, tmpName), oType);
		assign.lrVal = tmpRValue;
		return assign;
	}

	/**
	 * Handle postfix increment and decrement operators according to 
	 * Section 6.5.2.4 of C11.
	 * We translate the expression <code>LV++</code> to an auxiliary variable
	 * <code>t~post</code> and add to the resulting {@link ExpressionResult}
	 * the two assignments <code>t~post := LV</code> and 
	 * <code>LV := t~post + 1</code>.
	 * Hence the auxiliary variable <code>t~post</code> stores the old value of 
	 * the object to which the lvalue <code>LV</code> refers. 
	 */
	private Result handlePostfixIncrementAndDecrement(Dispatcher main,
			ILocation loc, int postfixOp, ExpressionResult exprRes) {
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
			LeftHandSide[] tmpAsLhs = new LeftHandSide[] { new VariableLHS(loc, tmpName) };
			Expression[] oldValue = new Expression[] { exprRes.lrVal.getValue() };
			assignStmt = new AssignmentStatement(loc, tmpAsLhs , oldValue);
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
		final Expression valueXcremented = constructXcrementedValue(main, loc,
				result, oType, op, tmpRValue.getValue());
		
		final RValue rhs = new RValue(valueXcremented, oType, false, false);
		final ExpressionResult assign = makeAssignment(loc, result.stmt, modifiedLValue, 
				rhs, result.decl, result.auxVars, result.overappr);
		assign.lrVal = tmpRValue;
		return assign;
	}

	/**
	 * Increment or decrement an expression.
	 * Construct expression that represents the value of the input expression
	 * but is incremented or decremented by one.
	 * If op is IASTBinaryExpression.op_plus we increment, 
	 * if op is IASTBinaryExpression.op_minus we decrement.
	 * If ctype is CPrimitive, we increment/decrement by one and also call
	 * the method that adds (depending on the settings) an overflow check.
	 * If ctype is CPointer, we increment/decrement by the size of the 
	 * pointsToType and call the method that adds (depending on the settings)
	 * an check if the pointer arithmetic was legal.
	 */
	private Expression constructXcrementedValue(Dispatcher main, ILocation loc,
			final ExpressionResult result, final CType ctype, final int op,
			final Expression value) {
		assert (op == IASTBinaryExpression.op_plus || op == IASTBinaryExpression.op_minus) : 
			"has to be either minus or plus";
		final Expression valueIncremented;
		if (ctype instanceof CPointer) {
			CPointer cPointer = (CPointer) ctype; 
			Expression oneEpr = m_ExpressionTranslation.constructLiteralForIntegerType(
					loc, m_ExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ONE);
			CPrimitive oneType = m_ExpressionTranslation.getCTypeOfPointerComponents();
			RValue one = new RValue(oneEpr, oneType);
			valueIncremented = mMemoryHandler.doPointerArithmetic(op, loc, value, one, cPointer.pointsToType);
			addOffsetInBoundsCheck(main, loc, valueIncremented, result);
		}
		else if (ctype instanceof CPrimitive) {
			CPrimitive cPrimitive = (CPrimitive) ctype;
			Expression one = m_ExpressionTranslation.constructLiteralForIntegerType(
					loc, cPrimitive, BigInteger.ONE);
			addIntegerBoundsCheck(main, loc, result, cPrimitive, op, value, one);
			valueIncremented = m_ExpressionTranslation.constructArithmeticExpression(
					loc, op, value, cPrimitive, one, cPrimitive);
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
			if (main instanceof PRDispatcher){
				// We are in the prerun mode.
				// As a workaround, we (incorrectly) return the value
				// instead of the address. But we add variables to the
				// heapVars and hence in the non-prerun mode the input
				// will be a HeapLValue instead of a LocalLValue.
				Expression expr = er.lrVal.getValue();
				if (expr instanceof IdentifierExpression) {
					IdentifierExpression idExpr = (IdentifierExpression) expr;
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
		ExpressionResult result = ExpressionResult.copyStmtDeclAuxvarOverapprox(er);
		result.lrVal = ad;
		return result;
	}
	
	/**
	 * Handle the indirection operator according to Section 6.5.3.2 of C11.
	 * (The indirection operator is the star for pointer dereference.)
	 */
	private Result handleIndirectionOperator(Dispatcher main, ExpressionResult er, ILocation loc) {
		ExpressionResult rop = er.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
		RValue rValue = (RValue) rop.lrVal;
		if (!(rValue.getCType().getUnderlyingType() instanceof CPointer)) {
			throw new IllegalArgumentException("dereference needs pointer but got " + rValue.getCType());
		}
		CPointer pointer = (CPointer) rValue.getCType().getUnderlyingType();
		CType pointedType = pointer.pointsToType;
		if (pointedType.isIncomplete())
			throw new IncorrectSyntaxException(loc, "Pointer dereference of incomplete type");

		return new ExpressionResult(rop.stmt, new HeapLValue(rValue.getValue(), pointedType),
				rop.decl, rop.auxVars, rop.overappr);
	}
	
	/**
	 * Handle unary arithmetic operators according to Section 6.5.3.3 of C11.
	 * Assumes that left (resp. right) are the results from handling the operands.
	 * Requires that the {@link LRValue} of operands is an {@link RValue}
	 * (i.e., switchToRValueIfNecessary was applied if needed).
	 */
	ExpressionResult handleUnaryArithmeticOperators(Dispatcher main, ILocation loc,
			int op, ExpressionResult operand) {
		assert (operand.lrVal instanceof RValue) : "no RValue";
		CType inputType = operand.lrVal.getCType().getUnderlyingType();

		switch (op) {
		case IASTUnaryExpression.op_not: {
			if (!inputType.isScalarType()) {
				throw new IllegalArgumentException("scalar type required");
			}
			final Expression negated;
			if (operand.lrVal.isBoogieBool()) {
				// in Boogie already represented by bool, we only negate
				negated = ExpressionFactory.newUnaryExpression(loc, UnaryExpression.Operator.LOGICNEG, operand.lrVal.getValue());
			} else {
				final Expression rhsOfComparison; 
						if (inputType instanceof CPointer) {
							rhsOfComparison = m_ExpressionTranslation.constructNullPointer(loc);
						} else if (inputType instanceof CEnum) {
							CPrimitive intType = new CPrimitive(PRIMITIVE.INT);
							rhsOfComparison = m_ExpressionTranslation.constructLiteralForIntegerType(
									loc, intType, BigInteger.ZERO);
						} else if (inputType instanceof CPrimitive) {
							CPrimitive inputPrimitive = (CPrimitive) inputType; 
							if (inputPrimitive.getGeneralType() == GENERALPRIMITIVE.INTTYPE) {
								rhsOfComparison = m_ExpressionTranslation.constructLiteralForIntegerType(
										loc, inputPrimitive, BigInteger.ZERO);
							} else if (inputPrimitive.getGeneralType() == GENERALPRIMITIVE.FLOATTYPE) {
								rhsOfComparison = m_ExpressionTranslation.constructLiteralForFloatingType(
										loc, inputPrimitive, BigInteger.ZERO);
							} else {
								throw new AssertionError("illegal case");
							}
						} else {
							throw new AssertionError("illegal case");
						}
				 negated = m_ExpressionTranslation.constructBinaryEqualityExpression(loc, 
						 IASTBinaryExpression.op_equals, operand.lrVal.getValue(), inputType, rhsOfComparison, inputType); 
						 
			}
			ExpressionResult result = ExpressionResult.copyStmtDeclAuxvarOverapprox(operand);
			// C11 6.5.3.3.5 The result has type int.
			CPrimitive resultType = new CPrimitive(PRIMITIVE.INT);
			// type of Operator.COMPEQ expression is bool
			boolean isBoogieBool = true;
			RValue rval = new RValue(negated, resultType, isBoogieBool);
			result.lrVal = rval;
			return result;
		}
		case IASTUnaryExpression.op_plus: {
			if (!inputType.isArithmeticType()) {
				throw new UnsupportedOperationException("arithmetic type required");
			}
			if (inputType.isArithmeticType()) {
				operand.rexBoolToIntIfNecessary(loc, m_ExpressionTranslation);
				m_ExpressionTranslation.doIntegerPromotion(loc, operand);
			}
			return operand;
		}
		case IASTUnaryExpression.op_minus:
		case IASTUnaryExpression.op_tilde:
			if (!inputType.isArithmeticType()) {
				throw new UnsupportedOperationException("arithmetic type required");
			}
			operand.rexBoolToIntIfNecessary(loc, m_ExpressionTranslation);
			m_ExpressionTranslation.doIntegerPromotion(loc, operand);
			CPrimitive resultType = (CPrimitive) operand.lrVal.getCType();
			ExpressionResult result = ExpressionResult.copyStmtDeclAuxvarOverapprox(operand);
			if (op == IASTUnaryExpression.op_minus && resultType.isIntegerType()) {
				addIntegerBoundsCheck(main, loc, result, resultType, op,  operand.lrVal.getValue());
			}
			Expression bwexpr = m_ExpressionTranslation.constructUnaryExpression(loc, 
					op, operand.lrVal.getValue(), resultType) ;
			RValue rval = new RValue(bwexpr, resultType, false);
			result.lrVal = rval;
			return result;
		default:
			throw new IllegalArgumentException("not a unary arithmetic operator " + op);
		}
	}
	
	
	

	@Override
	public Result visit(Dispatcher main, IASTBinaryExpression node) {
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		ArrayList<Statement> stmt = new ArrayList<Statement>();
		Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>();
		ILocation loc = LocationFactory.createCLocation(node);
		List<Overapprox> overappr = new ArrayList<Overapprox>();

		ExpressionResult l = (ExpressionResult) main.dispatch(node.getOperand1());
		ExpressionResult r = (ExpressionResult) main.dispatch(node.getOperand2());

		ExpressionResult rl = l.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
		ExpressionResult rr = r.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);

		CType lType = l.lrVal.getCType().getUnderlyingType();
		CType rType = r.lrVal.getCType().getUnderlyingType();

		switch (node.getOperator()) {
		case IASTBinaryExpression.op_assign: {
			stmt.addAll(l.stmt);
			decl.addAll(l.decl);
			auxVars.putAll(l.auxVars);
			overappr.addAll(l.overappr);
			
			if (lType instanceof CPointer && rType instanceof CArray) {
				//array must be on heap --> just take the address

				stmt.addAll(r.stmt);
				decl.addAll(r.decl);
				auxVars.putAll(r.auxVars);
				overappr.addAll(r.overappr);
				
				RValue address = null;
				if (r.lrVal instanceof HeapLValue)
					address = new RValue(((HeapLValue) r.lrVal).getAddress(), new CPointer(((CArray) rType).getValueType()));
				else
					address = new RValue(r.lrVal.getValue(), new CPointer(((CArray) rType).getValueType()));
				return makeAssignment(loc, stmt, l.lrVal, address, decl, auxVars, overappr);
			} else {
				stmt.addAll(rr.stmt);
				decl.addAll(rr.decl);
				auxVars.putAll(rr.auxVars);
				overappr.addAll(rr.overappr);
				rr.rexBoolToIntIfNecessary(loc, m_ExpressionTranslation);
				return makeAssignment(loc, stmt, l.lrVal, (RValue) rr.lrVal, decl, auxVars, overappr, l.unionFieldIdToCType);
			}
		}
		case IASTBinaryExpression.op_equals:
		case IASTBinaryExpression.op_notequals: {
			rr.rexBoolToIntIfNecessary(loc, m_ExpressionTranslation);
			rl.rexBoolToIntIfNecessary(loc, m_ExpressionTranslation);
			return handleEqualityOperators(main, loc, node.getOperator(), rl, rr);
		}
		case IASTBinaryExpression.op_greaterEqual:
		case IASTBinaryExpression.op_greaterThan:
		case IASTBinaryExpression.op_lessEqual:
		case IASTBinaryExpression.op_lessThan: {
			return handleRelationalOperators(main, loc, node.getOperator(), rl, rr);
		}

		case IASTBinaryExpression.op_logicalAnd: {
			rl.rexIntToBoolIfNecessary(loc, m_ExpressionTranslation, mMemoryHandler);
			rr.rexIntToBoolIfNecessary(loc, m_ExpressionTranslation, mMemoryHandler);
			

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
				RValue newRVal = new RValue(ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND,
						rl.lrVal.getValue(), rr.lrVal.getValue()),
						new CPrimitive(CPrimitive.PRIMITIVE.INT), true);

				return new ExpressionResult(stmt, newRVal, decl, auxVars, overappr);
			}
			// create and add tmp var #t~AND~UID
			CPrimitive intType = new CPrimitive(PRIMITIVE.INT);
			String resName = mNameHandler.getTempVarUID(SFO.AUXVAR.SHORTCIRCUIT, intType);
			VarList tempVar = new VarList(loc, new String[] { resName }, new PrimitiveType(loc, SFO.BOOL));
			VariableDeclaration tmpVar = new VariableDeclaration(loc, new Attribute[0], new VarList[] { tempVar });
			auxVars.put(tmpVar, loc);
			decl.add(tmpVar);
			VariableLHS lhs = new VariableLHS(loc, resName);
			RValue tmpRval = new RValue(new IdentifierExpression(loc, resName), intType, true);
			RValue resRval = tmpRval;
			// #t~AND~UID = left

			AssignmentStatement aStat = new AssignmentStatement(loc, new LeftHandSide[] { lhs },
					new Expression[] { rl.lrVal.getValue() });
			Map<String, IAnnotations> annots = aStat.getPayload().getAnnotations();
			for (Overapprox overapprItem : overappr) {
				annots.put(Overapprox.getIdentifier(), overapprItem);
			}
			stmt.add(aStat);
			// if (#t~AND~UID) {#t~AND~UID = right;}
			ArrayList<Statement> outerThenPart = new ArrayList<Statement>();
			outerThenPart.addAll(rr.stmt);

			outerThenPart.add(new AssignmentStatement(loc, new LeftHandSide[] { lhs },
					new Expression[] { rr.lrVal.getValue() }));
			IfStatement ifStatement = new IfStatement(loc, tmpRval.getValue(), outerThenPart.toArray(new Statement[0]),
					new Statement[0]);
			annots = ifStatement.getPayload().getAnnotations();
//			for (Overapprox overapprItem : overappr) {
//				annots.put(Overapprox.getIdentifier(), overapprItem);
//			}
			stmt.add(ifStatement);
			return new ExpressionResult(stmt, resRval, decl, auxVars, overappr);
		}
		case IASTBinaryExpression.op_logicalOr: {
			rl.rexIntToBoolIfNecessary(loc, m_ExpressionTranslation, mMemoryHandler);
			rr.rexIntToBoolIfNecessary(loc, m_ExpressionTranslation, mMemoryHandler);

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
				return new ExpressionResult(stmt, new RValue(ExpressionFactory.newBinaryExpression(loc,
						BinaryExpression.Operator.LOGICOR, rl.lrVal.getValue(), rr.lrVal.getValue()),
						new CPrimitive(CPrimitive.PRIMITIVE.INT), true), decl, auxVars, overappr);
			}
			// create and add tmp var #t~OR~UID
			CPrimitive intType = new CPrimitive(PRIMITIVE.INT);
			String resName = mNameHandler.getTempVarUID(SFO.AUXVAR.SHORTCIRCUIT, intType);
			VarList tempVar = new VarList(loc, new String[] { resName }, new PrimitiveType(loc, SFO.BOOL));
			VariableDeclaration tmpVar = new VariableDeclaration(loc, new Attribute[0], new VarList[] { tempVar });
			auxVars.put(tmpVar, loc);
			decl.add(tmpVar);
			VariableLHS lhs = new VariableLHS(loc, resName);
			RValue tmpRval = new RValue(new IdentifierExpression(loc, resName), intType, true);
			RValue resRval = tmpRval;
			// #t~OR~UID = left
			AssignmentStatement aStat = new AssignmentStatement(loc, new LeftHandSide[] { lhs },
					new Expression[] { rl.lrVal.getValue() });
			Map<String, IAnnotations> annots = aStat.getPayload().getAnnotations();
			for (Overapprox overapproxItem : overappr) {
				annots.put(Overapprox.getIdentifier(), overapproxItem);
			}
			stmt.add(aStat);
			// if (#t~OR~UID) {} else {#t~OR~UID = right;}
			ArrayList<Statement> outerElsePart = new ArrayList<Statement>();
			outerElsePart.addAll(rr.stmt);

			outerElsePart.add(new AssignmentStatement(loc, new LeftHandSide[] { lhs },
					new Expression[] { rr.lrVal.getValue() }));
			IfStatement ifStatement = new IfStatement(loc, tmpRval.getValue(), new Statement[0],
					outerElsePart.toArray(new Statement[0]));
			annots = ifStatement.getPayload().getAnnotations();
			for (Overapprox overapprItem : overappr) {
				annots.put(Overapprox.getIdentifier(), overapprItem);
			}
			stmt.add(ifStatement);
			return new ExpressionResult(stmt, resRval, decl, auxVars, overappr);
		}
		case IASTBinaryExpression.op_modulo:
		case IASTBinaryExpression.op_multiply:
		case IASTBinaryExpression.op_divide: {
			rl.rexBoolToIntIfNecessary(loc, m_ExpressionTranslation);
			rr.rexBoolToIntIfNecessary(loc, m_ExpressionTranslation);
			return handleMultiplicativeOperation(main, loc, null, node.getOperator(), rl, rr);
		}
		case IASTBinaryExpression.op_moduloAssign:
		case IASTBinaryExpression.op_multiplyAssign:
		case IASTBinaryExpression.op_divideAssign: {
			rl.rexBoolToIntIfNecessary(loc, m_ExpressionTranslation);
			rr.rexBoolToIntIfNecessary(loc, m_ExpressionTranslation);
			return handleMultiplicativeOperation(main, loc, l.lrVal, node.getOperator(), rl, rr);
		}
		case IASTBinaryExpression.op_plus:
		case IASTBinaryExpression.op_minus: {
			rl.rexBoolToIntIfNecessary(loc, m_ExpressionTranslation);
			rr.rexBoolToIntIfNecessary(loc, m_ExpressionTranslation);
			return handleAdditiveOperation(main, loc, null, node.getOperator(), rl, rr);
		}
		case IASTBinaryExpression.op_plusAssign:
		case IASTBinaryExpression.op_minusAssign: {
			rl.rexBoolToIntIfNecessary(loc, m_ExpressionTranslation);
			rr.rexBoolToIntIfNecessary(loc, m_ExpressionTranslation);
			return handleAdditiveOperation(main, loc, l.lrVal, node.getOperator(), rl, rr);
		}
		case IASTBinaryExpression.op_binaryAnd:
		case IASTBinaryExpression.op_binaryOr:
		case IASTBinaryExpression.op_binaryXor: {
			rl.rexBoolToIntIfNecessary(loc, m_ExpressionTranslation);
			rr.rexBoolToIntIfNecessary(loc, m_ExpressionTranslation);
			return handleBitwiseArithmeticOperation(main, loc, null, node.getOperator(), rl, rr);
		}
		case IASTBinaryExpression.op_binaryAndAssign:
		case IASTBinaryExpression.op_binaryOrAssign:
		case IASTBinaryExpression.op_binaryXorAssign: {
			rl.rexBoolToIntIfNecessary(loc, m_ExpressionTranslation);
			rr.rexBoolToIntIfNecessary(loc, m_ExpressionTranslation);
			return handleBitwiseArithmeticOperation(main, loc, l.lrVal, node.getOperator(), rl, rr);
		}
		case IASTBinaryExpression.op_shiftLeft:
		case IASTBinaryExpression.op_shiftRight: {
			rl.rexBoolToIntIfNecessary(loc, m_ExpressionTranslation);
			rr.rexBoolToIntIfNecessary(loc, m_ExpressionTranslation);
			return handleBitshiftOperation(main, loc, null, node.getOperator(), rl, rr);

		}
		case IASTBinaryExpression.op_shiftLeftAssign:
		case IASTBinaryExpression.op_shiftRightAssign: {
			rl.rexBoolToIntIfNecessary(loc, m_ExpressionTranslation);
			rr.rexBoolToIntIfNecessary(loc, m_ExpressionTranslation);
			return handleBitshiftOperation(main, loc, l.lrVal, node.getOperator(), rl, rr);
		}
		
		default:
			String msg = "Unknown or unsupported unary operation";
			throw new UnsupportedSyntaxException(loc, msg);
		}
	}



	
	/**
	 * Handle relational operators according to Section 6.5.8 of C11.
	 * Assumes that left (resp. right) are the results from handling the operands.
	 * Requires that the {@link LRValue} of operands is an {@link RValue}
	 * (i.e., switchToRValueIfNecessary was applied if needed).
	 */
	ExpressionResult handleRelationalOperators(Dispatcher main, ILocation loc,
			int op, ExpressionResult left, ExpressionResult right) {
		assert (left.lrVal instanceof RValue) : "no RValue";
		assert (right.lrVal instanceof RValue) : "no RValue";
		left.rexBoolToIntIfNecessary(loc, m_ExpressionTranslation);
		right.rexBoolToIntIfNecessary(loc, m_ExpressionTranslation);
		final CType lType = left.lrVal.getCType().getUnderlyingType();
		final CType rType = right.lrVal.getCType().getUnderlyingType();

		final ExpressionResult result = ExpressionResult.copyStmtDeclAuxvarOverapprox(left, right);
		final Expression expr;
		if (lType instanceof CPrimitive && rType instanceof CPrimitive) {
			assert lType.isRealType() && rType.isRealType() : "no real type";
			m_ExpressionTranslation.usualArithmeticConversions(loc, left, right);
			expr = m_ExpressionTranslation.constructBinaryComparisonExpression(
					loc, op, left.lrVal.getValue(), (CPrimitive) left.lrVal.getCType(), 
					right.lrVal.getValue(), (CPrimitive) right.lrVal.getCType());
		} else if (lType instanceof CPointer && rType instanceof CPointer) {
			final Expression baseEquality = constructPointerComponentRelation(loc, 
					IASTBinaryExpression.op_equals, left.lrVal.getValue(), right.lrVal.getValue(), SFO.POINTER_BASE);
			final Expression offsetRelation = constructPointerComponentRelation(loc, 
					op, left.lrVal.getValue(), right.lrVal.getValue(), SFO.POINTER_OFFSET);
			switch (mMemoryHandler.getPointerSubtractionAndComparisonValidityCheckMode()) {
			case ASSERTandASSUME:
				Statement assertStm = new AssertStatement(loc, baseEquality);
				Check chk = new Check(Spec.ILLEGAL_POINTER_ARITHMETIC);
				chk.addToNodeAnnot(assertStm);
				result.stmt.add(assertStm);
				expr = offsetRelation;
				break;
			case ASSUME:
				Statement assumeStm = new AssumeStatement(loc, baseEquality);
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
	 * @param loc
	 * @param op Comparison operation.
	 * @param leftPointer Boogie expression that represents pointer.
	 * @param rightPointer Boogie expression that represents pointer.
	 * @param component Defines which component is compared. Either "base" or
	 * "offset"
	 */
	private Expression constructPointerComponentRelation(ILocation loc, int op, 
			Expression leftPointer, Expression rightPointer, String component) {
		assert component.equals(SFO.POINTER_BASE) || component.equals(SFO.POINTER_OFFSET) : "unknown pointer component";
		StructAccessExpression leftComponent = new StructAccessExpression(loc, leftPointer, component);
		StructAccessExpression rightComponent = new StructAccessExpression(loc, rightPointer, component);
		switch (op) {
		case IASTBinaryExpression.op_equals:
		case IASTBinaryExpression.op_notequals: {
			return m_ExpressionTranslation.constructBinaryEqualityExpression(loc, op, 
					leftComponent, m_ExpressionTranslation.getCTypeOfPointerComponents(), 
					rightComponent, m_ExpressionTranslation.getCTypeOfPointerComponents());
		}
		case IASTBinaryExpression.op_lessThan:
		case IASTBinaryExpression.op_lessEqual:
		case IASTBinaryExpression.op_greaterThan:
		case IASTBinaryExpression.op_greaterEqual:		
			return m_ExpressionTranslation.constructBinaryComparisonExpression(loc, op, 
					leftComponent, m_ExpressionTranslation.getCTypeOfPointerComponents(), 
					rightComponent, m_ExpressionTranslation.getCTypeOfPointerComponents());
		default:
			throw new IllegalArgumentException("op " + op);
		}
	}
	
	/**
	 * Handle multiplicative operators according to Sections 6.5.5 of C11.
	 * Assumes that left (resp. right) are the results from handling the operands.
	 * Requires that the {@link LRValue} of operands is an {@link RValue}
	 * (i.e., switchToRValueIfNecessary was applied if needed).
	 * requires that the Boogie expressions in left (resp. right) are a 
	 * non-boolean representation of these results 
	 * (i.e., rexBoolToIntIfNecessary() has already been applied if needed).
	 * @param lhs is non-null iff we haven an assignment
	 */
	ExpressionResult handleMultiplicativeOperation(Dispatcher main, ILocation loc, 
			LRValue lhs, int op, ExpressionResult left, ExpressionResult right) {
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
		m_ExpressionTranslation.usualArithmeticConversions(loc, left, right);
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
		
		final Expression expr = m_ExpressionTranslation.constructArithmeticExpression(
				loc, op, left.lrVal.getValue(), typeOfResult, right.lrVal.getValue(), typeOfResult);
		final RValue rval = new RValue(expr,typeOfResult, false, false);
		
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
	private void addDivisionByZeroCheck(Dispatcher main, ILocation loc, 
			ExpressionResult divisorExpRes) {
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
				zero = m_ExpressionTranslation.constructLiteralForIntegerType(loc, divisorType, BigInteger.ZERO);
			} else if (divisorType.isRealFloatingType()) {
				throw new AssertionError("case should have been handled before");
			} else {
				throw new UnsupportedOperationException("unsupported " + divisorType);
			}
			final Expression divisorNotZero = m_ExpressionTranslation.constructBinaryEqualityExpression(
					loc, IASTBinaryExpression.op_notequals, 
					divisor, divisorType, zero, divisorType); 
			final Statement additionalStatement;
			if (main.getTranslationSettings().getDivisionByZero() == POINTER_CHECKMODE.ASSUME) {
				additionalStatement = new AssumeStatement(loc, divisorNotZero);
			} else if (main.getTranslationSettings().getDivisionByZero() == POINTER_CHECKMODE.ASSERTandASSUME) {
				additionalStatement = new AssertStatement(loc, divisorNotZero);
				Check check = new Check(Check.Spec.DIVISION_BY_ZERO);
				check.addToNodeAnnot(additionalStatement);
			} else {
				throw new AssertionError("illegal");
			}
			divisorExpRes.stmt.add(additionalStatement);
		}
	}
	
	/**
	 * Handle additive operators according to Sections 6.5.6 of C11.
	 * Assumes that left (resp. right) are the results from handling the operands.
	 * Requires that the {@link LRValue} of operands is an {@link RValue}
	 * (i.e., switchToRValueIfNecessary was applied if needed).
	 * requires that the Boogie expressions in left (resp. right) are a 
	 * non-boolean representation of these results 
	 * (i.e., rexBoolToIntIfNecessary() has already been applied if needed).
	 * @param lhs is non-null iff we haven an assignment
	 */
	ExpressionResult handleAdditiveOperation(Dispatcher main, ILocation loc, 
			LRValue lhs, int op, ExpressionResult left, ExpressionResult right) {
		assert (left.lrVal instanceof RValue) : "no RValue";
		assert (right.lrVal instanceof RValue) : "no RValue";
		final CType lType = left.lrVal.getCType().getUnderlyingType();
		final CType rType = right.lrVal.getCType().getUnderlyingType();
		ExpressionResult result;
		final Expression expr;
		final CType typeOfResult;
		if (lType.isArithmeticType() && rType.isArithmeticType()) {
			m_ExpressionTranslation.usualArithmeticConversions(loc, left, right);
			typeOfResult = left.lrVal.getCType();
			assert typeOfResult.equals(right.lrVal.getCType());
			result = ExpressionResult.copyStmtDeclAuxvarOverapprox(left, right);
			addIntegerBoundsCheck(main, loc, result, (CPrimitive)  typeOfResult, op, left.lrVal.getValue(), right.lrVal.getValue());
			expr = m_ExpressionTranslation.constructArithmeticExpression(
				loc, op, left.lrVal.getValue(), (CPrimitive)  typeOfResult, right.lrVal.getValue(), (CPrimitive)  typeOfResult);
		} else if ((lType instanceof CPointer) && rType.isArithmeticType()) {
			typeOfResult = left.lrVal.getCType();
			CType pointsToType = ((CPointer) typeOfResult).pointsToType;
			result = ExpressionResult.copyStmtDeclAuxvarOverapprox(left, right);
			ExpressionResult re = doPointerArithmeticWithConversion(main, op, loc, left.lrVal.getValue(), (RValue) right.lrVal, pointsToType);
			result.addAll(re);
			expr = re.lrVal.getValue();
			addOffsetInBoundsCheck(main, loc, expr, result);
		} else if (lType.isArithmeticType() && (rType instanceof CPointer)) {
			if (op != IASTBinaryExpression.op_plus && op != IASTBinaryExpression.op_plusAssign) {
				throw new AssertionError("lType arithmetic, rType CPointer only legal if op is plus");
			}
			typeOfResult = right.lrVal.getCType();
			CType pointsToType = ((CPointer) typeOfResult).pointsToType;
			result = ExpressionResult.copyStmtDeclAuxvarOverapprox(left, right);
			ExpressionResult re = doPointerArithmeticWithConversion(main, op, loc, right.lrVal.getValue(), (RValue) left.lrVal, pointsToType);
			result.addAll(re);
			expr = re.lrVal.getValue();
			addOffsetInBoundsCheck(main, loc, expr, result);
		} else if ((lType instanceof CPointer) && (rType instanceof CPointer)) {
			if (op != IASTBinaryExpression.op_minus && op != IASTBinaryExpression.op_minusAssign) {
				throw new AssertionError("lType arithmetic, rType CPointer only legal if op is minus");
			}
			// C11 6.5.6.9 says 
			//     "The size of the result is implementation-defined, 
			//     and its type (a signed integer type) is ptrdiff_t defined in 
			//     the <stddef.h> header."
			// We randomly choose the type whose Boogie translation we use to 
			// represent pointer components.
			typeOfResult = m_ExpressionTranslation.getCTypeOfPointerComponents();
			result = ExpressionResult.copyStmtDeclAuxvarOverapprox(left, right);
			CType pointsToType;
			{
				CType leftPointsToType = ((CPointer) lType).pointsToType;
				CType rightPointsToType = ((CPointer) rType).pointsToType;
				if (!leftPointsToType.equals(rightPointsToType)) {
					// TODO: Matthias 2015-09-08: Maybe this is too strict and we
					// have to check leftPointsToType.isCompatibleWith(rightPointsToType)
					throw new UnsupportedOperationException("incompatible pointers: pointsto " 
										+ leftPointsToType + " " + rightPointsToType);
				}
				pointsToType = leftPointsToType;
			}
			addBaseEqualityCheck(main, loc, left.lrVal.getValue(), right.lrVal.getValue(), result);
			expr = doPointerSubtraction(main, loc, left.lrVal.getValue(), right.lrVal.getValue(), pointsToType);
		} else {
			throw new UnsupportedOperationException("non-standard case of pointer arithmetic");
		}
		final RValue rval = new RValue(expr,typeOfResult, false, false);
		
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
	 * Check if two pointers have the same base component (i.e. if both point
	 * to the same array object).
	 * Depending on the preferences of this plugin we
	 * <ul> 
	 *  <li> assert that both have the same base component,
	 *  <li> assume that both have the same base component, or
	 *  <li> add nothing.
	 * </ul>
	 * 
	 * @param leftPtr Boogie {@link Expression} that represents the left pointer.
	 * @param rightPtr Boogie {@link Expression} that represents the right pointer.
	 * @param result {@link ExpressionResult} to which the additional statements
	 * are added.
	 */
	private void addBaseEqualityCheck(Dispatcher main, ILocation loc,
			Expression leftPtr, Expression rightPtr, ExpressionResult result) {
		if (mMemoryHandler.getPointerSubtractionAndComparisonValidityCheckMode() == POINTER_CHECKMODE.IGNORE) {
			// do not check anything
			return;
		}
		final Expression baseEquality = constructPointerComponentRelation(loc, 
				IASTBinaryExpression.op_equals, leftPtr, rightPtr, SFO.POINTER_BASE);
		switch (mMemoryHandler.getPointerSubtractionAndComparisonValidityCheckMode()) {
		case ASSERTandASSUME:
			Statement assertStm = new AssertStatement(loc, baseEquality);
			Check chk = new Check(Spec.ILLEGAL_POINTER_ARITHMETIC);
			chk.addToNodeAnnot(assertStm);
			result.stmt.add(assertStm);
			break;
		case ASSUME:
			Statement assumeStm = new AssumeStatement(loc, baseEquality);
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
	 * @param leftPtr Boogie {@link Expression} that represents the left pointer.
	 * @param rightPtr Boogie {@link Expression} that represents the right pointer.
	 * @param pointsToType {@link CType} of the objects to which the pointers
	 * point.
	 * @return An {@link Expression} that represents the difference of two
	 * Pointers according to C11 6.5.6.9.
	 */
	private Expression doPointerSubtraction(Dispatcher main,
			ILocation loc, Expression ptr1, Expression ptr2,
			CType pointsToType) {
		Expression ptr1Offset = new StructAccessExpression(loc, ptr1, SFO.POINTER_OFFSET);
		Expression ptr2Offset = new StructAccessExpression(loc, ptr2, SFO.POINTER_OFFSET);
		Expression offsetDifference = m_ExpressionTranslation.constructArithmeticExpression(
				loc, 
				IASTBinaryExpression.op_minus, ptr1Offset, 
				m_ExpressionTranslation.getCTypeOfPointerComponents(), ptr2Offset, m_ExpressionTranslation.getCTypeOfPointerComponents());
		Expression typesize = mMemoryHandler.calculateSizeOf(loc, pointsToType);
		CPrimitive typesizeType = new CPrimitive(PRIMITIVE.INT);
		//TODO: typesizeType and .getCTypeOfPointerComponents() might be 
		// different then one expression has to be converted into the type of
		// the other
		Expression offsetDifferenceDividedByTypesize = m_ExpressionTranslation.constructArithmeticExpression(
				loc, 
				IASTBinaryExpression.op_divide, offsetDifference,
				m_ExpressionTranslation.getCTypeOfPointerComponents(), typesize, typesizeType);
		return offsetDifferenceDividedByTypesize;
	}

		
	/**
	 * Check if pointer offset is in a legal range.
	 * In case a pointer points to allocated memory, the "base" of a pointer 
	 * points to some array object (in C). Now we check if the offset of this
	 * pointer does not violate the bounds of that array.
	 * This means that the offset 
	 * <ul> 
	 *  <li> must be non-negative, and
	 *  <li> must be small enough that the pointer points to an element of the
	 *       array or one past the last element of the array.
	 * </ul>
	 * Depending on the preferences of this plugin we
	 * <ul> 
	 *  <li> assert that the offset is in the bounds of the array,
	 *  <li> assume that the offset is in the bounds of the array, or
	 *  <li> add nothing.
	 * </ul>
	 * 
	 * @param ptr Boogie {@link Expression} that represents the pointer.
	 * @param result {@link ExpressionResult} to which the additional statements
	 * are added.
	 */
	private void addOffsetInBoundsCheck(Dispatcher main, ILocation loc,
			Expression ptr, ExpressionResult result) {
		//TODO: Matthias 2015-09-08 implement this
		// maybe additional parameters are required.
	}

	/**
	 * Handle equality operators according to Section 6.5.9 of C11.
	 * Assumes that left (resp. right) are the results from handling the operands.
	 * Requires that the {@link LRValue} of operands is an {@link RValue}
	 * (i.e., switchToRValueIfNecessary was applied if needed).
	 * requires that the Boogie expressions in left (resp. right) are a 
	 * non-boolean representation of these results 
	 * (i.e., rexBoolToIntIfNecessary() has already been applied if needed).
	 */
	ExpressionResult handleEqualityOperators(Dispatcher main, ILocation loc,
			int op, ExpressionResult left, ExpressionResult right) {
		assert (left.lrVal instanceof RValue) : "no RValue";
		assert (right.lrVal instanceof RValue) : "no RValue";
		{
			final CType lType = left.lrVal.getCType().getUnderlyingType();
			final CType rType = right.lrVal.getCType().getUnderlyingType();
			//FIXME Matthias 2015-09-05: operation only legal if both have type 
			// CPointer I guess the following implicit casts are a workaround
			// for arrays (or structs or union?)
			if (lType instanceof CPointer || rType instanceof CPointer) {
				if (!(lType instanceof CPointer)) {
//					throw new AssertionError("illegal case");
//					FIXME: the following is a workaround for the null pointer
					convert(loc, left, new CPointer(new CPrimitive(PRIMITIVE.VOID)));
				}
				if (!(rType instanceof CPointer)) {
//					throw new AssertionError("illegal case");
//					FIXME: the following is a workaround for the null pointer
					convert(loc, right, new CPointer(new CPrimitive(PRIMITIVE.VOID)));
				}
			} else if (lType.isArithmeticType() && rType.isArithmeticType()) {
				m_ExpressionTranslation.usualArithmeticConversions(loc, left, right);
			} else {
				throw new UnsupportedOperationException("unsupported " + rType + ", " + lType);
			}
		}
		// The result has type int (C11 6.5.9.1)
		final CPrimitive typeOfResult = new CPrimitive(PRIMITIVE.INT);
		final Expression expr = m_ExpressionTranslation.constructBinaryEqualityExpression(
				loc, op, left.lrVal.getValue(), left.lrVal.getCType(), 
				right.lrVal.getValue(), right.lrVal.getCType());
		final RValue rval = new RValue(expr,typeOfResult, true, false);
		final ExpressionResult result = ExpressionResult.copyStmtDeclAuxvarOverapprox(left, right);
		result.lrVal = rval;
		return result;
	}
	
	/**
	 * Handle equality operators according to Section 6.5.7 of C11.
	 * Assumes that left (resp. right) are the results from handling the operands.
	 * Requires that the {@link LRValue} of operands is an {@link RValue}
	 * (i.e., switchToRValueIfNecessary was applied if needed).
	 * requires that the Boogie expressions in left (resp. right) are a 
	 * non-boolean representation of these results 
	 * (i.e., rexBoolToIntIfNecessary() has already been applied if needed).
	 * @param lhs is non-null iff we haven an assignment
	 */
	ExpressionResult handleBitshiftOperation(Dispatcher main, ILocation loc, 
			LRValue lhs, int op, ExpressionResult left, ExpressionResult right) {
		assert (left.lrVal instanceof RValue) : "no RValue";
		assert (right.lrVal instanceof RValue) : "no RValue";
		final CType lType = left.lrVal.getCType().getUnderlyingType();
		final CType rType = right.lrVal.getCType().getUnderlyingType();
		if (!rType.isIntegerType() || !lType.isIntegerType()) {
			throw new UnsupportedOperationException("operands have to have integer types");
		}
		m_ExpressionTranslation.doIntegerPromotion(loc, left);
		final CPrimitive typeOfResult = (CPrimitive) left.lrVal.getCType();
		convert(loc, right, typeOfResult);
		final Expression expr = m_ExpressionTranslation.constructBinaryBitwiseExpression(
				loc, op, left.lrVal.getValue(), typeOfResult, right.lrVal.getValue(), typeOfResult);
		final RValue rval = new RValue(expr,typeOfResult, false, false);
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
			final ExpressionResult result = makeAssignment(loc, copy.stmt, lhs, rval, copy.decl, copy.auxVars, copy.overappr);
			return result;
		}
		default:
			throw new AssertionError("no bitshift " + op);
		}
	}
	
	/**
	 * Handle bitwise AND, bitwise XOR, and bitwise OR operators according to 
	 * sections 6.5.10, 6.5.11, 6.5.12 of C11.
	 * Assumes that left (resp. right) are the results from handling the operands.
	 * Requires that the {@link LRValue} of operands is an {@link RValue}
	 * (i.e., switchToRValueIfNecessary was applied if needed).
	 * requires that the Boogie expressions in left (resp. right) are a 
	 * non-boolean representation of these results 
	 * (i.e., rexBoolToIntIfNecessary() has already been applied if needed).
	 * @param lhs is non-null iff we haven an assignment
	 */
	ExpressionResult handleBitwiseArithmeticOperation(Dispatcher main, ILocation loc, 
			LRValue lhs, int op, ExpressionResult left, ExpressionResult right) {
		assert (left.lrVal instanceof RValue) : "no RValue";
		assert (right.lrVal instanceof RValue) : "no RValue";
		final CType lType = left.lrVal.getCType().getUnderlyingType();
		final CType rType = right.lrVal.getCType().getUnderlyingType();
		if (!rType.isIntegerType() || !lType.isIntegerType()) {
			throw new UnsupportedOperationException("operands have to have integer types");
		}
		m_ExpressionTranslation.usualArithmeticConversions(loc, left, right);
		final CPrimitive typeOfResult = (CPrimitive) left.lrVal.getCType();
		assert typeOfResult.equals(left.lrVal.getCType());
		final Expression expr = m_ExpressionTranslation.constructBinaryBitwiseExpression(
				loc, op, left.lrVal.getValue(), typeOfResult, right.lrVal.getValue(), typeOfResult);
		final RValue rval = new RValue(expr,typeOfResult, false, false);
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
			final ExpressionResult result = makeAssignment(loc, copy.stmt, lhs, rval, copy.decl, copy.auxVars, copy.overappr);
			return result;
		}
		default:
			throw new AssertionError("no bitwise arithmetic operation " + op);
		}
	}
	
	
	/**
	 * Add checks for integer overflows.
	 * Construct arithmetic operation and add an assert statement that checks 
	 * if the result is in the range of the corresponding C data type (i.e. 
	 * check for overflow wrt. max and min value). 
	 * Note that we do not check if a given expression is in the range. We
	 * explicitly construct a new expression for the arithmetic operation
	 * in this check because we possibly have to adjust the data type used in
	 * boogie. E.g., if we use 32bit bitvectors in Boogie we are unable to
	 * express an overflow check for a 32bit integer addition in C. Instead, we 
	 * have to use a 33bit bit bitvector in Boogie.
	 */
	private void addIntegerBoundsCheck(Dispatcher main, ILocation loc, ExpressionResult rex, 
			CPrimitive resultType, int operation, Expression... operands) {
		if (main.mPreferences.getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_SIGNED_INTEGER_BOUNDS)
				&& resultType.isIntegerType()
				&& !resultType.isUnsigned()) {
			Check check = new Check(Spec.INTEGER_OVERFLOW);
			final Expression operationResult;
			if (operands.length == 1) {
				operationResult = m_ExpressionTranslation.constructUnaryExpression(
						loc, operation, operands[0], resultType);
			} else if (operands.length == 2) {
				operationResult = m_ExpressionTranslation.constructArithmeticExpression(
						loc, operation, operands[0], resultType, operands[1], resultType);
			} else {
				throw new AssertionError("no such operation");
			}
			AssertStatement smallerMaxInt = new AssertStatement(loc, ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPLT, operationResult, 
					new IntegerLiteral(loc, main.getTypeSizes().getMaxValueOfPrimitiveType((CPrimitive) resultType).toString())));
			check.addToNodeAnnot(smallerMaxInt);
			AssertStatement biggerMinInt = new AssertStatement(loc, ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPGEQ, operationResult, 
					new IntegerLiteral(loc, main.getTypeSizes().getMinValueOfPrimitiveType((CPrimitive) resultType).toString())));
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
		Result r = main.dispatch(node.getExpression());
		if (r instanceof ExpressionResult) {
			ExpressionResult rExp = (ExpressionResult) r;
//			if (!rExp.stmt.isEmpty()) {
				ArrayList<Statement> stmt = new ArrayList<Statement>(rExp.stmt);
				ArrayList<Declaration> decl = new ArrayList<Declaration>(rExp.decl);
				List<Overapprox> overappr = new ArrayList<Overapprox>();
//				assert (isAuxVarMapcomplete(main, rExp.decl, rExp.auxVars));
				stmt.addAll(createHavocsForAuxVars(rExp.auxVars));
				overappr.addAll(rExp.overappr);
				Map<VariableDeclaration, ILocation> emptyAuxVars = new LinkedHashMap<VariableDeclaration, ILocation>(0);
				return new ExpressionResult(stmt, rExp.lrVal, decl, emptyAuxVars, overappr);
//			} else {
//				String msg = "This statement has no effect and will be dropped: " + node.getRawSignature();
//				main.warn(LocationFactory.createCLocation(node), msg);
//				return new SkipResult();
//			}
		} else if (r instanceof ExpressionListResult) {
			ArrayList<Statement> stmt = new ArrayList<Statement>();
			ArrayList<Declaration> decl = new ArrayList<Declaration>();
			List<Overapprox> overappr = new ArrayList<Overapprox>();
			Map<VariableDeclaration, ILocation> emptyAuxVars = new LinkedHashMap<VariableDeclaration, ILocation>(0);
			for (ExpressionResult res : ((ExpressionListResult) r).list) {
				if (!res.stmt.isEmpty()) {
					stmt.addAll(res.stmt);
					decl.addAll(res.decl);
//					assert (isAuxVarMapcomplete(main, res.decl, res.auxVars));
					stmt.addAll(createHavocsForAuxVars(res.auxVars));
					overappr.addAll(res.overappr);
				}
			}

			return new ExpressionResult(stmt, null, decl, emptyAuxVars, overappr);
		} else if (r instanceof SkipResult) {
			return r;
		}
		String msg = "We always convert to AssignmentStatement, other options raise this error!";
		ILocation loc = LocationFactory.createCLocation(node);
		throw new UnsupportedSyntaxException(loc, msg);
	}

	@Override
	public Result visit(Dispatcher main, IASTIfStatement node) {
		ILocation loc = LocationFactory.createCLocation(node);
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		ArrayList<Statement> stmt = new ArrayList<Statement>();
		List<Overapprox> overappr = new ArrayList<Overapprox>();
		Map<VariableDeclaration, ILocation> emptyAuxVars = new LinkedHashMap<VariableDeclaration, ILocation>();

		ExpressionResult condResult = (ExpressionResult) main.dispatch(node.getConditionExpression());
		condResult = condResult.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
		condResult.rexIntToBoolIfNecessary(loc, m_ExpressionTranslation, mMemoryHandler);
		RValue cond = (RValue) condResult.lrVal;
		decl.addAll(condResult.decl);
		stmt.addAll(condResult.stmt);
		overappr.addAll(condResult.overappr);
		List<HavocStatement> havocs = createHavocsForAuxVars(condResult.auxVars);

		Result thenResult = main.dispatch(node.getThenClause());
		List<Statement> thenStmt = new ArrayList<Statement>();
		thenStmt.addAll(havocs);
		if (thenResult instanceof ExpressionResult) {
			ExpressionResult re = (ExpressionResult) thenResult;
			decl.addAll(re.decl);
			thenStmt.addAll(re.stmt);
		} else if (thenResult instanceof Result) {
			if (thenResult.node instanceof Body) {
				Body thenPart = (Body) (thenResult.node);
				thenStmt.addAll(Arrays.asList(thenPart.getBlock()));
				decl.addAll(Arrays.asList(thenPart.getLocalVars()));
			} else if (thenResult instanceof SkipResult) {
				//add no statements or declarations
			} else {
				String msg = "Error: unexpected dispatch result";
				throw new IncorrectSyntaxException(loc, msg);
			}
		}

		List<Statement> elseStmt = new ArrayList<Statement>();
		elseStmt.addAll(havocs);
		if (node.getElseClause() != null) {
			Result elseResult = main.dispatch(node.getElseClause());
			if (elseResult instanceof ExpressionResult) {
				ExpressionResult re = (ExpressionResult) elseResult;
				decl.addAll(re.decl);
				elseStmt.addAll(re.stmt);
			} else if (elseResult instanceof Result) {
				if (elseResult.node instanceof Body) {
					Body elsePart = (Body) (elseResult.node);
					elseStmt.addAll(Arrays.asList(elsePart.getBlock()));
					decl.addAll(Arrays.asList(elsePart.getLocalVars()));
				}
			} else {
				String msg = "Error: unexpected dispatch result";
				throw new IncorrectSyntaxException(loc, msg);
			}
		}
		assert thenStmt != null;
		assert elseStmt != null;
		// TODO : handle if(pointer), if(pointer==NULL) and if(pointer==0)
		IfStatement ifStmt = new IfStatement(loc, cond.getValue(), thenStmt.toArray(new Statement[0]),
				elseStmt.toArray(new Statement[0]));
		Map<String, IAnnotations> annots = ifStmt.getPayload().getAnnotations();
		for (Overapprox overapprItem : overappr) {
			annots.put(Overapprox.getIdentifier(), overapprItem);
		}
		stmt.add(ifStmt);
		return new ExpressionResult(stmt, null, decl, emptyAuxVars, overappr);
	}


	@Override
	public Result visit(Dispatcher main, IASTWhileStatement node) {
		ExpressionResult condResult = (ExpressionResult) main.dispatch(node.getCondition());
		String loopLabel = mNameHandler.getGloballyUniqueIdentifier(SFO.LOOPLABEL);
		mInnerMostLoopLabel.push(loopLabel);
		Result bodyResult = main.dispatch(node.getBody());
		mInnerMostLoopLabel.pop();
		return handleLoops(main, node, bodyResult, condResult, loopLabel);
	}

	@Override
	public Result visit(Dispatcher main, IASTForStatement node) {
		String loopLabel = mNameHandler.getGloballyUniqueIdentifier(SFO.LOOPLABEL);
		return handleLoops(main, node, null, null, loopLabel);
	}

	@Override
	public Result visit(Dispatcher main, IASTDoStatement node) {
		ExpressionResult condResult = (ExpressionResult) main.dispatch(node.getCondition());
		String loopLabel = mNameHandler.getGloballyUniqueIdentifier(SFO.LOOPLABEL);
		mInnerMostLoopLabel.push(loopLabel);
		Result bodyResult = main.dispatch(node.getBody());
		mInnerMostLoopLabel.pop();
		return handleLoops(main, node, bodyResult, condResult, loopLabel);
	}

	@Override
	public Result visit(Dispatcher main, IASTContinueStatement cs) {
		ILocation loc = LocationFactory.createCLocation(cs);
		ArrayList<Statement> stmt = new ArrayList<Statement>();
		stmt.add(new GotoStatement(loc, new String[] { mInnerMostLoopLabel.peek() }));
		ExpressionResult contResult = new ExpressionResult(stmt, null);
		return contResult;
	}

	@Override
	public Result visit(Dispatcher main, IASTExpressionList node) {
		ExpressionListResult result = new ExpressionListResult();
		for (IASTExpression expr : node.getExpressions()) {
			Result r = main.dispatch(expr);
			assert r instanceof ExpressionResult;
			result.list.add((ExpressionResult) r);
		}
		return result;
	}

	@Override
	public Result visit(Dispatcher main, IASTInitializerList node) {
		ILocation loc = LocationFactory.createCLocation(node);
		if (node.getClauses().length != node.getSize()) {
			throw new IllegalArgumentException("You might have parsed your code with "
					+ "ITranslationUnit.AST_SKIP_TRIVIAL_EXPRESSIONS_IN_AGGREGATE_INITIALIZERS!");
		}
		ExpressionListRecResult result = new ExpressionListRecResult();
		for (IASTInitializerClause i : node.getClauses()) {
			Result r = main.dispatch(i);
			if (r instanceof ExpressionListRecResult) {
				result.list.add((ExpressionListRecResult) r);
			} else if (r instanceof ExpressionResult) {
				ExpressionResult rex = (ExpressionResult) r;
				rex = rex.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
				result.list.add(new ExpressionListRecResult(rex.stmt, rex.lrVal, rex.decl, rex.auxVars, rex.overappr));
//				result.auxVars.putAll(((ResultExpression) r).auxVars);//what for??
			} else {
				String msg = "Unexpected result";
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
		Check check = new Check(Check.Spec.PRE_CONDITION);
		ILocation loc = LocationFactory.createCLocation(node, check);
		IASTExpression functionName = node.getFunctionNameExpression();
		if (functionName instanceof IASTIdExpression) {
			Result standardFunction =  mFunctionHandler.handleStandardFunctions(main, 
					mMemoryHandler, mStructHandler, loc,
					((IASTIdExpression) functionName).getName().toString(), node.getArguments());
			if (standardFunction != null)
				return standardFunction;
		}
		return mFunctionHandler.handleFunctionCallExpression(main, 
				mMemoryHandler, mStructHandler, loc, functionName, node.getArguments());
	}

	@Override
	public Result visit(Dispatcher main, IASTBreakStatement node) {
		ArrayList<Statement> stmt = new ArrayList<Statement>();
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
		ILocation loc = LocationFactory.createCLocation(node);
		ArrayList<Statement> stmt = new ArrayList<Statement>();
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>();
		List<Overapprox> overappr = new ArrayList<Overapprox>();

		// dispatch the controlling expression, convert it to int
		Result switchParam = main.dispatch(node.getControllerExpression());
		assert switchParam instanceof ExpressionResult;
		ExpressionResult l = ((ExpressionResult) switchParam).switchToRValueIfNecessary(main, mMemoryHandler,
				mStructHandler, loc);
		// 6.8.4.2-1: "The controlling expression of a switch statement shall have integer type."
		// note that this does not mean that it has "int" type, it may be long or char, for instance
		assert l.lrVal.getCType().isIntegerType();
		// 6.8.4.2-5: "The integer promotions are performed on the controlling expression."
		m_ExpressionTranslation.doIntegerPromotion(loc, l);
		
		stmt.addAll(l.stmt);
		decl.addAll(l.decl);
		auxVars.putAll(l.auxVars);
		overappr.addAll(l.overappr);
		Expression switchArg = l.lrVal.getValue();


		CPrimitive intType = new CPrimitive(PRIMITIVE.INT);
		String breakLabelName = mNameHandler.getGloballyUniqueIdentifier("SWITCH~BREAK~");
        String switchFlag = mNameHandler.getTempVarUID(SFO.AUXVAR.SWITCH, intType);
        ASTType flagType = new PrimitiveType(loc, SFO.BOOL);

        VariableDeclaration switchAuxVarDec = SFO.getTempVarVariableDeclaration(switchFlag, flagType, loc);
        decl.add(switchAuxVarDec);
        auxVars.put(switchAuxVarDec, loc);


        boolean isFirst = true;
        boolean firstCond = true;
		Expression cond = null;
		ILocation locC = null;
		
		ArrayList<Statement> ifBlock = new ArrayList<Statement>();
		this.beginScope();
		for (IASTNode child : node.getBody().getChildren()) {
			if (isFirst && !(child instanceof IASTCaseStatement || child instanceof IASTDefaultStatement)) {
				// declarations in the beginning of a switch body (i.e. before the first case/default) are used, statements are dropped
				// see example 6.8.4.2-7
				
				// we need to dispatch the child in order to fill the symbol table with declarations accordingly
				// the result can only contain statements, which we drop.
				main.dispatch(child);

				continue;
			}
			isFirst = false;

			checkForACSL(main, ifBlock, decl, child, null);
			if (child instanceof IASTCaseStatement || child instanceof IASTDefaultStatement) {
				ExpressionResult caseExpression = (ExpressionResult) main.dispatch(child);
				if (locC != null) {
					IfStatement ifStmt = new IfStatement(locC, new IdentifierExpression(locC, switchFlag), ifBlock.toArray(new Statement[0]),
									new Statement[0]);
					Map<String, IAnnotations> annots = ifStmt.getPayload().getAnnotations();

					for (Overapprox overapprItem : caseExpression.overappr) {
						annots.put(Overapprox.getIdentifier(), overapprItem);
					}
	
					if (firstCond) {
						stmt.add(new AssignmentStatement(locC, new LeftHandSide[] {new VariableLHS(locC, switchFlag)}, new Expression[] { cond }));
						firstCond = false;
					} else {
						stmt.add(new AssignmentStatement(locC, new LeftHandSide[] {new VariableLHS(locC, switchFlag)}, 
												new Expression[] { ExpressionFactory.newBinaryExpression(locC, Operator.LOGICOR, new IdentifierExpression(locC, switchFlag), cond)}));
					}
					stmt.add(ifStmt);
				}

				ifBlock = new ArrayList<Statement>();
				locC = LocationFactory.createCLocation(child);

				if (child instanceof IASTCaseStatement) {
					// 6.8.4.2-5: "The constant	expression in each case label is converted to the promoted type of the controlling expression"
					m_ExpressionTranslation.convertIntToInt(locC, caseExpression, (CPrimitive) l.lrVal.getCType());
					cond = ExpressionFactory.newBinaryExpression(locC, Operator.COMPEQ, switchArg, caseExpression.lrVal.getValue());
					decl.addAll(caseExpression.decl);
					stmt.addAll(caseExpression.stmt);
					auxVars.putAll(caseExpression.auxVars);
					overappr.addAll(caseExpression.overappr);
				} else {
					//default statement
					cond = caseExpression.lrVal.getValue();
				}

				/*
				for (Statement s : res.stmt)
					if (s instanceof BreakStatement)
						ifBlock.add(new GotoStatement(locC, new String[] { breakLabelName }));
					else
						ifBlock.add(s);
				*/
			} else {
				Result r = main.dispatch(child);

				if (r instanceof ExpressionResult) {
					ExpressionResult res = (ExpressionResult) r;
					decl.addAll(res.decl);
					auxVars.putAll(res.auxVars);
					overappr.addAll(res.overappr);
					for (Statement s : res.stmt)
						if (s instanceof BreakStatement)
							ifBlock.add(new GotoStatement(locC, new String[] { breakLabelName }));
						else
							ifBlock.add(s);
				}
				if (r.node != null && r.node instanceof Body) {
					// we already have a unique naming for variables! -> unfold
					Body b = ((Body) r.node);
					decl.addAll(Arrays.asList(b.getLocalVars()));
					for (Statement s : b.getBlock()) {
							if (s instanceof BreakStatement)
								ifBlock.add(new GotoStatement(locC, new String[] { breakLabelName }));
							else
								ifBlock.add(s);
					}
				}
			}
		}
		assert cond != null;
		if (locC != null) {
			IfStatement ifStmt = new IfStatement(locC, new IdentifierExpression(locC, switchFlag), ifBlock.toArray(new Statement[0]),
							new Statement[0]);
			Map<String, IAnnotations> annots = ifStmt.getPayload().getAnnotations();
			for (Overapprox overapprItem : overappr) {
				annots.put(Overapprox.getIdentifier(), overapprItem);
			}

			if (firstCond) {
				stmt.add(new AssignmentStatement(locC, new LeftHandSide[] {new VariableLHS(locC, switchFlag)}, new Expression[] { cond }));
				firstCond = false;
			} else {
				stmt.add(new AssignmentStatement(locC, new LeftHandSide[] {new VariableLHS(locC, switchFlag)}, 
										new Expression[] { ExpressionFactory.newBinaryExpression(locC, Operator.LOGICOR, new IdentifierExpression(locC, switchFlag), cond)}));
			}
			stmt.add(ifStmt);
		}
		checkForACSL(main, stmt, decl, null, node);

		stmt.add(new Label(loc, breakLabelName));
		stmt.addAll(createHavocsForAuxVars(auxVars));
		
		
		stmt = updateStmtsAndDeclsAtScopeEnd(main, decl, stmt);
		this.endScope();
		
		return new ExpressionResult(stmt, null, decl, new LinkedHashMap<VariableDeclaration, ILocation>(), overappr);
	}	

	/**
	 * Translate a case statement for use inside a switch statement.
	 * C99:6.8.4.2-3: "The expression of each case label shall be an integer constant expression and no two
	 *   of the case constant expressions in  the same switch statement shall have the same value after conversion."
	 * 
	 */
	@Override
	public Result visit(Dispatcher main, IASTCaseStatement node) {
		ILocation loc = LocationFactory.createCLocation(node);
		ExpressionResult c = (ExpressionResult) main.dispatch(node.getExpression());
		c = c.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, LocationFactory.createCLocation(node));
		m_ExpressionTranslation.convertIntToInt(loc, c, new CPrimitive(PRIMITIVE.INT));
		return c;
	}

	@Override
	public Result visit(Dispatcher main, IASTDefaultStatement node) {
		ArrayList<Statement> stmt = new ArrayList<Statement>();
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		Map<VariableDeclaration, ILocation> emptyAuxVars = new LinkedHashMap<VariableDeclaration, ILocation>(0);
		List<Overapprox> overappr = new ArrayList<Overapprox>();
		return new ExpressionResult(stmt, new RValue(new BooleanLiteral(LocationFactory.createCLocation(node), true), new CPrimitive(
				PRIMITIVE.INT)), decl, emptyAuxVars, overappr);
	}

	@Override
	public Result visit(Dispatcher main, IASTLabelStatement node) {
		ILocation loc = LocationFactory.createCLocation(node);
		ArrayList<Statement> stmt = new ArrayList<Statement>();
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		Map<VariableDeclaration, ILocation> emptyAuxVars = new LinkedHashMap<VariableDeclaration, ILocation>(0);
		List<Overapprox> overappr = new ArrayList<Overapprox>();
		String label = node.getName().toString();
		if (mErrorLabelWarning && label.equals("ERROR")) {
			String longDescription = "The label \"ERROR\" does not have a special meaning in the translation mode you selected. You might want to change your settings and use the SV-COMP translation mode.";
			main.warn(loc, longDescription);
		}
		stmt.add(new Label(loc, label));
		Result r = main.dispatch(node.getNestedStatement());
		if (r instanceof ExpressionResult) {
			ExpressionResult res = (ExpressionResult) r;
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
				Body b = ((Body) r.node);
				decl.addAll(Arrays.asList(b.getLocalVars()));
				stmt.addAll(Arrays.asList(b.getBlock()));
			} else {
				String msg = "Unexpected boogie AST node type: " + r.node.getClass();
				throw new UnsupportedSyntaxException(loc, msg);
			}
			return new ExpressionResult(stmt, expr, decl, emptyAuxVars);
		}
	}

	@Override
	public Result visit(Dispatcher main, IASTGotoStatement node) {
		ArrayList<Statement> stmt = new ArrayList<Statement>();
		String[] name = new String[] { node.getName().toString() };
		stmt.add(new GotoStatement(LocationFactory.createCLocation(node), name));
		return new ExpressionResult(stmt, null);
	}

	@Override
	public Result visit(Dispatcher main, IASTCastExpression node) {
		ILocation loc = LocationFactory.createCLocation(node); 

		// TODO: check validity of cast?

		TypesResult resTypes = (TypesResult) main.dispatch(node.getTypeId().getDeclSpecifier());

		mCurrentDeclaredTypes.push(resTypes);
		DeclaratorResult declResult = (DeclaratorResult) main.dispatch(node.getTypeId().getAbstractDeclarator());
		CType newCType = declResult.getDeclaration().getType();
		mCurrentDeclaredTypes.pop();
		
		ExpressionResult expr = (ExpressionResult) main.dispatch(node.getOperand()); 
		if (expr.lrVal.getCType().getUnderlyingType() instanceof CArray
				&& newCType.getUnderlyingType() instanceof CPointer) {
			CType valueType = ((CArray) expr.lrVal.getCType().getUnderlyingType()).getValueType().getUnderlyingType();
				if (expr.lrVal instanceof HeapLValue)
					expr.lrVal = new RValue(((HeapLValue)expr.lrVal).getAddress(), new CPointer(valueType));
				else
					expr.lrVal = new RValue(expr.lrVal.getValue(), new CPointer(valueType));	
		} else {
			expr = expr.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
		}

		if (s_PointerCastIsUnsupportedSyntax && newCType instanceof CPointer && expr.lrVal.getCType() instanceof CPointer) {
			CType newPointsToType = ((CPointer) newCType).pointsToType;
			CType exprPointsToType = ((CPointer) expr.lrVal.getCType()).pointsToType;
			if (newPointsToType instanceof CPrimitive
					&& exprPointsToType instanceof CPrimitive) {
				if (
						((CPrimitive) newPointsToType).getGeneralType() == GENERALPRIMITIVE.INTTYPE
						&& ((CPrimitive) exprPointsToType).getGeneralType() == GENERALPRIMITIVE.INTTYPE
						) {
					if (
							(((CPrimitive) newPointsToType).isUnsigned()
									&& !((CPrimitive) exprPointsToType).isUnsigned())
									||
									!(((CPrimitive) newPointsToType).isUnsigned()
											&& ((CPrimitive) exprPointsToType).isUnsigned())
							) {
						throw new UnsupportedSyntaxException(loc, "unsupported cast: " + exprPointsToType 
								+ " pointer  to " + newPointsToType + " pointer");
					}

				} else if ( 
						((CPrimitive) newPointsToType).getGeneralType() == GENERALPRIMITIVE.VOID
						&& ((CPrimitive) exprPointsToType).getGeneralType() == GENERALPRIMITIVE.INTTYPE
						||
						((CPrimitive) newPointsToType).getGeneralType() == GENERALPRIMITIVE.INTTYPE
						&& ((CPrimitive) exprPointsToType).getGeneralType() == GENERALPRIMITIVE.VOID
						) {
					throw new UnsupportedSyntaxException(loc, "unsupported cast: " + exprPointsToType 
							+ " pointer  to " + newPointsToType + " pointer");
				}
			}
		}

		expr.rexBoolToIntIfNecessary(loc, m_ExpressionTranslation);
		convert(loc, expr, newCType);

		// String msg = "Ignored cast! At line: "
		// + node.getFileLocation().getStartingLineNumber();
		// Dispatcher.unsoundnessWarning(loc, msg,
		// "Ignored cast!");
		return expr;
	}

	@Override
	public Result visit(Dispatcher main, IASTConditionalExpression node) {
		ILocation loc = LocationFactory.createCLocation(node);
		assert node.getChildren().length == 3;
		Result resLocCond = main.dispatch(node.getLogicalConditionExpression());
		assert resLocCond instanceof ExpressionResult;
		ExpressionResult reLocCond = (ExpressionResult) resLocCond;
		reLocCond = reLocCond.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
		reLocCond.rexIntToBoolIfNecessary(loc, m_ExpressionTranslation, mMemoryHandler);

		Result rPositive = main.dispatch(node.getPositiveResultExpression());
		assert rPositive instanceof ExpressionResult;
		ExpressionResult rePositive = (ExpressionResult) rPositive;
		rePositive = rePositive.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
		rePositive.rexBoolToIntIfNecessary(loc, m_ExpressionTranslation);

		Result rNegative = main.dispatch(node.getNegativeResultExpression());
		assert rNegative instanceof ExpressionResult;
		ExpressionResult reNegative = (ExpressionResult) rNegative;
		reNegative = reNegative.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
		reNegative.rexBoolToIntIfNecessary(loc, m_ExpressionTranslation);
		
		if (rePositive.lrVal.getCType().isArithmeticType() && reNegative.lrVal.getCType().isArithmeticType()) {
			// C11 6.5.15.5: If 2nd and 3rd operand have arithmetic type, 
			// the result type is determined by the usual arithmetic conversions.
			m_ExpressionTranslation.usualArithmeticConversions(loc, rePositive, reNegative);
		}
		
		if ((rePositive.lrVal.getCType().getUnderlyingType() instanceof CPointer) && reNegative.lrVal.getCType().getUnderlyingType().isIntegerType()) {
			m_ExpressionTranslation.convertIntToPointer(loc, reNegative, (CPointer) rePositive.lrVal.getCType().getUnderlyingType());
		}
		if ((reNegative.lrVal.getCType().getUnderlyingType() instanceof CPointer) && rePositive.lrVal.getCType().getUnderlyingType().isIntegerType()) {
			m_ExpressionTranslation.convertIntToPointer(loc, rePositive, (CPointer) reNegative.lrVal.getCType().getUnderlyingType());
		}
		
		
		ArrayList<Statement> stmt = new ArrayList<Statement>();
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>(0);
		List<Overapprox> overappr = new ArrayList<Overapprox>();

		decl.addAll(reLocCond.decl);
		auxVars.putAll(reLocCond.auxVars);
		stmt.addAll(reLocCond.stmt);
		overappr.addAll(reLocCond.overappr);

		String tmpName = mNameHandler.getTempVarUID(SFO.AUXVAR.ITE, new CPrimitive(PRIMITIVE.INT));
		ASTType tmpType = mTypeHandler.ctype2asttype(loc, rePositive.lrVal.getCType());
		VariableDeclaration tmpVar = SFO.getTempVarVariableDeclaration(tmpName, tmpType, loc);

		decl.add(tmpVar);
		auxVars.put(tmpVar, loc);

		RValue condition = (RValue) reLocCond.lrVal;
		List<Statement> ifStatements = new ArrayList<Statement>();
		{
			ifStatements.addAll(rePositive.stmt);
			LeftHandSide[] lhs = { new VariableLHS(loc, tmpName) };
			Expression assignedVal = rePositive.lrVal.getValue();
			if (assignedVal != null) {
				AssignmentStatement assignStmt = new AssignmentStatement(loc, lhs,
						new Expression[] { rePositive.lrVal.getValue() });
				Map<String, IAnnotations> annots = assignStmt.getPayload().getAnnotations();
				for (Overapprox overapprItem : overappr) {
					annots.put(Overapprox.getIdentifier(), overapprItem);
				}
				ifStatements.add(assignStmt);
			}
			decl.addAll(rePositive.decl);
			auxVars.putAll(rePositive.auxVars);
			overappr.addAll(rePositive.overappr);
		}

		List<Statement> elseStatements = new ArrayList<Statement>();
		{
			elseStatements.addAll(reNegative.stmt);
			LeftHandSide[] lhs = { new VariableLHS(loc, tmpName) };
			Expression assignedVal = reNegative.lrVal.getValue();
			if (assignedVal != null) { // if we call a void function, we have to
										// skip this assignment
				AssignmentStatement assignStmt = new AssignmentStatement(loc, lhs, new Expression[] { assignedVal });
				Map<String, IAnnotations> annots = assignStmt.getPayload().getAnnotations();
				for (Overapprox overapprItem : overappr) {
					annots.put(Overapprox.getIdentifier(), overapprItem);
				}
				elseStatements.add(assignStmt);
			}
			decl.addAll(reNegative.decl);
			auxVars.putAll(reNegative.auxVars);
			overappr.addAll(reNegative.overappr);
		}
		Statement ifStatement = new IfStatement(loc, condition.getValue(), ifStatements.toArray(new Statement[0]),
				elseStatements.toArray(new Statement[0]));
		Map<String, IAnnotations> annots = ifStatement.getPayload().getAnnotations();
		for (Overapprox overapprItem : overappr) {
			annots.put(Overapprox.getIdentifier(), overapprItem);
		}
		stmt.add(ifStatement);

		IdentifierExpression tmpExpr = new IdentifierExpression(loc, tmpName);
		return new ExpressionResult(stmt, new RValue(tmpExpr, rePositive.lrVal.getCType()), decl, auxVars, overappr);
	}

	@Override
	public Result visit(Dispatcher main, IASTArraySubscriptExpression node) {
		return mArrayHandler.handleArraySubscriptExpression(main, mMemoryHandler, mStructHandler, node);
	}

	@Override
	public Result visit(Dispatcher main, IASTInitializerClause node) {
		assert node.getChildren().length == 1;
		Result r = main.dispatch(node.getChildren()[0]);
		assert r instanceof ExpressionResult;
		ExpressionResult rex = (ExpressionResult) r;
		return rex.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, LocationFactory.createCLocation(node));
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
		String msg = "Syntax error (statement problem) in C program: " + node.getProblem().getMessage();
		ILocation loc = LocationFactory.createCLocation(node);
		throw new IncorrectSyntaxException(loc, msg);
	}

	@Override
	public Result visit(Dispatcher main, IASTProblemDeclaration node) {
		String msg = "Syntax error (declaration problem) in C program: " + node.getProblem().getMessage();
		ILocation loc = LocationFactory.createCLocation(node);
		throw new IncorrectSyntaxException(loc, msg);
	}

	@Override
	public Result visit(Dispatcher main, IASTProblemExpression node) {
		String msg = "Syntax error (expression problem) in C program: " + node.getProblem().getMessage();
		ILocation loc = LocationFactory.createCLocation(node);
		throw new IncorrectSyntaxException(loc, msg);
	}

	@Override
	public Result visit(Dispatcher main, IASTProblem node) {
		String msg = "Syntax error in C program: " + node.getMessage();
		ILocation loc = LocationFactory.createCLocation(node);
		throw new IncorrectSyntaxException(loc, msg);
	}

	@Override
	public Result visit(Dispatcher main, IASTProblemTypeId node) {
		String msg = "Syntax error (type ID problem) in C program: " + node.getProblem().getMessage();
		ILocation loc = LocationFactory.createCLocation(node);
		throw new IncorrectSyntaxException(loc, msg);
	}

	@Override
	public Result visit(Dispatcher main, IASTTypeIdExpression node) {
		ILocation loc = LocationFactory.createCLocation(node);
		switch (node.getOperator()) {
		case IASTTypeIdExpression.op_sizeof: {
			TypesResult rt = (TypesResult) main.dispatch(node.getTypeId().getDeclSpecifier());
			mCurrentDeclaredTypes.push(rt);
//			main.dispatch(node.getTypeId().getAbstractDeclarator());
			DeclaratorResult dr = (DeclaratorResult) main.dispatch(node.getTypeId().getAbstractDeclarator());
			mCurrentDeclaredTypes.pop();
//			TypesResult checked = checkForPointer(main, node.getTypeId().getAbstractDeclarator().getPointerOperators(),
//					rt, false);

			return new ExpressionResult(new RValue(mMemoryHandler.calculateSizeOf(loc, dr.getDeclaration().getType()), new CPrimitive(
					PRIMITIVE.INT)));
		}
		case IASTTypeIdExpression.op_typeof: {
			TypesResult rt = (TypesResult) main.dispatch(node.getTypeId().getDeclSpecifier());

			mCurrentDeclaredTypes.push(rt);
			DeclaratorResult dr = (DeclaratorResult) main.dispatch(node.getTypeId().getAbstractDeclarator());
			mCurrentDeclaredTypes.pop();

			return dr;
		}
		default:
			break;
		}
		String msg = "Unsupported boogie AST node type: " + node.getClass();
		throw new UnsupportedSyntaxException(loc, msg);
	}
	

    public Result visit(Dispatcher main, IGNUASTCompoundStatementExpression node) {
//    	ArrayList<Statement> stmt = new ArrayList<>();
//    	ArrayList<Declaration> decl = new ArrayList<>();
//    	Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();
//    	ArrayList<Overapprox> overApp = new ArrayList<>();
//    	
//    	LRValue finalResult = null;
    	
//    	CompoundStatementExpressionResult childRes = (CompoundStatementExpressionResult) main.dispatch(node.getCompoundStatement());
    	return main.dispatch(node.getCompoundStatement());
//    	stmt.addAll(childRes.stmt);
//    	decl.addAll(childRes.decl);

//    	return new ExpressionResult(stmt, childRes.lrVal, decl, Collections.<VariableDeclaration, ILocation>emptyMap(), Collections.<Overapprox>emptyList());
//    	return new ExpressionResult(stmt, finalResult, decl, auxVars, overApp);
    }

	/**
		 * Create a havoc statement for each variable in auxVars. (Does not modify
		 * this auxVars map). We insert havocs for auxvars after the translation of
		 * a _statement_. This means that the Expressions carry the auxVarMap
		 * outside (via the ResultExpression they return), and that map is used for
		 * calling this procedure once we reach a (basic) statement.
		 */
		public static List<HavocStatement> createHavocsForAuxVars(Map<VariableDeclaration, ILocation> allAuxVars) {
	//		LinkedHashMap<VariableDeclaration, ILocation> allAuxVars = new LinkedHashMap<>();
	//		//TODO: is this for-loop/are these asserts necessary? -> probably no..
	//		for (Entry<VariableDeclaration, ILocation> e : auxVars.entrySet()) {
	//			assert e.getKey().getVariables().length == 1 
	//					&& e.getKey().getVariables()[0].getIdentifiers().length == 1 
	//					: "we always define only one auxvar at once, right?";
	//			allAuxVars.put(e.getKey(), e.getValue());
	//		}
	
			ArrayList<HavocStatement> result = new ArrayList<HavocStatement>();
			for (VariableDeclaration varDecl : allAuxVars.keySet()) {
				VarList[] varLists = varDecl.getVariables();
				for (VarList varList : varLists) {
					for (String varId : varList.getIdentifiers()) {
						ILocation originloc = allAuxVars.get(varDecl);
						result.add(new HavocStatement(originloc, new VariableLHS[] { new VariableLHS(originloc, varId) }));
					}
				}
			}
			return result;
		}

	/**
	 * Returns true iff all auxvars in decls are contained in auxVars
	 */
	public static boolean isAuxVarMapcomplete(INameHandler nameHandler, 
			List<Declaration> decls, Map<VariableDeclaration, ILocation> auxVars) {
		boolean result = true;
		for (Declaration rExprdecl : decls) {
			assert (rExprdecl instanceof VariableDeclaration);
			VariableDeclaration varDecl = (VariableDeclaration) rExprdecl;
			
			assert varDecl.getVariables().length == 1 
					: "there are never two auxvars declared in one declaration, right??";
			VarList vl = varDecl.getVariables()[0];
			assert vl.getIdentifiers().length == 1
					: "there are never two auxvars declared in one declaration, right??";
			String id = vl.getIdentifiers()[0];
	
			if (nameHandler.isTempVar(id)) {
				//malloc auxvars do not need to be havocced in some cases (alloca)
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
			ArrayList<Declaration> declOld, Map<VariableDeclaration, ILocation> auxVarsOld, List<Overapprox> overapprOld,
			Map<StructLHS, CType> unionFieldsToCType) {
		//we do not want to edit the stmt and so on we are given --> make copies
		ArrayList<Statement> stmt = new ArrayList<>(stmtOld);
		ArrayList<Declaration> decl = new ArrayList<>(declOld);
		LinkedHashMap<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>(auxVarsOld);
		ArrayList<Overapprox> overappr = new ArrayList<>(overapprOld);
		
		//do implicit cast -- assume the types are compatible
		ExpressionResult rExp = new ExpressionResult(stmt, rVal, decl, auxVars, overappr);
		convert(loc, rExp, lrVal.getCType());
		RValue rightHandSide = (RValue) rExp.lrVal;
		
		//for wraparound --> and avoiding it for ints that store pointers
		if (rightHandSide.isIntFromPointer()) {
			if (lrVal instanceof HeapLValue) {
				Expression address = ((HeapLValue) lrVal).getAddress();
				if (address instanceof IdentifierExpression) {
					String lId = ((IdentifierExpression ) ((HeapLValue) lrVal).getAddress()).getIdentifier();
					mSymbolTable.get(mSymbolTable.getCID4BoogieID(lId, loc), loc).isIntFromPointer = true;
				} else {
					//TODO
				}
			} else if (lrVal instanceof LocalLValue){
				String lId = null;
				LeftHandSide value = ((LocalLValue) lrVal).getLHS();
				if (value instanceof VariableLHS) {
					lId = ((VariableLHS) value).getIdentifier();
					mSymbolTable.get(mSymbolTable.getCID4BoogieID(lId, loc), loc).isIntFromPointer = true;
				} else {
					//TODO
				}
			}
		}

		if (lrVal instanceof HeapLValue) {
			HeapLValue hlv = (HeapLValue) lrVal;

			stmt.addAll(mMemoryHandler.getWriteCall(loc, hlv, rightHandSide.getValue(), rightHandSide.getCType()));

			return new ExpressionResult(stmt, rightHandSide, decl, auxVars, overappr);
		} else if (lrVal instanceof LocalLValue) {
			LocalLValue lValue = (LocalLValue) lrVal;
			AssignmentStatement assignStmt = new AssignmentStatement(loc, new LeftHandSide[] { lValue.getLHS() },
					new Expression[] { rightHandSide.getValue() });
			Map<String, IAnnotations> annots = assignStmt.getPayload().getAnnotations();
			for (Overapprox overapprItem : overappr) {
				annots.put(Overapprox.getIdentifier(), overapprItem);
			}
			stmt.add(assignStmt);

			// add havocs if we have a write to a union (which is not on heap,
			// otherwise the heap model should deal with everything)
			if (unionFieldsToCType != null) {
				
//				boolean unionIsFixedSize = true;
//				for (Entry<StructLHS, CType> en : unionFieldsToCType.entrySet())
//					unionIsFixedSize &= mMemoryHandler.calculateSizeOf(rVal.cType, loc) instanceof IntegerLiteral;
//
//				Expression lrValSize = mMemoryHandler.calculateSizeOf(lrVal.cType, loc);
//				unionIsFixedSize &= lrValSize instanceof IntegerLiteral;


				for (Entry<StructLHS, CType> en : unionFieldsToCType.entrySet()) {
					
					//do not havoc when the type of the field is "compatible"
					if (rightHandSide.getCType().equals(en.getValue())
							|| (rightHandSide.getCType().getUnderlyingType() instanceof CPrimitive && en.getValue() instanceof CPrimitive
							 && ((CPrimitive) rightHandSide.getCType().getUnderlyingType()).getGeneralType().equals(((CPrimitive) en.getValue()).getGeneralType())
							 && (mMemoryHandler.calculateSizeOf(loc, rightHandSide.getCType()) 
									 == mMemoryHandler.calculateSizeOf(loc, en.getValue())))) {
						stmt.add(new AssignmentStatement(loc, new LeftHandSide[] { en.getKey() },
								new Expression[] { rightHandSide.getValue() }));
//					} else if (rightHandSide.cType.getUnderlyingType() instanceof CStruct && unionIsFixedSize) {
//						CStruct structType = (CStruct) rightHandSide.cType.getUnderlyingType();
//
//						int lrValSizeInt = Integer.parseInt(((IntegerLiteral) lrValSize).getValue());
//						int currOffset = 0;
//						for (String fId : structType.getFieldIds()) {
//							CType fType = structType.getFieldType(fId).getUnderlyingType();
//							
//							if (currOffset > lrValSizeInt)
//								break;
//
//							currOffset += mMemoryHandler.calculateSizeOfWithGivenTypeSizes(loc, fType);
//							
//
//							String tmpId = mNameHandler.getTempVarUID(SFO.AUXVAR.UNION);
//							VariableDeclaration tVarDec = new VariableDeclaration(loc, new Attribute[0], new VarList[] { new VarList(loc,
//									new String[] { tmpId }, mTypeHandler.ctype2asttype(loc, en.getValue())) });
//							decl.add(tVarDec);
//							auxVars.put(tVarDec, loc); //ensures that the variable will be havoced (necessary only when we are inside a loop)
//
//							stmt.add(new AssignmentStatement(loc, new LeftHandSide[] { en.getKey() },
//									new Expression[] { new IdentifierExpression(loc, tmpId) }));						
//						}

					} else { //otherwise we consider the value undefined, thus havoc it
						// TODO: maybe not use auxiliary variables so lavishly
						String tmpId = mNameHandler.getTempVarUID(SFO.AUXVAR.UNION, en.getValue());
						VariableDeclaration tVarDec = new VariableDeclaration(loc, new Attribute[0], new VarList[] { new VarList(loc,
								new String[] { tmpId }, mTypeHandler.ctype2asttype(loc, en.getValue())) });
						decl.add(tVarDec);
						auxVars.put(tVarDec, loc); //ensures that the variable will be havoced (necessary only when we are inside a loop)

						stmt.add(new AssignmentStatement(loc, new LeftHandSide[] { en.getKey() },
								new Expression[] { new IdentifierExpression(loc, tmpId) }));
					}
				}
			}

			if (!mFunctionHandler.noCurrentProcedure())
				mFunctionHandler.checkIfModifiedGlobal(getSymbolTable(), BoogieASTUtil.getLHSId(lValue.getLHS()), loc);
			return new ExpressionResult(stmt, lValue, decl, auxVars, overappr);
		} else
			throw new AssertionError("Type error: trying to assign to an RValue in Statement" + loc.toString());
	}

	/**
	 * Checks ACSL for the next element and whether it must be added at the
	 * place where this method is called.
	 * 
	 * @param main
	 *            the main dispatcher.
	 * @param stmt
	 *            the statement list where the acsl should be appended - this is
	 *            assumed to be <code>null</code> when called from within the
	 *            <i>translation unit</i>.
	 * @param next
	 *            the current child node of a translation unit of compound
	 *            statement that will be added next. Should be <code>null</code>
	 *            when called at the end of <i>compound statement</i>.
	 * @param parent
	 *            the parent node of the current ACSL node. This should only be
	 *            set if called at the end of a <i>compound statement</i> and
	 *            <code>null</code> otherwise.
	 */
	private void checkForACSL(Dispatcher main, ArrayList<Statement> stmt, ArrayList<Declaration> decl, IASTNode next, IASTNode parent) {
 		if (mAcsl != null) {
			if (next instanceof IASTTranslationUnit) {
				for (ACSLNode globAcsl : mAcsl.mAcsl) {
					if (globAcsl instanceof GlobalLTLInvariant) {
						LTLExpressionExtractor extractor = new LTLExpressionExtractor();
						extractor.run(globAcsl);
						mGlobAcslExtractors.add(extractor);
//						mLogger.info(extractor.getLTLFormatString());
//						Map<String, de.uni_freiburg.informatik.ultimate.model.acsl.ast.Expression> expMap = extractor.getAP2SubExpressionMap();
//						Map<String, Expression> boogieExpMap = new LinkedHashMap<String, Expression>();
//						for (Entry<String, de.uni_freiburg.informatik.ultimate.model.acsl.ast.Expression> en : expMap.entrySet()) {
//							Result r = main.dispatch(en.getValue());
//							boogieExpMap.put(en.getKey(), null);
//						}
						try {
							mAcsl = main.nextACSLStatement();
						} catch (ParseException e1) {
							String msg = "Skipped a ACSL node due to: " + e1.getMessage();
							ILocation loc = LocationFactory.createCLocation(parent);
							main.unsupportedSyntax(loc, msg);
						}
					}
				} //TODO: deal with other global ACSL stuff
			} else if (mAcsl.mSuccessorCNode == null) {
				if (parent != null && stmt != null && next == null) {
					// ACSL at the end of a function or at the end of the last statement in a switch that is not terminated by a break
					// TODO: the latter case needs fixing, the ACSL is inserted outside the corresponding if-scope right now 
					//       example: int s = 1; switch (s) { case 0: s++; //@ assert \false; } will yield a unsafe boogie program
					for (ACSLNode acslNode : mAcsl.mAcsl) {
						if (parent.getFileLocation().getEndingLineNumber() <= acslNode.getStartingLineNumber()) {
							return;// handle later ...
						} else if (parent.getFileLocation().getEndingLineNumber() >= acslNode.getEndingLineNumber()
								&& parent.getFileLocation().getStartingLineNumber() <= acslNode
								.getStartingLineNumber()) {
							Result acslResult = main.dispatch(acslNode);
							if (acslResult instanceof ExpressionResult) {
								decl.addAll(((ExpressionResult) acslResult).decl);
								stmt.addAll(((ExpressionResult) acslResult).stmt);
								stmt.addAll(createHavocsForAuxVars(((ExpressionResult) acslResult).auxVars));
								try {
									mAcsl = main.nextACSLStatement();
								} catch (ParseException e1) {
									String msg = "Skipped a ACSL node due to: " + e1.getMessage();
									ILocation loc = LocationFactory.createCLocation(parent);
									main.unsupportedSyntax(loc, msg);
								}
							} else {
								String msg = "Unexpected ACSL comment: " + acslResult.node.getClass();
								ILocation loc = LocationFactory.createCLocation(parent);
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
				for (ACSLNode acslNode : mAcsl.mAcsl) {
					if (stmt != null) {
						// this means we are in a compound statement
						if (acslNode instanceof Contract || acslNode instanceof LoopAnnot) {
							// Loop contract
							mContract.add(acslNode);
						} else if (acslNode instanceof CodeAnnot) {
							Result acslResult = main.dispatch(acslNode);
							if (acslResult instanceof ExpressionResult) {
								// thrax93
								ExpressionResult re = (ExpressionResult) acslResult;
								stmt.addAll(re.stmt);
								decl.addAll(re.decl);
							} else {
								stmt.add((Statement) acslResult.node);
							}
						} else {
							String msg = "Unexpected ACSL comment: " + acslNode.getClass();
							ILocation loc = LocationFactory.createCLocation(next);
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
				} catch (ParseException e1) {
					String msg = "Skipped a ACSL node due to: " + e1.getMessage();
					ILocation loc = LocationFactory.createCLocation(parent);
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
			ASTType t = mTypeHandler.constructPointerType(null);
			CType cvar = new CPointer(resType.cType);
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
	 * Like {@link CHandler#doPointerArithmetic(int, ILocation, Expression, RValue, CType)}
	 * but additionally the integer operand is converted to the same type
	 * that we use to represent pointer components.
	 * As a consequence we have to return an ExpressionResult.
	 */
	public ExpressionResult doPointerArithmeticWithConversion(Dispatcher main, int operator, ILocation loc, Expression ptrAddress,
			RValue integer, CType valueType) {
		ExpressionResult eres = new ExpressionResult(integer);
		AExpressionTranslation exprTrans = ((CHandler) main.cHandler).getExpressionTranslation();
		exprTrans.convertIntToInt(loc, eres, exprTrans.getCTypeOfPointerComponents());
		Expression resultExpression = mMemoryHandler.doPointerArithmetic(operator, loc, ptrAddress, (RValue) eres.lrVal, valueType);
		eres.lrVal = new RValue(resultExpression, m_ExpressionTranslation.getCTypeOfPointerComponents());
		return eres;
	}
	
	


	/**
	 * Method that handles loops (for, while, do/while). Each of corresponding
	 * visit methods will call this method.
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
		int scopeDepth = mSymbolTable.getActiveScopeNum();
		assert node instanceof IASTWhileStatement || node instanceof IASTDoStatement
				|| node instanceof IASTForStatement;

		ILocation loc = LocationFactory.createCLocation(node);

		ArrayList<Statement> stmt = new ArrayList<Statement>();
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		List<Overapprox> overappr = new ArrayList<Overapprox>();
		Map<VariableDeclaration, ILocation> emptyAuxVars = new LinkedHashMap<VariableDeclaration, ILocation>(0);

		Result iterator = null;
		if (node instanceof IASTForStatement) {
			IASTForStatement forStmt = (IASTForStatement) node;
			// add initialization for this for loop
			IASTStatement cInitStmt = forStmt.getInitializerStatement();
			if (cInitStmt != null) {
				this.beginScope();
				Result initializer = main.dispatch(cInitStmt);
				if (initializer instanceof ExpressionResult) {
					ExpressionResult rExp = (ExpressionResult) initializer;
					stmt.addAll(rExp.stmt);
					decl.addAll(rExp.decl);
					overappr.addAll(rExp.overappr);
				} else if (initializer instanceof SkipResult) {
					// this is an empty statement in the C Code. We will skip it
				} else {
					String msg = "Uninplemented type of for loop initialization: " + initializer.getClass();
					throw new UnsupportedSyntaxException(loc, msg);
				}
			}

			// translate iterator
			IASTExpression cItExpr = forStmt.getIterationExpression();
			if (cItExpr != null)
				iterator = main.dispatch(cItExpr);

			// translate condition
			IASTExpression cCondExpr = forStmt.getConditionExpression();
			if (cCondExpr != null)
				condResult = (ExpressionResult) main.dispatch(cCondExpr);
			else
				condResult = new ExpressionResult(new RValue((new BooleanLiteral(loc, true)), new CPrimitive(
						PRIMITIVE.BOOL), true), new LinkedHashMap<VariableDeclaration, ILocation>(0));

			mInnerMostLoopLabel.push(loopLabel);
			bodyResult = main.dispatch(forStmt.getBody());
			mInnerMostLoopLabel.pop();
		}
		assert (isAuxVarMapcomplete(mNameHandler, condResult.decl, condResult.auxVars));

		ArrayList<Statement> bodyBlock = new ArrayList<Statement>();
		if (bodyResult instanceof ExpressionResult) {
			ExpressionResult re = (ExpressionResult) bodyResult;
			decl.addAll(re.decl);
			overappr.addAll(re.overappr);
			bodyBlock.addAll(re.stmt);
		} else if (bodyResult instanceof Result) {
			if (bodyResult.node instanceof Body) {
				Body body = (Body) (bodyResult.node);
				bodyBlock.addAll(Arrays.asList(body.getBlock()));
				decl.addAll(Arrays.asList(body.getLocalVars()));
			} else if (bodyResult instanceof SkipResult) {
				// do nothing - this is the special case where the loop does
				// not have a body.
			} else {
				String msg = "Error: unexpected dispatch result" + bodyResult.getClass();
				throw new UnsupportedSyntaxException(loc, msg);
			}
		}

		if (node instanceof IASTForStatement && iterator != null) {
			bodyBlock.add(new Label(loc, loopLabel));
			// add iterator statements of this for loop
			if (iterator instanceof ExpressionListResult) {
				for (ExpressionResult el : ((ExpressionListResult) iterator).list) {
					bodyBlock.addAll(el.stmt);
					decl.addAll(el.decl);
//					assert (isAuxVarMapcomplete(main, el.decl, el.auxVars));
					bodyBlock.addAll(createHavocsForAuxVars(el.auxVars));
				}
			} else if (iterator instanceof ExpressionResult) {
				ExpressionResult iteratorRE = (ExpressionResult) iterator;
				bodyBlock.addAll(iteratorRE.stmt);
				decl.addAll(iteratorRE.decl);
				overappr.addAll(iteratorRE.overappr);
				// 2015-11-08 Matthias: assert seems to be wrong here
				// auxVars have already been havoced
//				assert (isAuxVarMapcomplete(main, iteratorRE.decl, iteratorRE.auxVars));
				bodyBlock.addAll(createHavocsForAuxVars(iteratorRE.auxVars));
			} else {
				String msg = "Uninplemented type of loop iterator: " + iterator.getClass();
				throw new UnsupportedSyntaxException(loc, msg);
			}
		}

		condResult = condResult.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
		condResult.rexIntToBoolIfNecessary(loc, m_ExpressionTranslation, mMemoryHandler);
		decl.addAll(condResult.decl);
		RValue condRVal = (RValue) condResult.lrVal;
		IfStatement ifStmt;
		{
			Expression cond = ExpressionFactory.newUnaryExpression(loc, UnaryExpression.Operator.LOGICNEG, condRVal.getValue());
			ArrayList<Statement> thenStmt = new ArrayList<Statement>(
					createHavocsForAuxVars(condResult.auxVars));
			thenStmt.add(new BreakStatement(loc));
			Statement[] elseStmt = createHavocsForAuxVars(condResult.auxVars).toArray(new Statement[0]);
			ifStmt = new IfStatement(loc, cond, thenStmt.toArray(new Statement[0]), elseStmt);
		}

		if (node instanceof IASTWhileStatement || node instanceof IASTForStatement) {
			bodyBlock.add(0, ifStmt);
			bodyBlock.addAll(0, condResult.stmt);
			if (node instanceof IASTWhileStatement)
				bodyBlock.add(0, new Label(loc, loopLabel));
		} else if (node instanceof IASTDoStatement) {
			bodyBlock.add(new Label(loc, loopLabel));
			bodyBlock.addAll(condResult.stmt);
			bodyBlock.add(ifStmt);
		}

		LoopInvariantSpecification[] spec;
		if (mContract == null) {
			spec = new LoopInvariantSpecification[0];
		} else {
			List<LoopInvariantSpecification> specList = new ArrayList<LoopInvariantSpecification>();
			if (node instanceof IASTForStatement) {
				for (int i = 0; i < mContract.size(); i++) {
					// retranslate ACSL specification needed e.g., in cases
					// where ids of function parameters differ from is in ACSL
					// expression
					Result retranslateRes = main.dispatch(mContract.get(i));
					if (retranslateRes instanceof ContractResult) {
						ContractResult resContr = (ContractResult) retranslateRes;
						assert resContr.specs.length == 1;
						for (Specification cSpec : resContr.specs) {
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

				this.endScope();
			}
		}

		ILocation ignoreLocation = LocationFactory.createIgnoreCLocation(node);
		WhileStatement whileStmt = new WhileStatement(ignoreLocation, 
				new BooleanLiteral(ignoreLocation, true), spec,
				bodyBlock.toArray(new Statement[0]));
		Map<String, IAnnotations> annots = whileStmt.getPayload().getAnnotations();
		for (Overapprox overapprItem : overappr) {
			annots.put(Overapprox.getIdentifier(), overapprItem);
		}
		stmt.add(whileStmt);

		assert (mSymbolTable.getActiveScopeNum() == scopeDepth);
		return new ExpressionResult(stmt, null, decl, emptyAuxVars, overappr);
	}

	@Override
	public boolean isHeapVar(String boogieId) {
		CStorageClass c;
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
		Result r = main.dispatch(node.getDeclSpecifier());
		assert r instanceof TypesResult;
		TypesResult rt = (TypesResult) r;
		assert rt.cType instanceof CEnum;
		CEnum cEnum = (CEnum) rt.cType;
		ILocation loc = LocationFactory.createCLocation(node);
        CPrimitive intType = new CPrimitive(PRIMITIVE.INT);
        ASTType at = mTypeHandler.ctype2asttype(loc, intType); 
		String enumId = cEnum.getIdentifier();
		Expression oldValue = null;
		Expression[] enumDomain = new Expression[cEnum.getFieldCount()];
		
		// C standard says: "The identifiers in an enumerator list are declared 
		// as constants that have type int ..."
		CPrimitive typeOfEnumIdentifiers = new CPrimitive(CPrimitive.PRIMITIVE.INT);

		//ResultDeclaration result = new ResultDeclaration();
		for (int i = 0; i < cEnum.getFieldCount(); i++) {
			String fId = cEnum.getFieldIds()[i];
			String bId = enumId + "~" + fId;
			VarList vl = new VarList(loc, new String[] { bId }, at);
			ConstDeclaration cd = new ConstDeclaration(loc, new Attribute[0], false, vl, null, false);
			mDeclarationsGlobalInBoogie.put(cd, new CDeclaration(cEnum, fId));
			Expression l = new IdentifierExpression(loc, bId);
			Expression newValue = oldValue;
			if (oldValue == null && cEnum.getFieldValue(fId) == null) {
				Expression zero = m_ExpressionTranslation.constructLiteralForIntegerType(
						loc, typeOfEnumIdentifiers, BigInteger.ZERO);
				newValue = zero;  
			} else if (cEnum.getFieldValue(fId) == null) {
				Expression one = m_ExpressionTranslation.constructLiteralForIntegerType(
						loc, typeOfEnumIdentifiers, BigInteger.ONE);
				newValue = m_ExpressionTranslation.constructArithmeticExpression(
						loc, IASTBinaryExpression.op_plus, oldValue, typeOfEnumIdentifiers, one, typeOfEnumIdentifiers); 
			} else {
				newValue = cEnum.getFieldValue(fId);
			}
			oldValue = newValue;
			enumDomain[i] = newValue;
			mAxioms.add(new Axiom(loc, new Attribute[0], ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, l, newValue)));
			mSymbolTable.put(fId, new SymbolTableValue(bId, cd, 
					new CDeclaration(typeOfEnumIdentifiers, fId, scConstant2StorageClass(node.getDeclSpecifier().getStorageClass())),
					true, node)); // FIXME ??
		}
		//return result;
	}

	public Result handleLabelCommonCode(Dispatcher main, IASTLabelStatement node, ILocation loc) {

		ArrayList<Statement> stmt = new ArrayList<Statement>();
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		Map<VariableDeclaration, ILocation> emptyAuxVars = new LinkedHashMap<VariableDeclaration, ILocation>(0);
		List<Overapprox> overappr = new ArrayList<Overapprox>();
		String label = node.getName().toString();
		stmt.add(new Label(loc, label));
		Result r = main.dispatch(node.getNestedStatement());
		if (r instanceof ExpressionResult) {
			ExpressionResult res = (ExpressionResult) r;
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
				Body b = ((Body) r.node);
				decl.addAll(Arrays.asList(b.getLocalVars()));
				stmt.addAll(Arrays.asList(b.getBlock()));
			} else {
				String msg = "Unexpected boogie AST node type: " + r.node.getClass();
				throw new UnsupportedSyntaxException(loc, msg);
			}
			return new ExpressionResult(stmt, expr, decl, emptyAuxVars, overappr);
		}
	}

	/**
	 * m_declarationsGlobalInBoogie may contain type declarations that stem from
	 * typedefs using an incomplete struct type. This method is called when the
	 * struct type is completed.
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
		for (Entry<Declaration, CDeclaration> en : mDeclarationsGlobalInBoogie.entrySet()) {
			if (en.getValue().getType().toString().equals(incompleteStruct.toString())) {
				oldDec = (TypeDeclaration) en.getKey();
				oldCDec = en.getValue();
				newDec = new TypeDeclaration(oldDec.getLocation(), oldDec.getAttributes(), oldDec.isFinite(),
						oldDec.getIdentifier(), oldDec.getTypeParams(), mTypeHandler.ctype2asttype(oldDec.getLocation(),
								cvar));
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
	public SymbolTable getSymbolTable() {
		return mSymbolTable;
	}

	@Override
	public void clearContract() {
		this.mContract.clear();
	}

	public static Expression convertLHSToExpression(LeftHandSide lhs) {
		if (lhs instanceof VariableLHS) {
			return new IdentifierExpression(lhs.getLocation(), ((VariableLHS) lhs).getIdentifier());
		} else if (lhs instanceof ArrayLHS) {
			ArrayLHS alhs = (ArrayLHS) lhs;
			Expression array = convertLHSToExpression(alhs.getArray());
			return new ArrayAccessExpression(alhs.getLocation(), alhs.getType(), array, alhs.getIndices());
		} else if (lhs instanceof StructLHS) {
			StructLHS slhs = (StructLHS) lhs;
			Expression struct = convertLHSToExpression(slhs.getStruct());
			return new StructAccessExpression(slhs.getLocation(), slhs.getType(), struct, slhs.getField());
		} else {
			throw new AssertionError("Strange LeftHandSide " + lhs);
		}
	}

	public void beginScope() {
		this.mTypeHandler.beginScope();
		this.mSymbolTable.beginScope();
		this.mMemoryHandler.getVariablesToBeMalloced().beginScope();
		this.mMemoryHandler.getVariablesToBeFreed().beginScope();
	}

	public void endScope() {
		this.mTypeHandler.endScope();
		this.mSymbolTable.endScope();
		this.mMemoryHandler.getVariablesToBeMalloced().endScope();
		this.mMemoryHandler.getVariablesToBeFreed().endScope();
	}

	/**
	 * Handle conversions according to Section 6.3 of C11. 
	 * @param loc
	 * @param rexp
	 * @param newTypeRaw
	 */
	@Override
	public void convert(ILocation loc, ExpressionResult rexp, CType newTypeRaw) {
		RValue rValIn = (RValue) rexp.lrVal;
		CType newType = newTypeRaw.getUnderlyingType();
		CType oldType = rValIn.getCType().getUnderlyingType();
		if (oldType.equals(newType)) {
			return;
		}
		
		if (newType instanceof CPrimitive) {
			CPrimitive cPrimitive = (CPrimitive) newType;
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

	private void convertToIntegerType(ILocation loc, 
			ExpressionResult rexp, CPrimitive newType) {
		assert (rexp.lrVal instanceof RValue) : "has to be converted to RValue";
		CType oldType = rexp.lrVal.getCType().getUnderlyingType();
		if (oldType instanceof CPrimitive) {
			CPrimitive cPrimitive = (CPrimitive) oldType;
			if (cPrimitive.isIntegerType()) {
				m_ExpressionTranslation.convertIntToInt(loc, rexp, newType);
			} else if (cPrimitive.isRealFloatingType()) {
				m_ExpressionTranslation.convertFloatToInt(loc, rexp, newType);
			} else if (cPrimitive.getType().equals(PRIMITIVE.VOID)) {
				throw new IncorrectSyntaxException(loc, "cannot convert from void");
			} else {
				throw new AssertionError("unknown type " + newType);
			}
		} else if (oldType instanceof CPointer) {
			m_ExpressionTranslation.convertPointerToInt(loc, rexp, newType);
		} else if (oldType instanceof CEnum) {
			m_ExpressionTranslation.convertIntToInt(loc, rexp, newType);
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
	
	private void convertToFloatingType(ILocation loc, 
			ExpressionResult rexp, CPrimitive newType) {
		assert (rexp.lrVal instanceof RValue) : "has to be converted to RValue";
		CType oldType = rexp.lrVal.getCType().getUnderlyingType();
		if (oldType instanceof CPrimitive) {
			CPrimitive cPrimitive = (CPrimitive) oldType;
			if (cPrimitive.isIntegerType()) {
				m_ExpressionTranslation.convertIntToFloat(loc, rexp, newType);
			} else if (cPrimitive.isRealFloatingType()) {
				m_ExpressionTranslation.convertFloatToFloat(loc, rexp, newType);
			} else if (cPrimitive.getType().equals(PRIMITIVE.VOID)) {
				throw new IncorrectSyntaxException(loc, "cannot convert from void");
			} else {
				throw new AssertionError("unknown type " + newType);
			}
		} else if (oldType instanceof CPointer) {
			throw new IncorrectSyntaxException(loc, "cannot convert pointer to float");
		} else if (oldType instanceof CEnum) {
			m_ExpressionTranslation.convertIntToFloat(loc, rexp, newType);
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
	
	private void convertToVoid(ILocation loc, 
			ExpressionResult rexp, CPrimitive newType) {
		assert (rexp.lrVal instanceof RValue) : "has to be converted to RValue";
		CType oldType = rexp.lrVal.getCType().getUnderlyingType();
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
		RValue oldRValue = (RValue) rexp.lrVal;
		RValue resultRvalue = new RValue(oldRValue.getValue(), newType, 
				oldRValue.isBoogieBool(), oldRValue.isIntFromPointer());
		rexp.lrVal = resultRvalue;
	}
	
	
	private void convertToPointer(ILocation loc, 
			ExpressionResult rexp, CPointer newType) {
		assert (rexp.lrVal instanceof RValue) : "has to be converted to RValue";
		CType oldType = rexp.lrVal.getCType().getUnderlyingType();
		if (oldType instanceof CPrimitive) {
			CPrimitive cPrimitive = (CPrimitive) oldType;
			if (cPrimitive.isIntegerType()) {
				m_ExpressionTranslation.convertIntToPointer(loc, rexp, newType);
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
			m_ExpressionTranslation.convertIntToPointer(loc, rexp, newType);
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
	
	
	private void convertPointerToPointer(ILocation loc, 
			ExpressionResult rexp, CPointer newType) {
		// TODO: check if types are compatible
		assert (rexp.lrVal instanceof RValue) : "has to be converted to RValue";
		RValue oldRvalue = (RValue) rexp.lrVal;
		assert oldRvalue.getCType() instanceof CPointer : "has to be pointer";
		RValue newRvalue = new RValue(oldRvalue.getValue(), newType);
		rexp.lrVal = newRvalue;
	}

	@Override
	@Deprecated
	/* Matthias 2015-09-21: "premature optimization is the root of all evil"
	 * I think, by now we should not use this method and better live with
	 * long expressions.
	 * However, I don't want to delete this method, we might want to use
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
}	