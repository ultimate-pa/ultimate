/**
 * The base C handler implementation.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.math.BigInteger;
import java.text.ParseException;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Stack;

import javax.print.DocFlavor.STRING;

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
import org.eclipse.cdt.core.dom.ast.IASTEnumerationSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTEqualsInitializer;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTExpressionList;
import org.eclipse.cdt.core.dom.ast.IASTExpressionStatement;
import org.eclipse.cdt.core.dom.ast.IASTFieldDeclarator;
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
import org.eclipse.cdt.internal.core.dom.parser.c.CASTDeclarator;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTDesignatedInitializer;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTFunctionDeclarator;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.SymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.ArrayHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.CastAndConversionHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.FunctionHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.InitializationHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.LocalLValueILocationPair;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.PostProcessor;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.StructHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.SymbolTableValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.SymbolTableValue.StorageClass;
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
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultContract;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultExpression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultExpressionList;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultExpressionListRec;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultSkip;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultTypes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.BoogieASTUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.ConvExpr;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.ISOIEC9899TC3;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO.AUXVAR;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ICHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.CodeAnnot;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Contract;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.GlobalLTLInvariant;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopAnnot;
import de.uni_freiburg.informatik.ultimate.model.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.annotation.Overapprox;
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
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructConstructor;
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
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.UNSIGNED_TREATMENT;
import de.uni_freiburg.informatik.ultimate.result.Check;
import de.uni_freiburg.informatik.ultimate.result.LTLPropertyCheck;
import de.uni_freiburg.informatik.ultimate.result.Check.Spec;
import de.uni_freiburg.informatik.ultimate.result.LTLPropertyCheck.CheckableExpression;

/**
 * Class that handles translation of C nodes to Boogie nodes.
 * 
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 01.02.2012
 */
public class CHandler implements ICHandler {

	//the CHandler knows all its different Handlers..
	protected ArrayHandler mArrayHandler;
	
	protected FunctionHandler mFunctionHandler;
	
	protected StructHandler mStructHandler;
	
	public MemoryHandler mMemoryHandler;
	
	protected PostProcessor mPostProcessor;

	protected ITypeHandler mTypeHandler;
	
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
	 * Names of all bitwise operation that occurred in the program.
	 */
	protected LinkedHashMap<String, FunctionDeclaration> mFunctions;
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
	protected ArrayDeque<ResultTypes> mCurrentDeclaredTypes;

	/**
	 * Stores the labels of the loops we are currently inside. (For translation
	 * of a possible continue statement)
	 */
	Stack<String> mInnerMostLoopLabel;
	private Logger mLogger;
	
	CACSLPreferenceInitializer.UNSIGNED_TREATMENT mUnsignedTreatment;

	private ArrayList<LTLExpressionExtractor> mGlobAcslExtractors;


	/**
	 * Constructor.
	 * 
	 * @param main
	 *            a reference to the main dispatcher.
	 * @param backtranslator
	 *            a reference to the Backtranslator object.
	 */
	public CHandler(Dispatcher main, CACSL2BoogieBacktranslator backtranslator, boolean errorLabelWarning,
			Logger logger, ITypeHandler typeHandler) {

		mLogger = logger;
		this.mTypeHandler = typeHandler;

		
		this.mUnsignedTreatment = main.mPreferences.getEnum(CACSLPreferenceInitializer.LABEL_UNSIGNED_TREATMENT, 
				CACSLPreferenceInitializer.UNSIGNED_TREATMENT.class);

		this.mArrayHandler = new ArrayHandler();
		this.mFunctionHandler = new FunctionHandler();
		this.mStructHandler = new StructHandler();
		boolean checkPointerValidity = main.mPreferences.getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_POINTER_VALIDITY);
		this.mMemoryHandler = new MemoryHandler(mFunctionHandler, checkPointerValidity);
		this.mInitHandler = new InitializationHandler(mFunctionHandler, mStructHandler, mMemoryHandler);
		this.mPostProcessor = new PostProcessor(main, mLogger);
		
		this.mSymbolTable = new SymbolTable(main);
		this.mFunctions = new LinkedHashMap<String, FunctionDeclaration>();
		this.mDeclarationsGlobalInBoogie = new LinkedHashMap<Declaration, CDeclaration>();
		this.mAxioms = new LinkedHashSet<Axiom>();
		this.mBacktranslator = backtranslator;
		this.mContract = new ArrayList<ACSLNode>();
		this.mErrorLabelWarning = errorLabelWarning;
		this.mInnerMostLoopLabel = new Stack<String>();

		this.mBoogieIdsOfHeapVars = new LinkedHashSet<String>();
		this.mCurrentDeclaredTypes = new ArrayDeque<ResultTypes>();
		
		this.mGlobAcslExtractors = new ArrayList<>();
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
			if (!(r instanceof ResultSkip)) {
				throw new UnsupportedOperationException("Not yet implemented");
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

		checkForACSL(main, null, node, null);

		for (IASTNode child : node.getChildren()) {
			checkForACSL(main, null, child, null);
			Result childRes = main.dispatch(child);

			if (childRes instanceof ResultDeclaration) {
				// we have to add a global variable
				ResultDeclaration rd = (ResultDeclaration) childRes;
				for (CDeclaration cd : rd.getDeclarations()) {
					mDeclarationsGlobalInBoogie.put(mSymbolTable.getBoogieDeclOfResultDecl(cd), cd);
				}
			} else {
				if (childRes instanceof ResultSkip)
					continue;
				assert childRes.getClass() == Result.class;
				assert childRes.node != null;
				decl.add((Declaration) childRes.node);
			}
		}

		//(alex:) new function pointers
		for (Entry<String, Integer> en : ((MainDispatcher) main).getFunctionToIndex().entrySet()) {
			String funcId = SFO.FUNCTION_ADDRESS + en.getKey();
			VarList varList = new VarList(loc, new String[]{ funcId }, MemoryHandler.POINTER_TYPE);
			decl.add(new ConstDeclaration(loc, new Attribute[0], false, varList, null, false));//would unique make sense here?? -- would potentially add lots of axioms
			decl.add(new Axiom(loc, new Attribute[0], new BinaryExpression(loc, 
					BinaryExpression.Operator.COMPEQ, 
					new IdentifierExpression(loc, funcId), 
					MemoryHandler.constructPointerFromBaseAndOffset(
							new IntegerLiteral(loc, "-1"), 
							new IntegerLiteral(loc, en.getValue().toString()), loc))));
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

		decl.addAll(mPostProcessor.postProcess(main, loc, mMemoryHandler, mArrayHandler, mFunctionHandler, mStructHandler,
				main.typeHandler.getUndefinedTypes(), this.mFunctions.values(), mDeclarationsGlobalInBoogie));

		// this has to happen after postprocessing as pping may add sizeof
		// constants for initializations
		decl.addAll(mMemoryHandler.declareMemoryModelInfrastructure(main, loc));

		// handle proc. declaration & resolve their transitive modified globals
		decl.addAll(mFunctionHandler.calculateTransitiveModifiesClause(main, mMemoryHandler));
		
		//handle global ACSL stuff
		//TODO: do it!
		
		checkForACSL(main, null, node, null);

		//the overall translation result:
	    Unit boogieUnit = new Unit(loc, decl.toArray(new Declaration[0]));
		
	    //annotate the Unit with LTLPropertyChecks if applicable
		for (LTLExpressionExtractor ex : mGlobAcslExtractors) {
			Map<String, LTLPropertyCheck.CheckableExpression> checkableAtomicPropositions = new LinkedHashMap<String, LTLPropertyCheck.CheckableExpression>();

			for (Entry<String, de.uni_freiburg.informatik.ultimate.model.acsl.ast.Expression> en : ex.getAP2SubExpressionMap().entrySet()) {
				Result r = main.dispatch(en.getValue());
				checkableAtomicPropositions.put(en.getKey(), new CheckableExpression((Expression) r.node, null));
			}
			LTLPropertyCheck propCheck = new LTLPropertyCheck(ex.getLTLFormatString(), checkableAtomicPropositions, null);
			propCheck.annotate(boogieUnit);
		}
		
		return new Result(boogieUnit);
	}

	@Override
	public Result visit(Dispatcher main, IASTFunctionDefinition node) {
		LinkedHashSet<IASTDeclaration> reachableDecs = ((MainDispatcher) main).getReachableDeclarationsOrDeclarators();
		if (reachableDecs != null) {
			if (!reachableDecs.contains(node))
				return new ResultSkip();
		}

		ResultTypes resType = (ResultTypes) main.dispatch(node.getDeclSpecifier());

		mCurrentDeclaredTypes.push(resType);
		ResultDeclaration declResult = (ResultDeclaration) main.dispatch(node.getDeclarator());
		mCurrentDeclaredTypes.pop();
		return mFunctionHandler.handleFunctionDefinition(main, mMemoryHandler, node, declResult.getDeclarations().get(0),
				mContract);
	}

	@Override
	public Result visit(Dispatcher main, IASTCompoundStatement node) {
		ILocation loc = LocationFactory.createCLocation(node);
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		ArrayList<VariableDeclaration> lVarDecl = new ArrayList<VariableDeclaration>();
		ArrayList<Statement> stmt = new ArrayList<Statement>();
		IASTNode parent = node.getParent();

		if (isNewScopeRequired(parent)) {
			this.beginScope();
		}

		for (IASTNode child : node.getChildren()) {
			checkForACSL(main, stmt, child, null);
			Result r = main.dispatch(child);
			if (r instanceof ResultExpression) {
				ResultExpression res = (ResultExpression) r;
				// assert (res.auxVars.isEmpty()) : "unhavoced auxvars";
				for (Declaration d : res.decl) {
					if (d instanceof VariableDeclaration) {
						lVarDecl.add((VariableDeclaration) d);
					}
				}
				decl.addAll(res.decl);
				stmt.addAll(res.stmt);
			}
			if (r.node != null && r.node instanceof Body) {
				// already have a unique naming for variables! --> unfold
				Body b = ((Body) r.node);
				decl.addAll(Arrays.asList(b.getLocalVars()));
				stmt.addAll(Arrays.asList(b.getBlock()));
			}
		}
		checkForACSL(main, stmt, null, node);
		if (isNewScopeRequired(parent)) {
			stmt = mMemoryHandler.insertMallocs(main, stmt);
			for (SymbolTableValue stv : mSymbolTable.currentScopeValues()) {
				if (!stv.isBoogieGlobalVar()) {
					decl.add(stv.getBoogieDecl());
				}
			}

			this.endScope();
		}
		return new Result(new Body(loc, decl.toArray(new VariableDeclaration[0]), stmt.toArray(new Statement[0])));
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
		LinkedHashSet<IASTDeclaration> reachableDecs = ((MainDispatcher) main).getReachableDeclarationsOrDeclarators();
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
						return new ResultSkip();
				}
			}
		}

		ILocation loc = LocationFactory.createCLocation(node);
		if (node.getDeclSpecifier() == null) {
			String msg = "This statement can be removed!";
			main.warn(loc, msg);
			return new ResultSkip();
		}

		// enum case
		if (node.getDeclSpecifier() instanceof IASTEnumerationSpecifier) {
			return handleEnumDeclaration(main, node);
		}

		Result r = main.dispatch(node.getDeclSpecifier());
		assert r instanceof ResultSkip || r instanceof ResultTypes;
		if (r instanceof ResultSkip)
			return r;
		if (r instanceof ResultTypes) {
			ResultTypes resType = (ResultTypes) r;
			Result result = new ResultSkip(); // Skip will be overwritten in
												// case of a global or a local
												// initialized variable

			StorageClass storageClass = scConstant2StorageClass(node.getDeclSpecifier().getStorageClass());

			mCurrentDeclaredTypes.push(resType);
			/**
			 * Christian: C allows several declarations of "similar" types in
			 * one go. For instance: <code>int a, b[2];</code> Here
			 * <code>a</code> has type <code>int</code> and <code>b</code> has
			 * type <code>int[]</code>. To solve this, the declaration items are
			 * visited one after another.
			 */
			for (IASTDeclarator d : node.getDeclarators()) {
				if (d instanceof IASTFieldDeclarator)
					throw new UnsupportedSyntaxException(loc, "bitfields are not supported at the moment");
	
				ResultDeclaration declResult = (ResultDeclaration) main.dispatch(d);

				// the ResultDeclaration from one Declarator always only
				// contains one CDeclaration, right?
				// or at most one??
				assert declResult.getDeclarations().size() == 1;
				CDeclaration cDec = declResult.getDeclarations().get(0);

				// update symbol table

				// functions keep their cId, and their declaration is not stored
				// in the symbolTable but in
				// FunctionHandler.procedures.
				if (cDec.getType() instanceof CFunction && storageClass != StorageClass.TYPEDEF) {
					// update functionHandler.procedures instead of symbol table
					mFunctionHandler.handleFunctionDeclarator(main, LocationFactory.createCLocation(d), mContract, cDec);
					continue;
				}

				boolean onHeap = cDec.isOnHeap();
				String bId = main.nameHandler.getUniqueIdentifier(node, cDec.getName(),
						mSymbolTable.getCompoundCounter(), onHeap);
				if (onHeap)
					mBoogieIdsOfHeapVars.add(bId);

				Declaration boogieDec = null;
				boolean globalInBoogie = false;

				// this .put() is only to have a minimal symbolTableEntry
				// (containing boogieID) for
				// translation of the initializer
				mSymbolTable.put(cDec.getName(),
						new SymbolTableValue(bId, boogieDec, cDec, globalInBoogie, storageClass));
				cDec.translateInitializer(main);

				ASTType translatedType = null;
				if (onHeap)
					translatedType = MemoryHandler.POINTER_TYPE;
				else
					translatedType = main.typeHandler.ctype2asttype(loc, cDec.getType());

				if (storageClass == StorageClass.TYPEDEF) {
					boogieDec = new TypeDeclaration(loc, new Attribute[0], false, bId, new String[0], translatedType);
					main.typeHandler.addDefinedType(bId, new ResultTypes(new NamedType(loc, cDec.getName(), null),
							false, false, cDec.getType()));
					// TODO: add a sizeof-constant for the type??
					globalInBoogie = true;
					mDeclarationsGlobalInBoogie.put(boogieDec, cDec);
				} else if (storageClass == StorageClass.STATIC && !mFunctionHandler.noCurrentProcedure()) {
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
							!(cDec.getType() instanceof CArray && !(cDec.getInitializer() instanceof ResultExpressionListRec));

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
						assert result instanceof ResultSkip || result instanceof ResultExpression;

						if (result instanceof ResultSkip)
							result = new ResultExpression((LRValue) null);

						VariableLHS lhs = new VariableLHS(loc, bId);

						if (cDec.hasInitializer()) { //must be a non-real initializer for variable length array size --> need to pass this on
								((ResultExpression) result).decl.addAll(cDec.getInitializer().decl);
								((ResultExpression) result).stmt.addAll(cDec.getInitializer().stmt);
								((ResultExpression) result).auxVars.putAll(cDec.getInitializer().auxVars);
						}
							
						//no initializer --> essentially needs to be havoced f.i. in each loop iteration
						if (!onHeap) {
							((ResultExpression) result).stmt.add(
									new HavocStatement(loc, new VariableLHS[] { lhs }));
						} else {
							String tmpId = main.nameHandler.getTempVarUID(SFO.AUXVAR.NONDET);
							LocalLValue llVal = new LocalLValue(lhs, cDec.getType());
//							((ResultExpression) result).stmt.add(mMemoryHandler.getMallocCall(main, mFunctionHandler, 
//									mMemoryHandler.calculateSizeOf(cDec.getType(), loc), llVal , loc));
							VariableDeclaration tmpVarDec = new VariableDeclaration(loc, new Attribute[0], 
									new VarList[] { new VarList(loc, new String[] { tmpId }, 
											main.typeHandler.ctype2asttype(loc, cDec.getType())) });
							((ResultExpression) result).decl.add(tmpVarDec);
							((ResultExpression) result).stmt.addAll(mMemoryHandler.getWriteCall(loc, 
									new HeapLValue(new IdentifierExpression(loc, bId), cDec.getType()), 
									new RValue(new IdentifierExpression(loc, tmpId), cDec.getType())));
							((ResultExpression) result).auxVars.put(tmpVarDec, loc);

							mMemoryHandler.addVariableToBeMallocedAndFreed(main, 
									new LocalLValueILocationPair(llVal, LocationFactory.createIgnoreLocation(loc)));
						}
					} else if (hasRealInitializer && !mFunctionHandler.noCurrentProcedure() && !mTypeHandler.isStructDeclaration()) { 
						//in case of a local variable declaration with an initializer, the statements and delcs
						// necessary for the initialization are the result
						assert result instanceof ResultSkip || result instanceof ResultExpression;
						VariableLHS lhs = new VariableLHS(loc, bId);
						ResultExpression initRex = 
								mInitHandler.initVar(loc, main, 
										lhs, cDec.getType(),
										cDec.getInitializer());
						if (result instanceof ResultSkip)
							result = new ResultExpression((LRValue) null);
						
						if (onHeap) {
							LocalLValue llVal = new LocalLValue(lhs, cDec.getType());
							mMemoryHandler.addVariableToBeMallocedAndFreed(main, new LocalLValueILocationPair(llVal, loc));
						}

						((ResultExpression) result).stmt.addAll(initRex.stmt);
						((ResultExpression) result).stmt.addAll(createHavocsForNonMallocAuxVars(initRex.auxVars));
						((ResultExpression) result).decl.addAll(initRex.decl);
						((ResultExpression) result).overappr.addAll(initRex.overappr);
					} else {
						// in case of global variables, the result is the
						// declaration, initialization is
						// done in the postProcessor
						// in case this simpleDeclaration is part of a struct
						// definition, we also need the
						// Declarations as a result
						assert result instanceof ResultSkip || result instanceof ResultDeclaration;
						if (result instanceof ResultSkip)
							result = new ResultDeclaration();
						((ResultDeclaration) result).addDeclaration(cDec);
					}
					boogieDec = new VariableDeclaration(loc, new Attribute[0], new VarList[] { new VarList(loc,
							new String[] { bId }, translatedType) });
					globalInBoogie |= mFunctionHandler.noCurrentProcedure();
				}

				mSymbolTable.put(cDec.getName(), new SymbolTableValue(bId,
						boogieDec, cDec, globalInBoogie,
						storageClass)); 
			}
			mCurrentDeclaredTypes.pop();
			
			if (result instanceof ResultExpression)
				((ResultExpression) result).stmt.addAll(
						Dispatcher.createHavocsForAuxVars(((ResultExpression) result).auxVars));
			return result;
		}
		String msg = "Unknown result type: " + r.getClass();
		throw new UnsupportedSyntaxException(loc, msg);
	}

	@Override
	public Result visit(Dispatcher main, IASTParameterDeclaration node) {
		ResultTypes resType = (ResultTypes) main.dispatch(node.getDeclSpecifier());

		mCurrentDeclaredTypes.push(resType);
		ResultDeclaration declResult = (ResultDeclaration) main.dispatch(node.getDeclarator());
		mCurrentDeclaredTypes.pop();
		return declResult;
	}

	@Override
	public Result visit(Dispatcher main, IASTDeclarator node) {
		ILocation loc = LocationFactory.createCLocation(node);
		ResultTypes resType = mCurrentDeclaredTypes.peek();
		ResultTypes newResType = new ResultTypes(resType);

		newResType.isOnHeap |= main instanceof MainDispatcher 
				? ((MainDispatcher) main).getVariablesForHeap().contains(node)
						 : false; //in this case we are in the PRDispatcher

		IASTPointerOperator[] pointerOps = node.getPointerOperators();
		for (int i = 0; i < pointerOps.length; i++) {
			newResType.cType = new CPointer(newResType.cType);
		}
		ResultExpression variableLengthArrayAuxVarInitializer = null;
		if (node instanceof IASTArrayDeclarator) {
			IASTArrayDeclarator arrDecl = (IASTArrayDeclarator) node;

			boolean variableLength = false;
			ArrayList<Expression> sizeConstants = new ArrayList<Expression>();
			Expression overallSize = new IntegerLiteral(loc, "1");
			for (IASTArrayModifier am : arrDecl.getArrayModifiers()) {
				ResultExpression constEx = null;
				if (am.getConstantExpression() != null) {
					constEx = (ResultExpression) main.
							dispatch(am.getConstantExpression());
				//the innermost array modifier may be empty, if there is an initializer; like int a[1][2][] = {...}
				} else if (am.getConstantExpression() == null && 
						arrDecl.getArrayModifiers()[arrDecl.getArrayModifiers().length - 1] == am) {
					if (arrDecl.getInitializer() != null) {
						assert arrDecl.getInitializer() instanceof IASTEqualsInitializer;
						IASTEqualsInitializer eqInit = ((IASTEqualsInitializer) arrDecl.getInitializer());
						assert eqInit.getInitializerClause() instanceof IASTInitializerList;
						IASTInitializerList initList = (IASTInitializerList) eqInit.getInitializerClause();
						constEx = new ResultExpression(new RValue(new IntegerLiteral(loc, new Integer(
								initList.getSize()).toString()), new CPrimitive(PRIMITIVE.INT)));
					} else { // we have an incomplete array type without an
								// initializer -- this may happen in a function
								// parameter..
						variableLength = true;
						constEx = new ResultExpression(new RValue(new IntegerLiteral(loc, "-1"), new CPrimitive(
								PRIMITIVE.INT)));
					}
				} else {
					throw new IncorrectSyntaxException(loc, "wrong array type in declaration");
				}

				constEx = constEx.switchToRValueIfNecessary(main, // just to be
																	// safe..
						mMemoryHandler, mStructHandler, loc);
				sizeConstants.add(constEx.lrVal.getValue());
				overallSize = CHandler.createArithmeticExpression(IASTBinaryExpression.op_multiply, 
						overallSize, constEx.lrVal.getValue(), loc);
				//if all dimensions are given as integer literals, createArithmeticExpression(..) should return an integer literal
				// otherwise we have a variable length array
				if (!(overallSize instanceof IntegerLiteral))
					variableLength = true;
			}
			CArray arrayType = null;

			if (variableLength) {
				if (!(overallSize instanceof IntegerLiteral)) { //size is given but variable --> a real variable length array
					//introduce a new auxiliary variable storing the size of the array 
					//(the variable used may change independently from the array)

					ArrayList<Statement> initStmts = new ArrayList<>();
					ArrayList<Declaration> initDecls = new ArrayList<>();
					HashMap<VariableDeclaration, ILocation> initAuxVars = new HashMap<>();
					
					ArrayList<Expression> sizeExpressions = new ArrayList<>();

					for (Expression sc : sizeConstants) {
						if (!(sc instanceof IntegerLiteral)) {
							String tmpName = main.nameHandler.getTempVarUID(SFO.AUXVAR.ARRAYDIM);
							VariableDeclaration tmpVar = SFO.getTempVarVariableDeclaration(tmpName, new PrimitiveType(loc, SFO.INT) , loc);

							initStmts.add(new AssignmentStatement(loc, 
									new LeftHandSide[] { new VariableLHS(loc, tmpName) }, new Expression[] { overallSize }));
							initDecls.add(tmpVar);
							initAuxVars.put(tmpVar, loc);					
							sizeExpressions.add(new IdentifierExpression(loc, tmpName));
						} else {
							sizeExpressions.add(sc);
						}
					}


					variableLengthArrayAuxVarInitializer = new ResultExpression(initStmts, 
							null, initDecls, initAuxVars);
	
					arrayType = new CArray(sizeExpressions.toArray(new Expression[sizeExpressions.size()]), newResType.cType);
				} else { //something like int a[] -- no size given
					arrayType = new CArray(sizeConstants.toArray(new Expression[sizeConstants.size()]), newResType.cType);
				}
			} else {
				arrayType = new CArray(sizeConstants.toArray(new Expression[sizeConstants.size()]), newResType.cType);
			}
			newResType.cType = arrayType;

		} else if (node instanceof CASTFunctionDeclarator) {
			CASTFunctionDeclarator funcDecl = (CASTFunctionDeclarator) node;

			IASTParameterDeclaration[] paramDecls = funcDecl.getParameters();
			CDeclaration[] paramsParsed = new CDeclaration[paramDecls.length];
			for (int i = 0; i < paramDecls.length; i++) {
				ResultDeclaration decl = (ResultDeclaration) main.dispatch(paramDecls[i]);
				if (decl.getDeclarations().size() != 1)
					throw new UnsupportedSyntaxException(loc, "Multiple names in parameter declaration");
				if (decl.getDeclarations().get(0).getName() == ""
						&& decl.getDeclarations().get(0).getType() instanceof CPrimitive
						&& ((CPrimitive) decl.getDeclarations().get(0).getType()).getType().equals(PRIMITIVE.VOID)) {
					assert paramDecls.length == 1;
					paramsParsed = new CDeclaration[0];
					break;
				}
				paramsParsed[i] = decl.getDeclarations().get(0);
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
			ResultDeclaration result = (ResultDeclaration) main.dispatch(node.getNestedDeclarator());
			mCurrentDeclaredTypes.pop();
			if (node.getInitializer() != null) {
				assert result.getDeclarations().size() == 1;
				CDeclaration cdec = result.getDeclarations().remove(0);// have
																		// to do
																		// this,
																		// because
																		// CDeclaration
																		// is
																		// immutable,
																		// right?
				result.addDeclaration(cdec.getType(), cdec.getName(),
						node.getInitializer(), variableLengthArrayAuxVarInitializer, cdec.isOnHeap());
			}
			return result;
		} else {
			ResultDeclaration result = new ResultDeclaration();
			result.addDeclaration(newResType.cType, node.getName().toString(), node.getInitializer(),
					variableLengthArrayAuxVarInitializer, newResType.isOnHeap);
			return result;
		}
	}

	@Override
	public Result visit(Dispatcher main, IASTLiteralExpression node) {
		ILocation loc = LocationFactory.createCLocation(node);

		switch (node.getKind()) {
		case IASTLiteralExpression.lk_float_constant:
			String val = new String(node.getValue());
			val = ISOIEC9899TC3.handleFloatConstant(val, loc, main);
			return new ResultExpression(new RValue(new RealLiteral(loc, val), new CPrimitive(PRIMITIVE.FLOAT)));
		case IASTLiteralExpression.lk_char_constant:
			val = new String(node.getValue());
			val = ISOIEC9899TC3.handleCharConstant(val, loc, main);
			return new ResultExpression(new RValue(new IntegerLiteral(loc, val), new CPrimitive(PRIMITIVE.CHAR)));
		case IASTLiteralExpression.lk_integer_constant:
			val = new String(node.getValue());
			RValue rVal = ISOIEC9899TC3.handleIntegerConstant(val, loc, main);
			return new ResultExpression(rVal);
		case IASTLiteralExpression.lk_string_literal:
			// Translate string to uninitialized char pointer
			String tId = main.nameHandler.getTempVarUID(SFO.AUXVAR.NONDET);
			VariableDeclaration tVarDecl = new VariableDeclaration(loc, new Attribute[0], new VarList[] { new VarList(
					loc, new String[] { tId }, MemoryHandler.POINTER_TYPE) });
			RValue rvalue = new RValue(new IdentifierExpression(loc, tId), new CPointer(new CPrimitive(PRIMITIVE.CHAR)));
			ArrayList<Declaration> decls = new ArrayList<Declaration>();
			decls.add(tVarDecl);
			Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>();
			auxVars.put(tVarDecl, loc);
			return new ResultExpression(new ArrayList<Statement>(), rvalue, decls, auxVars);
		case IASTLiteralExpression.lk_false:
			return new ResultExpression(new RValue(new BooleanLiteral(loc, false), new CPrimitive(PRIMITIVE.INT)));
		case IASTLiteralExpression.lk_true:
			return new ResultExpression(new RValue(new BooleanLiteral(loc, true), new CPrimitive(PRIMITIVE.INT)));
		default:
			String msg = "Unknown or unsupported kind of IASTLiteralExpression";
			throw new UnsupportedSyntaxException(loc, msg);
		}
	}

	@Override
	public Result visit(Dispatcher main, IASTIdExpression node) {
		ILocation loc = LocationFactory.createCLocation(node);
		String cId = node.getName().toString();

		//deal with builtin constants
		if (cId.equals("NULL")) {
			return new ResultExpression(new RValue(new IdentifierExpression(loc, SFO.NULL), 
					new CPointer(new CPrimitive(PRIMITIVE.VOID))));
		} else if (node.getName().toString().equals("__func__")){
			String tId = main.nameHandler.getTempVarUID(SFO.AUXVAR.NONDET);
			VariableDeclaration tVarDecl = new VariableDeclaration(loc, new Attribute[0], new VarList[] { new VarList(
					loc, new String[] { tId }, MemoryHandler.POINTER_TYPE) });
			RValue rvalue = new RValue(new IdentifierExpression(loc, tId), new CPointer(new CPrimitive(PRIMITIVE.CHAR)));
			ArrayList<Declaration> decls = new ArrayList<Declaration>();
			decls.add(tVarDecl);
			Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>();
			auxVars.put(tVarDecl, loc);
			return new ResultExpression(new ArrayList<Statement>(), rvalue, decls, auxVars);
		}

		String bId = null;
		CType cType = null;
		boolean useHeap = false;
		boolean intFromPtr = false;

		// Christian: function name, handle separately
		if (!mSymbolTable.containsCSymbol(cId) && main.getFunctionToIndex().containsKey(cId)) {
				cType = new CPointer(new CFunction(null, null, false));
				bId = SFO.FUNCTION_ADDRESS + cId;
				useHeap = true;
		} else if (mSymbolTable.containsCSymbol(cId)) {
			// we have a normal variable
			bId = mSymbolTable.get(cId, loc).getBoogieName();
			cType = mSymbolTable.get(cId, loc).getCVariable();
			useHeap = isHeapVar(bId);
			intFromPtr = mSymbolTable.get(cId, loc).isIntFromPointer;
		} else {
			throw new UnsupportedSyntaxException(loc, "identifier is not declared (neither a variable nor a function name)");
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
		return new ResultExpression(lrVal);
	}

	@Override
	public Result visit(Dispatcher main, IASTUnaryExpression node) {
		ResultExpression o = (ResultExpression) main.dispatch(node.getOperand());
		ILocation loc = LocationFactory.createCLocation(node);
		Expression nr1 = new IntegerLiteral(loc, SFO.NR1);

		// for the cases we know that it's an RValue..
		// ResultExpression rop = o.switchToRValueIfNecessary(main,
		// memoryHandler, structHandler, loc);

		CType oType = o.lrVal.cType;
		if (oType instanceof CNamed)
			oType = ((CNamed) oType).getUnderlyingType();

		switch (node.getOperator()) {
		case IASTUnaryExpression.op_minus: {
			ResultExpression rop = o.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
			ResultExpression ropToInt = ConvExpr.rexBoolToIntIfNecessary(loc, rop);
			if (ropToInt.lrVal.cType instanceof CPrimitive) {
				if (((CPrimitive) ropToInt.lrVal.cType).getGeneralType() == GENERALPRIMITIVE.INTTYPE) {
					Expression newEx = new UnaryExpression(loc, 
							UnaryExpression.Operator.ARITHNEGATIVE, ropToInt.lrVal.getValue());				
					ResultExpression rex = new ResultExpression(ropToInt.stmt, new RValue(newEx, ropToInt.lrVal.cType), 
							ropToInt.decl, ropToInt.auxVars, ropToInt.overappr);
					checkIntegerBounds(main, loc, rex);
					return rex;
				} else if (((CPrimitive) ropToInt.lrVal.cType).getGeneralType() == GENERALPRIMITIVE.FLOATTYPE) {
					//TODO: having boogie deal with negative real literals would be the nice solution..
					Expression newEx = new BinaryExpression(loc, BinaryExpression.Operator.ARITHMINUS, 
							new RealLiteral(loc, "0.0"), ropToInt.lrVal.getValue());				
					return new ResultExpression(ropToInt.stmt, new RValue(newEx, ropToInt.lrVal.cType), 
							ropToInt.decl, ropToInt.auxVars, ropToInt.overappr);
				} else {
					main.warn(loc, "-ex where ex is not a Primitive number type");
					Expression newEx = new UnaryExpression(loc, 
							UnaryExpression.Operator.ARITHNEGATIVE, ropToInt.lrVal.getValue());				
					return new ResultExpression(ropToInt.stmt, new RValue(newEx, ropToInt.lrVal.cType), 
							ropToInt.decl, ropToInt.auxVars, ropToInt.overappr);				
				}
				
			}

//			Expression newEx = new UnaryExpression(loc, ropToInt.lrVal.getValue().getType(), 
//							UnaryExpression.Operator.ARITHNEGATIVE, ropToInt.lrVal.getValue());

		}
		case IASTUnaryExpression.op_not:
		/** boolean <code>p</code> becomes <code>!p ? 1 : 0</code> */
		/**
		 * int <code>x</code> of form <code>y ? 1 : 0</code> becomes
		 * <code>!y ? 1 : 0</code>
		 */
		/** int <code>x</code> becomes <code>x == 0 ? 1 : 0</code> */
		{
			ResultExpression rop = o.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
			// implicit cast
			if (!rop.lrVal.isBoogieBool
					&& (!(rop.lrVal.cType instanceof CPrimitive) || ((CPrimitive) rop.lrVal.cType).getGeneralType() == GENERALPRIMITIVE.INTTYPE)) {
				if (rop.lrVal.cType instanceof CPointer) {// TODO: how general
															// is this
															// solution??
					rop.lrVal = new RValue(new StructAccessExpression(loc, rop.lrVal.getValue(), SFO.POINTER_BASE),
							new CPrimitive(PRIMITIVE.INT));
				}
			}
			ResultExpression ropToBool = ConvExpr.rexIntToBoolIfNecessary(loc, rop);
			Expression negated = new UnaryExpression(loc, UnaryExpression.Operator.LOGICNEG, ropToBool.lrVal.getValue());
			ResultExpression re = new ResultExpression(new RValue(negated, new CPrimitive(PRIMITIVE.INT), true),
					new LinkedHashMap<VariableDeclaration, ILocation>(), ropToBool.overappr);
			re.addAll(ropToBool);
			return re;
		}
		case IASTUnaryExpression.op_plus: {
			ResultExpression rop = o.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
			ResultExpression ropToInt = ConvExpr.rexBoolToIntIfNecessary(loc, rop);
			ropToInt = ConvExpr.rexBoolToIntIfNecessary(loc, rop);
			return new ResultExpression(ropToInt.stmt, ropToInt.lrVal, ropToInt.decl, ropToInt.auxVars,
					ropToInt.overappr);
		}
		case IASTUnaryExpression.op_postFixIncr:
		case IASTUnaryExpression.op_postFixDecr: {
			// FIXME: would it make sense here, to work with o, not rop??
			// --> we have to have an LValue, here, anyway.. (same thing for
			// prefixInc/Dec)
			// --> there even is an assert below to ensure this
			assert !o.lrVal.isBoogieBool;
			// E++ -> t = E; E = t + 1; t
			ResultExpression rop = o.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
			ArrayList<Declaration> decl = new ArrayList<Declaration>();
			ArrayList<Statement> stmt = new ArrayList<Statement>();
			Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>();
			List<Overapprox> overappr = new ArrayList<Overapprox>();
			// In this case we need a temporary variable
			String tmpName = main.nameHandler.getTempVarUID(SFO.AUXVAR.POST_MOD);
			ASTType tmpIType = mTypeHandler.ctype2asttype(loc, rop.lrVal.cType);

			VariableDeclaration tmpVar = SFO.getTempVarVariableDeclaration(tmpName, tmpIType, loc);
			auxVars.put(tmpVar, loc);
			decl.add(tmpVar);
			stmt.addAll(rop.stmt);
			decl.addAll(rop.decl);
			auxVars.putAll(rop.auxVars);
			overappr.addAll(rop.overappr);
			AssignmentStatement assignStmt = new AssignmentStatement(loc, new LeftHandSide[] { new VariableLHS(loc, // tmpIType,
					tmpName) }, new Expression[] { rop.lrVal.getValue() });
			Map<String, IAnnotations> annots = assignStmt.getPayload().getAnnotations();
			for (Overapprox overapprItem : overappr) {
				annots.put(Overapprox.getIdentifier(), overapprItem);
			}
			stmt.add(assignStmt);
			RValue tmpRValue = new RValue(new IdentifierExpression(loc, tmpName), o.lrVal.cType);
			int op;
			if (node.getOperator() == IASTUnaryExpression.op_postFixIncr)
				op = IASTBinaryExpression.op_plus;
			else
				op = IASTBinaryExpression.op_minus;

			RValue rhs = null;
			if (oType instanceof CPointer)
				rhs = doPointerArithPointerAndInteger(main, op, loc, tmpRValue, new RValue(nr1, new CPrimitive(
						PRIMITIVE.INT)), ((CPointer) tmpRValue.cType).pointsToType);
			else
				rhs = new RValue(createArithmeticExpression(op, tmpRValue.getValue(), nr1, loc), o.lrVal.cType);

			assert !(o.lrVal instanceof RValue);
			ResultExpression assign = makeAssignment(main, loc, stmt, o.lrVal, rhs, decl, auxVars, overappr);// ,
																												// o.lrVal.cType);
			checkIntegerBounds(main, loc, rhs, assign.stmt);
			return new ResultExpression(assign.stmt, tmpRValue, assign.decl, assign.auxVars, assign.overappr);
		}
		case IASTUnaryExpression.op_prefixDecr:
		case IASTUnaryExpression.op_prefixIncr: {
			assert !o.lrVal.isBoogieBool;
			// ++E -> t = E+1; E = t; t
			ResultExpression rop = o.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
			ArrayList<Declaration> decl = new ArrayList<Declaration>();
			ArrayList<Statement> stmt = new ArrayList<Statement>();
			Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>();
			List<Overapprox> overappr = new ArrayList<Overapprox>();
			// In this case we need a temporary variable
			String tmpName = main.nameHandler.getTempVarUID(SFO.AUXVAR.POST_MOD);
			ASTType tmpType = mTypeHandler.ctype2asttype(loc, rop.lrVal.cType);
			VariableDeclaration tmpVar = SFO.getTempVarVariableDeclaration(tmpName, tmpType, loc);
			auxVars.put(tmpVar, loc);
			decl.add(tmpVar);
			stmt.addAll(rop.stmt);
			decl.addAll(rop.decl);
			auxVars.putAll(rop.auxVars);
			overappr.addAll(rop.overappr);
			int op;
			if (node.getOperator() == IASTUnaryExpression.op_prefixIncr)
				op = IASTBinaryExpression.op_plus;
			else
				op = IASTBinaryExpression.op_minus;

			RValue rhs = null;
			if (oType instanceof CPointer)
				rhs = doPointerArithPointerAndInteger(main, op,
						// loc, (RValue) o.lrVal,
						loc, (RValue) rop.lrVal, new RValue(nr1, new CPrimitive(PRIMITIVE.INT)),
						((CPointer) o.lrVal.cType).pointsToType);
			// .lrVal.getValue();
			else
				rhs = new RValue(createArithmeticExpression(op, rop.lrVal.getValue(), nr1, loc), o.lrVal.cType);

			AssignmentStatement assignStmt = new AssignmentStatement(loc, new LeftHandSide[] { new VariableLHS(loc, // tmpIType,
					tmpName) }, new Expression[] { rhs.getValue() });
			Map<String, IAnnotations> annots = assignStmt.getPayload().getAnnotations();
			for (Overapprox overapprItem : overappr) {
				annots.put(Overapprox.getIdentifier(), overapprItem);
			}
			stmt.add(assignStmt);
			assert !(o.lrVal instanceof RValue);
			RValue tmpRValue = new RValue(new IdentifierExpression(loc, /*
																		 * tmpIType,
																		 */tmpName), o.lrVal.cType);
			ResultExpression assign = makeAssignment(main, loc, stmt, o.lrVal, tmpRValue, decl, auxVars, overappr);// ,
																													// o.lrVal.cType);
			checkIntegerBounds(main, loc, tmpRValue, assign.stmt);
			return new ResultExpression(assign.stmt, tmpRValue, assign.decl, assign.auxVars, assign.overappr);
		}
		case IASTUnaryExpression.op_bracketedPrimary:
			return o;
		case IASTUnaryExpression.op_sizeof:
			Map<VariableDeclaration, ILocation> emptyAuxVars = new LinkedHashMap<VariableDeclaration, ILocation>(0);
			return new ResultExpression(new RValue(mMemoryHandler.calculateSizeOf(oType, loc), new CPrimitive(
					PRIMITIVE.INT)), emptyAuxVars);
		case IASTUnaryExpression.op_star: {
			ResultExpression rop = o.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
			Expression addr = rop.lrVal.getValue();
			if (rop.lrVal.cType instanceof CArray) {
				CArray arrayCType = (CArray) rop.lrVal.cType;
				// FIXME: type like this??
				ArrayList<Expression> dims = new ArrayList<Expression>(Arrays.asList(arrayCType.getDimensions()));
				dims.remove(0);
				CType newCType = null;
				if (dims.size() == 0)
					newCType = arrayCType.getValueType();
				else
					newCType = new CArray(dims.toArray(new Expression[0]), arrayCType.getValueType());
				return new ResultExpression(rop.stmt, new HeapLValue(addr, newCType), rop.decl, rop.auxVars,
						rop.overappr);
			} else {
				assert rop.lrVal.cType.getUnderlyingType() instanceof CPointer : "type error: expected pointer , got "
						+ rop.lrVal.cType.toString();
				return new ResultExpression(rop.stmt, new HeapLValue(addr, ((CPointer) rop.lrVal.cType.getUnderlyingType()).pointsToType),
						rop.decl, rop.auxVars, rop.overappr);
			}
		}
		case IASTUnaryExpression.op_amper:
			if (o.lrVal instanceof HeapLValue) {
				Expression addr = ((HeapLValue) o.lrVal).getAddress();
				return new ResultExpression(o.stmt, new RValue(addr, new CPointer(o.lrVal.cType)), o.decl, o.auxVars,
						o.overappr);
			} else if (o.lrVal instanceof RValue && o.lrVal.getValue() instanceof IntegerLiteral) {
				assert node.getOperand() instanceof IASTIdExpression : "this is a function pointer, right??";
				return o;
			} else {
				throw new AssertionError("Address of something that is not on the heap.");
			}
		case IASTUnaryExpression.op_tilde:
			ResultExpression rop = o.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
			List<Overapprox> overappr = new ArrayList<Overapprox>();
			overappr.addAll(rop.overappr);
			overappr.add(new Overapprox(Overapprox.BITVEC, loc));
			Expression bwexpr = createBitwiseExpression(node.getOperator(), null, rop.lrVal.getValue(), loc);
			return new ResultExpression(rop.stmt, new RValue(bwexpr, rop.lrVal.cType), rop.decl, rop.auxVars, overappr);
		case IASTUnaryExpression.op_alignOf:
		default:
			String msg = "Unknown or unsupported unary operation: " + node.getOperator();
			throw new UnsupportedSyntaxException(loc, msg);
		}
	}

	@Override
	public Result visit(Dispatcher main, IASTBinaryExpression node) {
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		ArrayList<Statement> stmt = new ArrayList<Statement>();
		Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>();
		ILocation loc = LocationFactory.createCLocation(node);
		List<Overapprox> overappr = new ArrayList<Overapprox>();

		ResultExpression l = (ResultExpression) main.dispatch(node.getOperand1());
		ResultExpression r = (ResultExpression) main.dispatch(node.getOperand2());

		ResultExpression rl = l.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
		ResultExpression rr = r.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);

		CType lType = l.lrVal.cType.getUnderlyingType();
		CType rType = r.lrVal.cType.getUnderlyingType();

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
				return makeAssignment(main, loc, stmt, l.lrVal, address, decl, auxVars, overappr);
			} else {
				stmt.addAll(rr.stmt);
				decl.addAll(rr.decl);
				auxVars.putAll(rr.auxVars);
				overappr.addAll(rr.overappr);
				//			if (l.lrVal.cType instanceof CPrimitive
				//					&& ((CPrimitive) l.lrVal.cType).getGeneralType() == GENERALPRIMITIVE.INTTYPE) {
				ResultExpression rrToInt = ConvExpr.rexBoolToIntIfNecessary(loc, rr);
				//			}
				return makeAssignment(main, loc, stmt, l.lrVal, (RValue) rrToInt.lrVal, decl, auxVars, overappr,
						l.unionFieldIdToCType);// , r.lrVal.cType);
			}
//			} else {
//				return makeAssignment(main, loc, stmt, l.lrVal, (RValue) rr.lrVal, decl, auxVars, overappr,
//						l.unionFieldIdToCType);// , r.lrVal.cType);
//			}
		}
		case IASTBinaryExpression.op_equals:
		case IASTBinaryExpression.op_greaterEqual:
		case IASTBinaryExpression.op_greaterThan:
		case IASTBinaryExpression.op_lessEqual:
		case IASTBinaryExpression.op_lessThan:
		case IASTBinaryExpression.op_notequals: {
			BinaryExpression.Operator op;
			switch (node.getOperator()) {
			case IASTBinaryExpression.op_equals:
				op = BinaryExpression.Operator.COMPEQ;
				break;
			case IASTBinaryExpression.op_greaterEqual:
				op = BinaryExpression.Operator.COMPGEQ;
				break;
			case IASTBinaryExpression.op_greaterThan:
				op = BinaryExpression.Operator.COMPGT;
				break;
			case IASTBinaryExpression.op_lessEqual:
				op = BinaryExpression.Operator.COMPLEQ;
				break;
			case IASTBinaryExpression.op_lessThan:
				op = BinaryExpression.Operator.COMPLT;
				break;
			case IASTBinaryExpression.op_notequals:
				op = BinaryExpression.Operator.COMPNEQ;
				break;
			default:
				throw new AssertionError("???");
			}
			ResultExpression rrToInt = ConvExpr.rexBoolToIntIfNecessary(loc, rr);
			ResultExpression rlToInt = ConvExpr.rexBoolToIntIfNecessary(loc, rl);
			
			CastAndConversionHandler.usualArithmeticConversions(main, loc, mMemoryHandler, rlToInt, rrToInt, true);
			
			
			stmt.addAll(rlToInt.stmt);
			stmt.addAll(rrToInt.stmt);
			decl.addAll(rlToInt.decl);
			decl.addAll(rrToInt.decl);
			auxVars.putAll(rlToInt.auxVars);
			auxVars.putAll(rrToInt.auxVars);
			overappr.addAll(rlToInt.overappr);
			overappr.addAll(rrToInt.overappr);

			RValue rval = null;
			if (node.getOperator() == IASTBinaryExpression.op_equals 
					|| node.getOperator() == IASTBinaryExpression.op_notequals) {
				//!= and == are treated differently from the inequality operators
				// --> behaviour is never undefined for instance..
				
				// implicit casts
				if (lType instanceof CPointer || rType instanceof CPointer) {
					if (!(lType instanceof CPointer)) {
						rlToInt.lrVal = castToType(loc, (RValue) rlToInt.lrVal, new CPointer(new CPrimitive(PRIMITIVE.VOID)));
//								new RValue(MemoryHandler.constructPointerFromBaseAndOffset(new IntegerLiteral(loc,
//								"0"), rlToInt.lrVal.getValue(), loc), new CPrimitive(PRIMITIVE.VOID));
					}
					if (!(rType instanceof CPointer)) {
						rrToInt.lrVal = castToType(loc, (RValue) rrToInt.lrVal, new CPointer(new CPrimitive(PRIMITIVE.VOID)));
//						new RValue(MemoryHandler.constructPointerFromBaseAndOffset(new IntegerLiteral(loc,
//								"0"), rrToInt.lrVal.getValue(), loc), new CPrimitive(PRIMITIVE.VOID));
					}
				}
				rval = new RValue(new BinaryExpression(loc, op, rlToInt.lrVal.getValue(), rrToInt.lrVal.getValue()),
						new CPrimitive(PRIMITIVE.INT));
			} else {
				// we have a "relational" pointer comparison
				if (lType instanceof CPointer || rType instanceof CPointer) {
					// both of the two following ifs will lead to an assertion
					// violation if the pointer compared to
					// is something different from NULL (as we construct Pointers
					// with base 0) --> but this is ok, as
					// it would be undefined behaviour
					// except if we converted a pointer into an allocated region to
					// int, this is not supported yet (TODO)
					if (!(lType instanceof CPointer)) {
						rlToInt.lrVal = new RValue(MemoryHandler.constructPointerFromBaseAndOffset(new IntegerLiteral(loc,
								"0"), rlToInt.lrVal.getValue(), loc), new CPrimitive(PRIMITIVE.VOID));
					}
					if (!(rType instanceof CPointer)) {
						rrToInt.lrVal = new RValue(MemoryHandler.constructPointerFromBaseAndOffset(new IntegerLiteral(loc,
								"0"), rrToInt.lrVal.getValue(), loc), new CPrimitive(PRIMITIVE.VOID));
					}
					// assert ((CPointer)
					// rlToInt.lrVal.cType).pointsToType.equals(((CPointer)
					// rrToInt.lrVal.cType).pointsToType); //FIXME macht dieses
					// assert Sinn?
					// assert (in Boogie) that the base value of the pointers
					// matches
					if (this.mMemoryHandler.getPointerSubtractionAndComparisonValidityCheckMode() == POINTER_CHECKMODE.ASSERTandASSUME) {
						Statement assertStm = new AssertStatement(loc, new BinaryExpression(loc,
								BinaryExpression.Operator.COMPEQ, new StructAccessExpression(loc, rlToInt.lrVal.getValue(),
										SFO.POINTER_BASE), new StructAccessExpression(loc, rrToInt.lrVal.getValue(),
												SFO.POINTER_BASE)));
						stmt.add(assertStm);
						Check chk = new Check(Spec.ILLEGAL_POINTER_ARITHMETIC);
						chk.addToNodeAnnot(assertStm);
					} else if (this.mMemoryHandler.getPointerSubtractionAndComparisonValidityCheckMode() == POINTER_CHECKMODE.ASSUME) {
						Statement assumeStm = new AssumeStatement(loc, new BinaryExpression(loc,
								BinaryExpression.Operator.COMPEQ, new StructAccessExpression(loc, rlToInt.lrVal.getValue(),
										SFO.POINTER_BASE), new StructAccessExpression(loc, rrToInt.lrVal.getValue(),
												SFO.POINTER_BASE)));
						stmt.add(assumeStm);
					}

					rval = new RValue(new BinaryExpression(loc, op, 
							new StructAccessExpression(loc, rlToInt.lrVal.getValue(), SFO.POINTER_OFFSET), 
							new StructAccessExpression(loc, rrToInt.lrVal.getValue(), SFO.POINTER_OFFSET)), 
							new CPrimitive(PRIMITIVE.INT));
				} else {
					rval = new RValue(new BinaryExpression(loc, op, rlToInt.lrVal.getValue(), rrToInt.lrVal.getValue()),
							new CPrimitive(PRIMITIVE.INT));
				}
			}
			rval.isBoogieBool = true;
			return new ResultExpression(stmt, rval, decl, auxVars, overappr);
		}
		case IASTBinaryExpression.op_logicalAnd: {
			ResultExpression rlToBool = ConvExpr.rexIntToBoolIfNecessary(loc, rl);
			ResultExpression rrToBool = ConvExpr.rexIntToBoolIfNecessary(loc, rr);
			

			stmt.addAll(rlToBool.stmt);
			// NOTE: no rr.stmt
			decl.addAll(rlToBool.decl);
			decl.addAll(rrToBool.decl);
			auxVars.putAll(rlToBool.auxVars);
			auxVars.putAll(rrToBool.auxVars);
			overappr.addAll(rlToBool.overappr);
			overappr.addAll(rrToBool.overappr);

			if (rrToBool.stmt.isEmpty()) {
				// no statements in right operands, hence no side effects in
				// operand
				// we can directly combine operands with LOGICAND
				RValue newRVal = new RValue(new BinaryExpression(loc, BinaryExpression.Operator.LOGICAND,
						rlToBool.lrVal.getValue(), rrToBool.lrVal.getValue()),
						new CPrimitive(CPrimitive.PRIMITIVE.INT), true);

				return new ResultExpression(stmt, newRVal, decl, auxVars, overappr);
			}
			// create and add tmp var #t~AND~UID
			String resName = main.nameHandler.getTempVarUID(SFO.AUXVAR.SHORTCIRCUIT);
			VarList tempVar = new VarList(loc, new String[] { resName }, new PrimitiveType(loc, SFO.BOOL));
			VariableDeclaration tmpVar = new VariableDeclaration(loc, new Attribute[0], new VarList[] { tempVar });
			auxVars.put(tmpVar, loc);
			decl.add(tmpVar);
			VariableLHS lhs = new VariableLHS(loc, resName);
			RValue tmpRval = new RValue(new IdentifierExpression(loc, resName), new CPrimitive(PRIMITIVE.INT), true);
			RValue resRval = tmpRval;
			// #t~AND~UID = left

			AssignmentStatement aStat = new AssignmentStatement(loc, new LeftHandSide[] { lhs },
					new Expression[] { rlToBool.lrVal.getValue() });
			Map<String, IAnnotations> annots = aStat.getPayload().getAnnotations();
			for (Overapprox overapprItem : overappr) {
				annots.put(Overapprox.getIdentifier(), overapprItem);
			}
			stmt.add(aStat);
			// if (#t~AND~UID) {#t~AND~UID = right;}
			ArrayList<Statement> outerThenPart = new ArrayList<Statement>();
			outerThenPart.addAll(rrToBool.stmt);

			outerThenPart.add(new AssignmentStatement(loc, new LeftHandSide[] { lhs },
					new Expression[] { rrToBool.lrVal.getValue() }));
			IfStatement ifStatement = new IfStatement(loc, tmpRval.getValue(), outerThenPart.toArray(new Statement[0]),
					new Statement[0]);
			annots = ifStatement.getPayload().getAnnotations();
			for (Overapprox overapprItem : overappr) {
				annots.put(Overapprox.getIdentifier(), overapprItem);
			}
			stmt.add(ifStatement);
			return new ResultExpression(stmt, resRval, decl, auxVars, overappr);
		}
		case IASTBinaryExpression.op_logicalOr: {
			ResultExpression rlToBool = ConvExpr.rexIntToBoolIfNecessary(loc, rl);
			ResultExpression rrToBool = ConvExpr.rexIntToBoolIfNecessary(loc, rr);

			stmt.addAll(rlToBool.stmt);
			// NOTE: no rr.stmt
			decl.addAll(rlToBool.decl);
			decl.addAll(rrToBool.decl);
			auxVars.putAll(rlToBool.auxVars);
			auxVars.putAll(rrToBool.auxVars);
			overappr.addAll(rlToBool.overappr);
			overappr.addAll(rrToBool.overappr);

			if (rrToBool.stmt.isEmpty()) {
				// no auxVar in operands, hence no side effects in operands
				// we can directly combine operands with LOGICOR
				return new ResultExpression(stmt, new RValue(new BinaryExpression(loc,
						BinaryExpression.Operator.LOGICOR, rlToBool.lrVal.getValue(), rrToBool.lrVal.getValue()),
						new CPrimitive(CPrimitive.PRIMITIVE.INT), true), decl, auxVars, overappr);
			}
			// create and add tmp var #t~OR~UID
			String resName = main.nameHandler.getTempVarUID(SFO.AUXVAR.SHORTCIRCUIT);
			VarList tempVar = new VarList(loc, new String[] { resName }, new PrimitiveType(loc, SFO.BOOL));
			VariableDeclaration tmpVar = new VariableDeclaration(loc, new Attribute[0], new VarList[] { tempVar });
			auxVars.put(tmpVar, loc);
			decl.add(tmpVar);
			VariableLHS lhs = new VariableLHS(loc, resName);
			RValue tmpRval = new RValue(new IdentifierExpression(loc, resName), new CPrimitive(PRIMITIVE.INT), true);
			RValue resRval = tmpRval;
			// #t~OR~UID = left
			AssignmentStatement aStat = new AssignmentStatement(loc, new LeftHandSide[] { lhs },
					new Expression[] { rlToBool.lrVal.getValue() });
			Map<String, IAnnotations> annots = aStat.getPayload().getAnnotations();
			for (Overapprox overapproxItem : overappr) {
				annots.put(Overapprox.getIdentifier(), overapproxItem);
			}
			stmt.add(aStat);
			// if (#t~OR~UID) {} else {#t~OR~UID = right;}
			ArrayList<Statement> outerElsePart = new ArrayList<Statement>();
			outerElsePart.addAll(rr.stmt);

			outerElsePart.add(new AssignmentStatement(loc, new LeftHandSide[] { lhs },
					new Expression[] { rrToBool.lrVal.getValue() }));
			IfStatement ifStatement = new IfStatement(loc, tmpRval.getValue(), new Statement[0],
					outerElsePart.toArray(new Statement[0]));
			annots = ifStatement.getPayload().getAnnotations();
			for (Overapprox overapprItem : overappr) {
				annots.put(Overapprox.getIdentifier(), overapprItem);
			}
			stmt.add(ifStatement);
			return new ResultExpression(stmt, resRval, decl, auxVars, overappr);
		}
		case IASTBinaryExpression.op_minus:
		case IASTBinaryExpression.op_plus:
		case IASTBinaryExpression.op_modulo:
		case IASTBinaryExpression.op_multiply:
		case IASTBinaryExpression.op_divide: {
			
			if (lType instanceof CArray || rType instanceof CArray) {
				ResultExpression rlToInt = ConvExpr.rexBoolToIntIfNecessary(loc, rl);
				ResultExpression rrToInt = ConvExpr.rexBoolToIntIfNecessary(loc, rr);
	
				RValue rval = null;
				if (lType instanceof CArray
						&& rType instanceof CPrimitive
						&& ((CPrimitive) rType).getGeneralType() == GENERALPRIMITIVE.INTTYPE) {
					CType valueType = ((CArray) lType).getValueType().getUnderlyingType();

					RValue arrayAdd = null;
					if (l.lrVal instanceof HeapLValue)
						arrayAdd = new RValue(((HeapLValue)l.lrVal).getAddress(), new CPointer(valueType));
					else
						arrayAdd = new RValue(l.lrVal.getValue(), new CPointer(valueType));
						

					rval = doPointerArithPointerAndInteger(main, node.getOperator(), loc, arrayAdd,
							((RValue) rrToInt.lrVal), new CPointer(valueType));

					stmt.addAll(l.stmt);
					stmt.addAll(rrToInt.stmt);
					decl.addAll(l.decl);
					decl.addAll(rrToInt.decl);
					auxVars.putAll(l.auxVars);
					auxVars.putAll(rrToInt.auxVars);
					overappr.addAll(l.overappr);
					overappr.addAll(rrToInt.overappr);
					
				} else if ((rType instanceof CArray) 
						&& lType instanceof CPrimitive
						&& ((CPrimitive) lType).getGeneralType() == GENERALPRIMITIVE.INTTYPE) {
					CType valueType = ((CArray) rType).getValueType().getUnderlyingType();

					RValue arrayAdd = null;
					if (r.lrVal instanceof HeapLValue)
						arrayAdd = new RValue(((HeapLValue)r.lrVal).getAddress(), new CPointer(valueType));
					else
						arrayAdd = new RValue(r.lrVal.getValue(), new CPointer(valueType));
	
					rval = doPointerArithPointerAndInteger(main, node.getOperator(), loc,
							(RValue) rlToInt.lrVal, arrayAdd, new CPointer(valueType));

					stmt.addAll(rlToInt.stmt);
					stmt.addAll(r.stmt);
					decl.addAll(rlToInt.decl);
					decl.addAll(r.decl);
					auxVars.putAll(rlToInt.auxVars);
					auxVars.putAll(r.auxVars);
					overappr.addAll(rlToInt.overappr);
					overappr.addAll(r.overappr);	

				} else if (lType instanceof CArray
						&& rType instanceof CArray) {
					CType lValueType = ((CArray) lType).getValueType();
					CType rValueType = ((CArray) rType).getValueType();
					
					RValue arrayAddl = null;
					if (l.lrVal instanceof HeapLValue)
						arrayAddl = new RValue(((HeapLValue)l.lrVal).getAddress(), new CPointer(lValueType));
					else
						arrayAddl = new RValue(l.lrVal.getValue(), new CPointer(lValueType));
			
					RValue arrayAddr = null;
					if (r.lrVal instanceof HeapLValue)
						arrayAddr = new RValue(((HeapLValue)r.lrVal).getAddress(), new CPointer(rValueType));
					else
						arrayAddr = new RValue(r.lrVal.getValue(), new CPointer(rValueType));
		
					assert lValueType.equals(rValueType);
					if (this.mMemoryHandler.getPointerSubtractionAndComparisonValidityCheckMode() == POINTER_CHECKMODE.ASSERTandASSUME) {
						Statement assertStm = new AssertStatement(loc, new BinaryExpression(loc,
								BinaryExpression.Operator.COMPEQ, new StructAccessExpression(loc, arrayAddl.getValue(),
										SFO.POINTER_BASE), new StructAccessExpression(loc, arrayAddr.getValue(),
												SFO.POINTER_BASE)));
						stmt.add(assertStm);
						Check chk = new Check(Spec.ILLEGAL_POINTER_ARITHMETIC);
						chk.addToNodeAnnot(assertStm);
					} else if (this.mMemoryHandler.getPointerSubtractionAndComparisonValidityCheckMode() == POINTER_CHECKMODE.ASSUME) {
						Statement assumeStm = new AssumeStatement(loc, new BinaryExpression(loc,
								BinaryExpression.Operator.COMPEQ, new StructAccessExpression(loc, arrayAddl.getValue(),
										SFO.POINTER_BASE), new StructAccessExpression(loc, arrayAddr.getValue(),
												SFO.POINTER_BASE)));
						stmt.add(assumeStm);
					}

					rval = doPointerArithPointerAndPointer(main, node.getOperator(), loc, arrayAddl,
							arrayAddr);

					stmt.addAll(l.stmt);
					stmt.addAll(r.stmt);
					decl.addAll(l.decl);
					decl.addAll(r.decl);
					auxVars.putAll(l.auxVars);
					auxVars.putAll(r.auxVars);
					overappr.addAll(l.overappr);
					overappr.addAll(r.overappr);
				}
				
				return new ResultExpression(stmt, rval, decl, auxVars, overappr);
			} else if (lType instanceof CPointer || rType instanceof CPointer) {
				ResultExpression rlToInt = ConvExpr.rexBoolToIntIfNecessary(loc, rl);
				ResultExpression rrToInt = ConvExpr.rexBoolToIntIfNecessary(loc, rr);
				RValue rval = null;
				if ((lType instanceof CPointer) 
						&& rType instanceof CPrimitive
						&& ((CPrimitive) rType).getGeneralType() == GENERALPRIMITIVE.INTTYPE) {
					CType valueType = ((CPointer) lType).pointsToType.getUnderlyingType();
									
					rval = doPointerArithPointerAndInteger(main, node.getOperator(), loc, ((RValue) rlToInt.lrVal),
									((RValue) rrToInt.lrVal), valueType);
				} else if ((rType instanceof CPointer) 
						&& lType instanceof CPrimitive
						&& ((CPrimitive) lType).getGeneralType() == GENERALPRIMITIVE.INTTYPE) {
					CType valueType =  ((CPointer) rType).pointsToType.getUnderlyingType();
					rval = doPointerArithPointerAndInteger(main, node.getOperator(), loc, (RValue) rrToInt.lrVal,
									(RValue) rlToInt.lrVal, valueType);
				} else if (lType instanceof CPointer
						&& rType instanceof CPointer) {
					assert node.getOperator() == IASTBinaryExpression.op_minus : "only subtraction of two pointers is allowed";
					CType lValueType = ((CPointer) lType).pointsToType;
					CType rValueType = ((CPointer) rType).pointsToType;
					assert lValueType.equals(rValueType);
					// assert (in Boogie) that the base value of the pointers
					// matches
					if (this.mMemoryHandler.getPointerSubtractionAndComparisonValidityCheckMode() == POINTER_CHECKMODE.ASSERTandASSUME) {
						Statement assertStm = new AssertStatement(loc, new BinaryExpression(loc,
								BinaryExpression.Operator.COMPEQ, new StructAccessExpression(loc, rlToInt.lrVal.getValue(),
										SFO.POINTER_BASE), new StructAccessExpression(loc, rrToInt.lrVal.getValue(),
												SFO.POINTER_BASE)));
						stmt.add(assertStm);
						Check chk = new Check(Spec.ILLEGAL_POINTER_ARITHMETIC);
						chk.addToNodeAnnot(assertStm);
					} else if (this.mMemoryHandler.getPointerSubtractionAndComparisonValidityCheckMode() == POINTER_CHECKMODE.ASSUME) {
						Statement assumeStm = new AssumeStatement(loc, new BinaryExpression(loc,
								BinaryExpression.Operator.COMPEQ, new StructAccessExpression(loc, rlToInt.lrVal.getValue(),
										SFO.POINTER_BASE), new StructAccessExpression(loc, rrToInt.lrVal.getValue(),
												SFO.POINTER_BASE)));
						stmt.add(assumeStm);
					}

					rval = doPointerArithPointerAndPointer(main, node.getOperator(), loc, (RValue) rlToInt.lrVal,
							(RValue) rrToInt.lrVal);
				}
				stmt.addAll(rlToInt.stmt);
				stmt.addAll(rrToInt.stmt);
				decl.addAll(rlToInt.decl);
				decl.addAll(rrToInt.decl);
				auxVars.putAll(rlToInt.auxVars);
				auxVars.putAll(rrToInt.auxVars);
				overappr.addAll(rlToInt.overappr);
				overappr.addAll(rrToInt.overappr);

				return new ResultExpression(stmt, rval, decl, auxVars, overappr);

			} else {


				ResultExpression rlToInt = ConvExpr.rexBoolToIntIfNecessary(loc, rl);
				ResultExpression rrToInt = ConvExpr.rexBoolToIntIfNecessary(loc, rr);

				if (node.getOperator() == IASTBinaryExpression.op_divide) {
					Check check = new Check(Check.Spec.DIVISION_BY_ZERO);
					ILocation assertLoc = LocationFactory.createCLocation(node, check);
					AssertStatement assertStmt = new AssertStatement(assertLoc, new BinaryExpression(assertLoc,
							BinaryExpression.Operator.COMPNEQ, new IntegerLiteral(assertLoc, SFO.NR0),
							rrToInt.lrVal.getValue()));
					Map<String, IAnnotations> annots = assertStmt.getPayload().getAnnotations();
					for (Overapprox overapprItem : overappr) {
						annots.put(Overapprox.getIdentifier(), overapprItem);
					}
					stmt.add(assertStmt);
					check.addToNodeAnnot(assertStmt);
					stmt.add(assertStmt);

					//modulo is not compatible with division..
					CastAndConversionHandler.usualArithmeticConversions(main, loc, mMemoryHandler, 
							rlToInt, rrToInt, true);
					//FIXME ..or should we do wraparound only on nominator??
				} else {
					CastAndConversionHandler.usualArithmeticConversions(main, loc, mMemoryHandler, 
							rlToInt, rrToInt, false);
				}
				stmt.addAll(rlToInt.stmt);
				stmt.addAll(rrToInt.stmt);
				decl.addAll(rlToInt.decl);
				decl.addAll(rrToInt.decl);
				auxVars.putAll(rlToInt.auxVars);
				auxVars.putAll(rrToInt.auxVars);
				overappr.addAll(rlToInt.overappr);
				overappr.addAll(rrToInt.overappr);


				RValue rval = new RValue(createArithmeticExpression(node.getOperator(), rlToInt.lrVal.getValue(),
						rrToInt.lrVal.getValue(), loc), rlToInt.lrVal.cType);
				
				
				assert (main.isAuxVarMapcomplete(decl, auxVars)) : "unhavoced auxvars";
				ResultExpression rex = new ResultExpression(stmt, rval, decl, auxVars, overappr);
				if (node.getOperator() != IASTBinaryExpression.op_divide
						&& node.getOperator() != IASTBinaryExpression.op_modulo)
					checkIntegerBounds(main, loc, rex);
				return rex;
			}
		}
		case IASTBinaryExpression.op_minusAssign:
		case IASTBinaryExpression.op_multiplyAssign:
		case IASTBinaryExpression.op_divideAssign:
		case IASTBinaryExpression.op_moduloAssign:
		case IASTBinaryExpression.op_plusAssign: {
			assert !rl.lrVal.isBoogieBool && !rr.lrVal.isBoogieBool;

			if (node.getOperator() == IASTBinaryExpression.op_divideAssign) {
				Check check = new Check(Check.Spec.DIVISION_BY_ZERO);
				ILocation assertLoc = LocationFactory.createCLocation(node, check);
				AssertStatement assertStmt = new AssertStatement(assertLoc, new BinaryExpression(assertLoc,
						BinaryExpression.Operator.COMPNEQ, new IntegerLiteral(assertLoc, SFO.NR0), rr.lrVal.getValue()));
				Map<String, IAnnotations> annots = assertStmt.getPayload().getAnnotations();
				for (Overapprox overapprItem : overappr) {
					annots.put(Overapprox.getIdentifier(), overapprItem);
				}
				check.addToNodeAnnot(assertStmt);
				stmt.add(assertStmt);

				//modulo is not compatible with division..
				CastAndConversionHandler.usualArithmeticConversions(main, loc, mMemoryHandler, 
						rl, rr, true);
			} else {
				CastAndConversionHandler.usualArithmeticConversions(main, loc, mMemoryHandler, 
						rl, rr, false); 
			}
			stmt.addAll(rl.stmt);
			stmt.addAll(rr.stmt);
			decl.addAll(rl.decl);
			decl.addAll(rr.decl);
			auxVars.putAll(rl.auxVars);
			auxVars.putAll(rr.auxVars);
			overappr.addAll(rl.overappr);
			overappr.addAll(rr.overappr);
			
			// handle pointer arithmetic.
			RValue rightHandside = null;
			if (lType instanceof CPointer && rType instanceof CPrimitive
					&& ((CPrimitive) rType).getType() == PRIMITIVE.INT) {
				rightHandside = doPointerArithPointerAndInteger(main, node.getOperator(), loc, (RValue) rl.lrVal,
						(RValue) rr.lrVal, ((CPointer) rl.lrVal.cType.getUnderlyingType()).pointsToType);
			} else {
				rightHandside = new RValue(createArithmeticExpression(node.getOperator(), rl.lrVal.getValue(),
						rr.lrVal.getValue(), loc), rr.lrVal.cType);
			} 
			if (node.getOperator() != IASTBinaryExpression.op_divideAssign
						&& node.getOperator() != IASTBinaryExpression.op_moduloAssign)
				checkIntegerBounds(main, loc, rightHandside, stmt);
			return makeAssignment(main, loc, stmt, l.lrVal, rightHandside, decl, auxVars, overappr);
		}
		case IASTBinaryExpression.op_binaryAnd:
		case IASTBinaryExpression.op_binaryOr:
		case IASTBinaryExpression.op_binaryXor:
		case IASTBinaryExpression.op_shiftLeft:
		case IASTBinaryExpression.op_shiftRight: {
			CastAndConversionHandler.usualArithmeticConversions(main, loc, mMemoryHandler, 
						rl, rr, false); 
			stmt.addAll(rl.stmt);
			stmt.addAll(rr.stmt);
			decl.addAll(rl.decl);
			decl.addAll(rr.decl);
			auxVars.putAll(rl.auxVars);
			auxVars.putAll(rr.auxVars);
			overappr.addAll(rl.overappr);
			overappr.addAll(rr.overappr);
			overappr.add(new Overapprox(Overapprox.BITVEC, loc));
			Expression bwexpr = createBitwiseExpression(node.getOperator(), rl.lrVal.getValue(), rr.lrVal.getValue(),
					loc);
			return new ResultExpression(stmt, new RValue(bwexpr, rl.lrVal.cType), decl, auxVars, overappr);
		}
		case IASTBinaryExpression.op_shiftLeftAssign:
		case IASTBinaryExpression.op_shiftRightAssign:
		case IASTBinaryExpression.op_binaryAndAssign:
		case IASTBinaryExpression.op_binaryOrAssign:
		case IASTBinaryExpression.op_binaryXorAssign: {
			CastAndConversionHandler.usualArithmeticConversions(main, loc, mMemoryHandler, 
						rl, rr, false); 
			stmt.addAll(rl.stmt);
			stmt.addAll(rr.stmt);
			decl.addAll(rl.decl);
			decl.addAll(rr.decl);
			auxVars.putAll(rl.auxVars);
			auxVars.putAll(rr.auxVars);
			overappr.addAll(rl.overappr);
			overappr.addAll(rr.overappr);
			overappr.add(new Overapprox(Overapprox.BITVEC, loc));
			Expression bwexpr = createBitwiseExpression(node.getOperator(), rl.lrVal.getValue(), rr.lrVal.getValue(),
					loc);
			return makeAssignment(main, loc, stmt, l.lrVal, new RValue(bwexpr, rr.lrVal.cType), decl, auxVars, overappr);// ,
																															// l.lrVal.cType);
		}
		default:
			String msg = "Unknown or unsupported unary operation";
			throw new UnsupportedSyntaxException(loc, msg);
		}
	}
	
//	public void doIntOverflowTreatmentInComparisonIfApplicable(Dispatcher main,
//			ILocation loc, ResultExpression left,
//			ResultExpression right) {
//		if (main.cHandler.getUnsignedTreatment() == UNSIGNED_TREATMENT.IGNORE)
//			return;
//		
//		boolean isLeftUnsigned = left.lrVal.cType instanceof CPrimitive
//				&& ((CPrimitive) left.lrVal.cType).isUnsigned()
//				&& !left.lrVal.isIntFromPointer;
//		boolean isRightUnsigned = right.lrVal.cType instanceof CPrimitive
//				&& ((CPrimitive) right.lrVal.cType).isUnsigned()
//				&& !right.lrVal.isIntFromPointer;
//
//		//if one is unsigned, we convert the other to unsigned
//		// --> C99: "usual conversions"
//		if (isLeftUnsigned || isRightUnsigned) {
//			CastAndConversionHandler.doIntOverflowTreatment(main, mMemoryHandler, loc, left);
//			CastAndConversionHandler.doIntOverflowTreatment(main, mMemoryHandler, loc, right);
//		}
//		
//	}

//	public void doIntOverflowTreatmentIfApplicable(Dispatcher main,
//			ILocation loc, ResultExpression rex) {
//		if (main.cHandler.getUnsignedTreatment() == UNSIGNED_TREATMENT.IGNORE)
//			return;
//		
//		boolean isRexUnsigned = rex.lrVal.cType instanceof CPrimitive
//				&& ((CPrimitive) rex.lrVal.cType).isUnsigned()
//				&& !rex.lrVal.isIntFromPointer;
//		
//		if (isRexUnsigned)
//			doIntOverflowTreatment(main, loc, rex);
//	}
//	
//	public void doIntOverflowTreatment(Dispatcher main, ILocation loc,
//			ResultExpression rex) {
//		//FIXME  it is not always correct to take the size of rex's lrval's ctype, in case of a comparison we may need to take the
//		// size of the other value's type
//
//		//special treatment for unsigned integer types
//		int exponentInBytes = -1; 
//		if (rex.lrVal.cType.getUnderlyingType() instanceof CEnum) {
//			exponentInBytes = mMemoryHandler.typeSizeConstants.sizeOfEnumType;
//		} else {
//			//should be primitive
//			exponentInBytes = mMemoryHandler.typeSizeConstants
//				.CPrimitiveToTypeSizeConstant.get(((CPrimitive) rex.lrVal.cType.getUnderlyingType()).getType());
//		}
//		BigInteger maxValue = new BigInteger("2")
//			.pow(exponentInBytes * 8);
//
//		if (main.cHandler.getUnsignedTreatment() == UNSIGNED_TREATMENT.ASSUME_ALL) {
//			AssumeStatement assumeGeq0 = new AssumeStatement(loc, new BinaryExpression(loc, BinaryExpression.Operator.COMPGEQ,
//					rex.lrVal.getValue(), new IntegerLiteral(loc, SFO.NR0)));
//			rex.stmt.add(assumeGeq0);
//
//			AssumeStatement assumeLtMax = new AssumeStatement(loc, new BinaryExpression(loc, BinaryExpression.Operator.COMPLT,
//					rex.lrVal.getValue(), new IntegerLiteral(loc, maxValue.toString())));
//			rex.stmt.add(assumeLtMax);
//		} else if (main.cHandler.getUnsignedTreatment() == UNSIGNED_TREATMENT.WRAPAROUND) {
//			rex.lrVal = new RValue(new BinaryExpression(loc, BinaryExpression.Operator.ARITHMOD, 
//					rex.lrVal.getValue(), 
//					new IntegerLiteral(loc, maxValue.toString())), 
//					rex.lrVal.cType, 
//					rex.lrVal.isBoogieBool,
//					false);
//		}
//	}

	/**
	 * Takes a ResultExpression coming from an arithmetic expression, and, if the corresponding preference
	 * is set, adds asserts that check that no integer over-/underflow occurs.
	 * Does that only if the corresponding preference is set.
	 */
	private void checkIntegerBounds(Dispatcher main, ILocation loc, ResultExpression rex) {
		checkIntegerBounds(main, loc, (RValue) rex.lrVal, rex.stmt);
	}

	private void checkIntegerBounds(Dispatcher main, ILocation loc, RValue rVal, ArrayList<Statement> stmt) {
		if (main.mPreferences.getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_SIGNED_INTEGER_BOUNDS)
				&& rVal.cType instanceof CPrimitive
				&& ((CPrimitive) rVal.cType).getGeneralType() == GENERALPRIMITIVE.INTTYPE
				&& !((CPrimitive) rVal.cType).isUnsigned()) {
			Check check = new Check(Spec.INTEGER_OVERFLOW);
			AssertStatement smallerMaxInt = new AssertStatement(loc, new BinaryExpression(loc, BinaryExpression.Operator.COMPLT, rVal.getValue(), 
					new IntegerLiteral(loc, CastAndConversionHandler.getMaxValueOfPrimitiveType(mMemoryHandler, rVal.cType.getUnderlyingType()).toString())));
			check.addToNodeAnnot(smallerMaxInt);
			stmt.add(smallerMaxInt);
			AssertStatement biggerMinInt = new AssertStatement(loc, new BinaryExpression(loc, BinaryExpression.Operator.COMPGEQ, rVal.getValue(), 
					new IntegerLiteral(loc, CastAndConversionHandler.getMaxValueOfPrimitiveType(mMemoryHandler, rVal.cType.getUnderlyingType()).negate().toString())));
			check.addToNodeAnnot(biggerMinInt);
			stmt.add(biggerMinInt);
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
		if (r instanceof ResultExpression) {
			ResultExpression rExp = (ResultExpression) r;
			if (!rExp.stmt.isEmpty()) {
				ArrayList<Statement> stmt = new ArrayList<Statement>(rExp.stmt);
				ArrayList<Declaration> decl = new ArrayList<Declaration>(rExp.decl);
				List<Overapprox> overappr = new ArrayList<Overapprox>();
				assert (main.isAuxVarMapcomplete(rExp.decl, rExp.auxVars));
				stmt.addAll(createHavocsForNonMallocAuxVars(rExp.auxVars));
				overappr.addAll(rExp.overappr);
				Map<VariableDeclaration, ILocation> emptyAuxVars = new LinkedHashMap<VariableDeclaration, ILocation>(0);
				return new ResultExpression(stmt, null, decl, emptyAuxVars, overappr);
			} else {
				String msg = "This statement has no effect and will be dropped: " + node.getRawSignature();
				main.warn(LocationFactory.createCLocation(node), msg);
				return new ResultSkip();
			}
		} else if (r instanceof ResultExpressionList) {
			ArrayList<Statement> stmt = new ArrayList<Statement>();
			ArrayList<Declaration> decl = new ArrayList<Declaration>();
			List<Overapprox> overappr = new ArrayList<Overapprox>();
			Map<VariableDeclaration, ILocation> emptyAuxVars = new LinkedHashMap<VariableDeclaration, ILocation>(0);
			for (ResultExpression res : ((ResultExpressionList) r).list) {
				if (!res.stmt.isEmpty()) {
					stmt.addAll(res.stmt);
					decl.addAll(res.decl);
					assert (main.isAuxVarMapcomplete(res.decl, res.auxVars));
					stmt.addAll(createHavocsForNonMallocAuxVars(res.auxVars));
					overappr.addAll(res.overappr);
				}
			}

			return new ResultExpression(stmt, null, decl, emptyAuxVars, overappr);
		} else if (r instanceof ResultSkip) {
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

		ResultExpression condResult = (ResultExpression) main.dispatch(node.getConditionExpression());
		condResult = condResult.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
		condResult = ConvExpr.rexIntToBoolIfNecessary(loc, condResult);
		RValue cond = (RValue) condResult.lrVal;
		decl.addAll(condResult.decl);
		stmt.addAll(condResult.stmt);
		overappr.addAll(condResult.overappr);
		List<HavocStatement> havocs = createHavocsForNonMallocAuxVars(condResult.auxVars);

		Result thenResult = main.dispatch(node.getThenClause());
		List<Statement> thenStmt = new ArrayList<Statement>();
		thenStmt.addAll(havocs);
		if (thenResult instanceof ResultExpression) {
			ResultExpression re = (ResultExpression) thenResult;
			decl.addAll(re.decl);
			thenStmt.addAll(re.stmt);
		} else if (thenResult instanceof Result) {
			if (thenResult.node instanceof Body) {
				Body thenPart = (Body) (thenResult.node);
				thenStmt.addAll(Arrays.asList(thenPart.getBlock()));
				decl.addAll(Arrays.asList(thenPart.getLocalVars()));
			} else if (thenResult instanceof ResultSkip) {
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
			if (elseResult instanceof ResultExpression) {
				ResultExpression re = (ResultExpression) elseResult;
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
		return new ResultExpression(stmt, null, decl, emptyAuxVars, overappr);
	}

	/**
	 * Takes all auxvars, partitions them into ones of malloc-type and the rest.
	 * Returns havoc statements for the rest.
	 * 
	 * @param auxVars
	 * @return
	 */
	public static List<HavocStatement> createHavocsForNonMallocAuxVars(Map<VariableDeclaration, ILocation> auxVars) {
		LinkedHashMap<VariableDeclaration, ILocation> nonMallocAuxVars = new LinkedHashMap<>();
		for (Entry<VariableDeclaration, ILocation> e : auxVars.entrySet()) {
			assert e.getKey().getVariables().length == 1 : "we always define only one auxvar at once, right?";
			assert e.getKey().getVariables()[0].getIdentifiers().length == 1 : "we always define only one auxvar at once, right?";
			if (!e.getKey().getVariables()[0].getIdentifiers()[0].contains(AUXVAR.MALLOC.getId()))
				nonMallocAuxVars.put(e.getKey(), e.getValue());
		}
		return Dispatcher.createHavocsForAuxVars(nonMallocAuxVars);
	}

	@Override
	public Result visit(Dispatcher main, IASTWhileStatement node) {
		ResultExpression condResult = (ResultExpression) main.dispatch(node.getCondition());
		String loopLabel = main.nameHandler.getGloballyUniqueIdentifier(SFO.LOOPLABEL);
		mInnerMostLoopLabel.push(loopLabel);
		Result bodyResult = main.dispatch(node.getBody());
		mInnerMostLoopLabel.pop();
		return handleLoops(main, node, bodyResult, condResult, loopLabel);
	}

	@Override
	public Result visit(Dispatcher main, IASTForStatement node) {
		String loopLabel = main.nameHandler.getGloballyUniqueIdentifier(SFO.LOOPLABEL);
		return handleLoops(main, node, null, null, loopLabel);
	}

	@Override
	public Result visit(Dispatcher main, IASTDoStatement node) {
		ResultExpression condResult = (ResultExpression) main.dispatch(node.getCondition());
		String loopLabel = main.nameHandler.getGloballyUniqueIdentifier(SFO.LOOPLABEL);
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
		ResultExpression contResult = new ResultExpression(stmt, null);
		return contResult;
	}

	@Override
	public Result visit(Dispatcher main, IASTExpressionList node) {
		ResultExpressionList result = new ResultExpressionList();
		for (IASTExpression expr : node.getExpressions()) {
			Result r = main.dispatch(expr);
			assert r instanceof ResultExpression;
			result.list.add((ResultExpression) r);
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
		ResultExpressionListRec result = new ResultExpressionListRec();
		for (IASTInitializerClause i : node.getClauses()) {
			Result r = main.dispatch(i);
			if (r instanceof ResultExpressionListRec) {
				result.list.add((ResultExpressionListRec) r);
			} else if (r instanceof ResultExpression) {
				ResultExpression rex = (ResultExpression) r;
				rex = rex.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
				result.list.add(new ResultExpressionListRec(rex.stmt, rex.lrVal, rex.decl, rex.auxVars, rex.overappr));
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
		return mFunctionHandler.handleFunctionCallExpression(main, mMemoryHandler, mStructHandler, node);
	}

	@Override
	public Result visit(Dispatcher main, IASTBreakStatement node) {
		ArrayList<Statement> stmt = new ArrayList<Statement>();
		stmt.add(new BreakStatement(LocationFactory.createCLocation(node)));
		return new ResultExpression(stmt, null);
	}

	@Override
	public Result visit(Dispatcher main, IASTNullStatement node) {
		return new ResultSkip();
	}

	@Override
	public Result visit(Dispatcher main, IASTSwitchStatement node) {
		// FIXME : This is not exactly as described in C99 standard!
		// declarations are allowed like this:
		// switch ([COND])
		// { [DECL]* [[CASE|DEFAULT]+ [STMT]+ [DECL|STMT]* [BREAK]?] }
		// we allow DECLS after case|default atm but no decls at the beginning!
		ILocation loc = LocationFactory.createCLocation(node);
		ArrayList<Statement> stmt = new ArrayList<Statement>();
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>();
		List<Overapprox> overappr = new ArrayList<Overapprox>();
		Map<VariableDeclaration, ILocation> emptyAuxVars = new LinkedHashMap<VariableDeclaration, ILocation>();
		Result switchParam = main.dispatch(node.getControllerExpression());
		assert switchParam instanceof ResultExpression;
		ResultExpression l = ((ResultExpression) switchParam).switchToRValueIfNecessary(main, mMemoryHandler,
				mStructHandler, loc);
		stmt.addAll(l.stmt);
		decl.addAll(l.decl);
		auxVars.putAll(l.auxVars);
		overappr.addAll(l.overappr);
		Expression switchArg = l.lrVal.getValue();

		Expression cond = null;
		boolean isFirst = true;
		String breakLabelName = "SWITCH~BREAK~" + node.hashCode();

		ArrayList<Statement> ifBlock = new ArrayList<Statement>();
		this.beginScope();
		for (IASTNode child : node.getBody().getChildren()) {
			ILocation locC = LocationFactory.createCLocation(child);
			if (isFirst && !(child instanceof IASTCaseStatement || child instanceof IASTDefaultStatement)) {
				String msg = "A case/default statement is expected at the beginning of a switch block!";
				throw new IncorrectSyntaxException(locC, msg);
			}
			checkForACSL(main, ifBlock, child, null);
			Result r = main.dispatch(child);
			if (r instanceof ResultExpression) {
				ResultExpression res = (ResultExpression) r;
				if (child instanceof IASTCaseStatement || child instanceof IASTDefaultStatement) {
					if (!isFirst && ifBlock.size() > 0) {
						IfStatement ifStmt = new IfStatement(locC, cond, ifBlock.toArray(new Statement[0]),
								new Statement[0]);
						Map<String, IAnnotations> annots = ifStmt.getPayload().getAnnotations();
						for (Overapprox overapprItem : res.overappr) {
							annots.put(Overapprox.getIdentifier(), overapprItem);
						}
						stmt.add(ifStmt);
					}
					isFirst = false;
					Expression thisCase;
					if (child instanceof IASTCaseStatement)
						thisCase = new BinaryExpression(locC, Operator.COMPEQ, switchArg, res.lrVal.getValue());
					else
						/* default statement */
						thisCase = res.lrVal.getValue();

					if (cond == null) {
						cond = thisCase;
					} else {
						cond = new BinaryExpression(locC, Operator.LOGICOR, cond, thisCase);
					}
					ifBlock = new ArrayList<Statement>();
				}
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
				stmt.addAll(Arrays.asList(b.getBlock()));
			}
		}
		assert cond != null;
		if (ifBlock.size() > 0) {
			IfStatement ifStmt = new IfStatement(loc, cond, ifBlock.toArray(new Statement[0]), new Statement[0]);
			Map<String, IAnnotations> annots = ifStmt.getPayload().getAnnotations();
			for (Overapprox overapprItem : overappr) {
				annots.put(Overapprox.getIdentifier(), overapprItem);
			}
			stmt.add(ifStmt);
		}
		checkForACSL(main, stmt, null, node);
		stmt.add(new Label(loc, breakLabelName));
		stmt.addAll(createHavocsForNonMallocAuxVars(auxVars));
		// mallocAuxVars.putAll(getOnlyMallocAuxVars(auxVars));

		this.endScope();
		return new ResultExpression(stmt, null, decl, emptyAuxVars, overappr);
	}

	@Override
	public Result visit(Dispatcher main, IASTCaseStatement node) {
		ResultExpression c = (ResultExpression) main.dispatch(node.getExpression());
		return c.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, LocationFactory.createCLocation(node));
	}

	@Override
	public Result visit(Dispatcher main, IASTDefaultStatement node) {
		ArrayList<Statement> stmt = new ArrayList<Statement>();
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		Map<VariableDeclaration, ILocation> emptyAuxVars = new LinkedHashMap<VariableDeclaration, ILocation>(0);
		List<Overapprox> overappr = new ArrayList<Overapprox>();
		return new ResultExpression(stmt, new RValue(new BooleanLiteral(LocationFactory.createCLocation(node), true), new CPrimitive(
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
		if (r instanceof ResultExpression) {
			ResultExpression res = (ResultExpression) r;
			decl.addAll(res.decl);
			stmt.addAll(res.stmt);
			overappr.addAll(res.overappr);
			return new ResultExpression(stmt, res.lrVal, decl, emptyAuxVars, overappr);
		} else if (r instanceof ResultSkip) {
			return new ResultExpression(stmt, null, decl, emptyAuxVars);
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
			return new ResultExpression(stmt, expr, decl, emptyAuxVars);
		}
	}

	@Override
	public Result visit(Dispatcher main, IASTGotoStatement node) {
		ArrayList<Statement> stmt = new ArrayList<Statement>();
		String[] name = new String[] { node.getName().toString() };
		stmt.add(new GotoStatement(LocationFactory.createCLocation(node), name));
//		Map<VariableDeclaration, ILocation> emptyAuxVars = new LinkedHashMap<VariableDeclaration, ILocation>(0);
		return new ResultExpression(stmt, null);
	}

	@Override
	public Result visit(Dispatcher main, IASTCastExpression node) {
		ILocation loc = LocationFactory.createCLocation(node); 

		// TODO: check validity of cast?

		ResultTypes resTypes = (ResultTypes) main.dispatch(node.getTypeId().getDeclSpecifier());

		mCurrentDeclaredTypes.push(resTypes);
		ResultDeclaration declResult = (ResultDeclaration) main.dispatch(node.getTypeId().getAbstractDeclarator());
		assert declResult.getDeclarations().size() == 1;
		CType newCType = declResult.getDeclarations().get(0).getType();
		mCurrentDeclaredTypes.pop();
		
		ResultExpression expr = (ResultExpression) main.dispatch(node.getOperand()); 
		if (expr.lrVal.cType.getUnderlyingType() instanceof CArray
				&& newCType.getUnderlyingType() instanceof CPointer) {
			CType valueType = ((CArray) expr.lrVal.cType.getUnderlyingType()).getValueType().getUnderlyingType();
				if (expr.lrVal instanceof HeapLValue)
					expr.lrVal = new RValue(((HeapLValue)expr.lrVal).getAddress(), new CPointer(valueType));
				else
					expr.lrVal = new RValue(expr.lrVal.getValue(), new CPointer(valueType));	
		} else {
			expr = expr.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
		}

		if (newCType instanceof CPointer && expr.lrVal.cType instanceof CPointer) {
			CType newPointsToType = ((CPointer) newCType).pointsToType;
			CType exprPointsToType = ((CPointer) expr.lrVal.cType).pointsToType;
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

		expr.lrVal = castToType(loc, (RValue) expr.lrVal, newCType);

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
		assert resLocCond instanceof ResultExpression;
		ResultExpression reLocCond = (ResultExpression) resLocCond;
		reLocCond = reLocCond.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
		reLocCond = ConvExpr.rexIntToBoolIfNecessary(loc, reLocCond);

		Result rPositive = main.dispatch(node.getPositiveResultExpression());
		assert rPositive instanceof ResultExpression;
		ResultExpression rePositive = (ResultExpression) rPositive;
		rePositive = rePositive.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
		rePositive = ConvExpr.rexBoolToIntIfNecessary(loc, rePositive);

		Result rNegative = main.dispatch(node.getNegativeResultExpression());
		assert rNegative instanceof ResultExpression;
		ResultExpression reNegative = (ResultExpression) rNegative;
		reNegative = reNegative.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
		reNegative = ConvExpr.rexBoolToIntIfNecessary(loc, reNegative);
		
		CastAndConversionHandler.usualArithmeticConversions(main, loc, mMemoryHandler, rePositive, reNegative, false);
		CastAndConversionHandler.doPrimitiveVsPointerConversions(main, loc, mMemoryHandler, rePositive, reNegative);

//		// implicit casting -- not very general
//		if (!rePositive.lrVal.cType.equals(reNegative.lrVal.cType)) {
//			if (rePositive.lrVal.getValue() instanceof IntegerLiteral
//					&& ((IntegerLiteral) rePositive.lrVal.getValue()).getValue().equals("0")
//					&& reNegative.lrVal.cType instanceof CPointer) {
//				rePositive.lrVal = new RValue(new IdentifierExpression(loc, SFO.NULL), reNegative.lrVal.cType);
//			} else if (reNegative.lrVal.getValue() instanceof IntegerLiteral
//					&& ((IntegerLiteral) reNegative.lrVal.getValue()).getValue().equals("0")
//					&& rePositive.lrVal.cType instanceof CPointer) {
//				reNegative.lrVal = new RValue(new IdentifierExpression(loc, SFO.NULL), rePositive.lrVal.cType);
//			} else if (reNegative.lrVal.getValue() == null
//					|| rePositive.lrVal.getValue() == null) {
//				// one of the values is void --> can only come from the call of a void function, i think..
//				//do nothing here.. (should crash later if the value is assigned..)
//			} else {
//				assert false : "types do not match";
//			}
//		}

		ArrayList<Statement> stmt = new ArrayList<Statement>();
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>(0);
		List<Overapprox> overappr = new ArrayList<Overapprox>();

		decl.addAll(reLocCond.decl);
		auxVars.putAll(reLocCond.auxVars);
		stmt.addAll(reLocCond.stmt);
		overappr.addAll(reLocCond.overappr);

		String tmpName = main.nameHandler.getTempVarUID(SFO.AUXVAR.ITE);
		ASTType tmpType = mTypeHandler.ctype2asttype(loc, rePositive.lrVal.cType);
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
		return new ResultExpression(stmt, new RValue(tmpExpr, rePositive.lrVal.cType), decl, auxVars, overappr);
	}

	@Override
	public Result visit(Dispatcher main, IASTArraySubscriptExpression node) {
		return mArrayHandler.handleArraySubscriptExpression(main, mMemoryHandler, mStructHandler, node);
	}

	@Override
	public Result visit(Dispatcher main, IASTInitializerClause node) {
		assert node.getChildren().length == 1;
		Result r = main.dispatch(node.getChildren()[0]);
		assert r instanceof ResultExpression;
		ResultExpression rex = (ResultExpression) r;
		return rex.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, LocationFactory.createCLocation(node));
	}

	@Override
	public Result visit(Dispatcher main, IASTFieldReference node) {
		return mStructHandler.handleFieldReference(main, node, mMemoryHandler);
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
		case IASTTypeIdExpression.op_sizeof:
			ResultTypes rt = (ResultTypes) main.dispatch(node.getTypeId().getDeclSpecifier());
			ResultTypes checked = checkForPointer(main, node.getTypeId().getAbstractDeclarator().getPointerOperators(),
					rt, false);

			return new ResultExpression(new RValue(mMemoryHandler.calculateSizeOf(checked.cType, loc), new CPrimitive(
					PRIMITIVE.INT)));
			// }
		default:
			break;
		}
		String msg = "Unsupported boogie AST node type: " + node.getClass();
		throw new UnsupportedSyntaxException(loc, msg);
	}
	
	@Override
	public Result visit(Dispatcher main, IASTExpression node) {
//		ArrayList<Statement> stmt = new ArrayList<>();
		return null;
	}


	public ResultExpression makeAssignment(Dispatcher main, ILocation loc, ArrayList<Statement> stmt, LRValue lrVal,
			RValue rVal, ArrayList<Declaration> decl, Map<VariableDeclaration, ILocation> auxVars,
			List<Overapprox> overappr) {
		return makeAssignment(main, loc, stmt, lrVal, rVal, decl, auxVars, overappr, null);
	}

	public ResultExpression makeAssignment(Dispatcher main, ILocation loc, ArrayList<Statement> stmt, LRValue lrVal,
			RValue rVal, ArrayList<Declaration> decl, Map<VariableDeclaration, ILocation> auxVars,
			List<Overapprox> overappr, Map<StructLHS, CType> unionFieldsToCType) {
		RValue rightHandSide = rVal; //we may change the content of the right hand side later

		//do implicit cast -- assume the types are compatible
		rightHandSide = castToType(loc, rightHandSide, lrVal.cType);
		
		//for wraparound --> and avoiding it for ints that store pointers
		if (rightHandSide.isIntFromPointer) {
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

			stmt.addAll(mMemoryHandler.getWriteCall(loc, hlv, rightHandSide));

			return new ResultExpression(stmt, rightHandSide, decl, auxVars, overappr);
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
					if (rightHandSide.cType.equals(en.getValue())
							|| (rightHandSide.cType.getUnderlyingType() instanceof CPrimitive && en.getValue() instanceof CPrimitive
							 && ((CPrimitive) rightHandSide.cType.getUnderlyingType()).getGeneralType().equals(((CPrimitive) en.getValue()).getGeneralType())
							 && (mMemoryHandler.calculateSizeOfWithGivenTypeSizes(loc, rightHandSide.cType) 
									 == mMemoryHandler.calculateSizeOfWithGivenTypeSizes(loc, en.getValue())))) {
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
//							String tmpId = main.nameHandler.getTempVarUID(SFO.AUXVAR.UNION);
//							VariableDeclaration tVarDec = new VariableDeclaration(loc, new Attribute[0], new VarList[] { new VarList(loc,
//									new String[] { tmpId }, main.typeHandler.ctype2asttype(loc, en.getValue())) });
//							decl.add(tVarDec);
//							auxVars.put(tVarDec, loc); //ensures that the variable will be havoced (necessary only when we are inside a loop)
//
//							stmt.add(new AssignmentStatement(loc, new LeftHandSide[] { en.getKey() },
//									new Expression[] { new IdentifierExpression(loc, tmpId) }));						
//						}

					} else { //otherwise we consider the value undefined, thus havoc it
						// TODO: maybe not use auxiliary variables so lavishly
						String tmpId = main.nameHandler.getTempVarUID(SFO.AUXVAR.UNION);
						VariableDeclaration tVarDec = new VariableDeclaration(loc, new Attribute[0], new VarList[] { new VarList(loc,
								new String[] { tmpId }, main.typeHandler.ctype2asttype(loc, en.getValue())) });
						decl.add(tVarDec);
						auxVars.put(tVarDec, loc); //ensures that the variable will be havoced (necessary only when we are inside a loop)

						stmt.add(new AssignmentStatement(loc, new LeftHandSide[] { en.getKey() },
								new Expression[] { new IdentifierExpression(loc, tmpId) }));
					}
				}
			}

			if (!mFunctionHandler.noCurrentProcedure())
				mFunctionHandler.checkIfModifiedGlobal(main, BoogieASTUtil.getLHSId(lValue.getLHS()), loc);
			return new ResultExpression(stmt, lValue, decl, auxVars, overappr);
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
	private void checkForACSL(Dispatcher main, ArrayList<Statement> stmt, IASTNode next, IASTNode parent) {
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
					// ACSL at the end of a function
					for (ACSLNode acslNode : mAcsl.mAcsl) {
						if (parent.getFileLocation().getEndingLineNumber() <= acslNode.getStartingLineNumber()) {
							return; // handle later ...
						}
						Result acslResult = main.dispatch(acslNode);
						if (acslResult.node instanceof Statement) {
							if (parent.getFileLocation().getEndingLineNumber() >= acslNode.getEndingLineNumber()
									&& parent.getFileLocation().getStartingLineNumber() <= acslNode
											.getStartingLineNumber()) {
								stmt.add((Statement) acslResult.node);
								try {
									mAcsl = main.nextACSLStatement();
								} catch (ParseException e1) {
									String msg = "Skipped a ACSL node due to: " + e1.getMessage();
									ILocation loc = LocationFactory.createCLocation(parent);
									main.unsupportedSyntax(loc, msg);
								}
							}
						} else {
							String msg = "Unexpected ACSL comment: " + acslResult.node.getClass();
							ILocation loc = LocationFactory.createCLocation(parent);
							throw new IncorrectSyntaxException(loc, msg);
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
							stmt.add((Statement) acslResult.node);
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
	public ResultTypes checkForPointer(Dispatcher main, IASTPointerOperator[] pointerOps, ResultTypes resType,
			boolean putOnHeap) {
		if (putOnHeap || pointerOps.length != 0) {
			// TODO : not sure, if this is enough!
			// There could be multiple PointerOperators (i.e.
			// IASTPointer) - what does that mean for the translation?
			// String typeId = resType.cvar.toString();
			ASTType t = MemoryHandler.POINTER_TYPE;
			CType cvar = new CPointer(resType.cType);
			return new ResultTypes(t, resType.isConst, resType.isVoid, cvar);
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

	public RValue doPointerArithPointerAndPointer(Dispatcher main, int operator, ILocation loc, RValue ptr1, RValue ptr2) {
		return new RValue(createArithmeticExpression(operator, new StructAccessExpression(loc, ptr1.getValue(),
				SFO.POINTER_OFFSET), new StructAccessExpression(loc, ptr2.getValue(), SFO.POINTER_OFFSET), loc),
				new CPrimitive(PRIMITIVE.INT));
		// TODO: which solution is better? -- maybe switch back once we have
		// Pointer to int conversion
		// return new RValue(doPointerArith(main, operator, loc,
		// ptr1.getValue(),
		// new StructAccessExpression(loc, ptr2.getValue(), SFO.POINTER_OFFSET),
		// null),
		// ptr2.cType);
	}

	/**
	 * Add up a Pointer and an integer (both given as RValues) to a new Pointer
	 * 
	 * @param main
	 *            The MainDispatcher
	 * @param operator
	 * @param loc
	 * @param ptr
	 * @param integer
	 * @param valueType
	 *            The value type the pointer points to (we need it because we
	 *            have to multiply with its size) if valueType is null, then we
	 *            leave out the multiplication
	 * @return a pointer of the form: {base: ptr.base, offset: ptr.offset +
	 *         integer * sizeof(valueType)}
	 */
	public RValue doPointerArithPointerAndInteger(Dispatcher main, int operator, ILocation loc, RValue ptr,
			RValue integer, CType valueType) {
		Expression ptrAddress = ptr.getValue();
		Expression newPointer = doPointerArith(main, operator, loc, ptrAddress, integer.getValue(), valueType);
		return new RValue(newPointer, ptr.cType);
	}

	/**
	 * Like doPointerArtih(... RValue ptr, RValue integer, ...) but with
	 * Expressions instead of RValues.
	 */
	public Expression doPointerArith(Dispatcher main, int operator, ILocation loc, Expression ptrAddress,
			Expression integer, CType valueType) {
		Expression pointerBase = MemoryHandler.getPointerBaseAddress(ptrAddress, loc);
		Expression pointerOffset = MemoryHandler.getPointerOffset(ptrAddress, loc);
		Expression timesSizeOf = null;
		if (valueType != null) {
			timesSizeOf = createArithmeticExpression(IASTBinaryExpression.op_multiply, integer,
					mMemoryHandler.calculateSizeOf(valueType, loc), loc);
		} else {
			timesSizeOf = integer;
		}
		Expression sum = createArithmeticExpression(operator, pointerOffset, timesSizeOf, loc);
		StructConstructor newPointer = MemoryHandler.constructPointerFromBaseAndOffset(pointerBase, sum, loc);
		return newPointer;
	}

	/**
	 * Translates arithmetic binary expressions.
	 * 
	 * @param op
	 *            the IASTBinaryExpression.Operator
	 * @param left
	 *            the left part of the expression
	 * @param right
	 *            the right part of the expression
	 * @param loc
	 *            the location of the translated node
	 * @return the resulting binary expres
	 */
	public static Expression createArithmeticExpression(int op, Expression left, Expression right, ILocation loc) {
		BinaryExpression.Operator operator;
		boolean bothAreIntegerLiterals = left instanceof IntegerLiteral && right instanceof IntegerLiteral;
		BigInteger leftValue = null;
		BigInteger rightValue = null;
		//TODO: add checks for UnaryExpression (otherwise we don't catch negative constants, here) --> or remove all the cases 
		//(if-then-else conditions are checked for being constant in RCFGBuilder anyway, so this is merely a decision of readability of Boogie code..)
		if (left instanceof IntegerLiteral)
			leftValue = new BigInteger(((IntegerLiteral) left).getValue());
		if (right instanceof IntegerLiteral)
			rightValue = new BigInteger(((IntegerLiteral) right).getValue());
		//TODO: make this more general, (a + 4) + 4 may still occur this way..
		String constantResult = "";
		switch (op) {
		case IASTBinaryExpression.op_minusAssign:
		case IASTBinaryExpression.op_minus:
			operator = Operator.ARITHMINUS;
			if (bothAreIntegerLiterals) {
				constantResult = 
						leftValue
						.subtract(rightValue).toString();
				return new IntegerLiteral(loc, constantResult);
			} else {
				return new BinaryExpression(loc, operator, left, right);
			}
		case IASTBinaryExpression.op_multiplyAssign:
		case IASTBinaryExpression.op_multiply:
			operator = Operator.ARITHMUL;
			if (bothAreIntegerLiterals) {
				constantResult = 
						leftValue
							.multiply(rightValue).toString();
				return new IntegerLiteral(loc, constantResult);
			} else {
				return new BinaryExpression(loc, operator, left, right);
			}
		case IASTBinaryExpression.op_divideAssign:
		case IASTBinaryExpression.op_divide:
			operator = Operator.ARITHDIV;
			/* In C the semantics of integer division is "rounding towards zero".
			 * In Boogie euclidian division is used.
			 * We translate a / b into
			 *  (a < 0) ? ( (b < 0) ? (a/b)+1 : (a/b)-1) : a/b
			 */
			if (bothAreIntegerLiterals) {
				constantResult = 
						leftValue
							.divide(rightValue).toString();
				return new IntegerLiteral(loc, constantResult);
			} else {
				BinaryExpression leftSmallerZero = new BinaryExpression(loc, 
						BinaryExpression.Operator.COMPLT, 
						left,
						new IntegerLiteral(loc, SFO.NR0));
				BinaryExpression rightSmallerZero = new BinaryExpression(loc, 
						BinaryExpression.Operator.COMPLT, 
						right,
						new IntegerLiteral(loc, SFO.NR0));
				BinaryExpression normalDivision = new BinaryExpression(loc, operator, left, right);
				if (left instanceof IntegerLiteral) {
					if (leftValue.signum() == 1) {
						return normalDivision;
					} else if (leftValue.signum() == -1) {
						return new IfThenElseExpression(loc, rightSmallerZero, 
									new BinaryExpression(loc, 
											BinaryExpression.Operator.ARITHMINUS, 
											normalDivision, 
											new IntegerLiteral(loc, SFO.NR1)), 
									new BinaryExpression(loc, 
											BinaryExpression.Operator.ARITHPLUS, 
											normalDivision, 
											new IntegerLiteral(loc, SFO.NR1)));
					} else {
						return new IntegerLiteral(loc, SFO.NR0);
					}
				} else if (right instanceof IntegerLiteral) {
					if (rightValue.signum() == 1) {
						return new IfThenElseExpression(loc, leftSmallerZero, 
								new BinaryExpression(loc, 
										BinaryExpression.Operator.ARITHPLUS, 
										normalDivision, 
										new IntegerLiteral(loc, SFO.NR1)), 
								normalDivision);
					} else if (rightValue.signum() == -1) {
						return new IfThenElseExpression(loc, leftSmallerZero, 
									new BinaryExpression(loc, 
											BinaryExpression.Operator.ARITHMINUS, 
											normalDivision, 
											new IntegerLiteral(loc, SFO.NR1)), 
									normalDivision);
					} else {
						assert false : "program divides by (constant) 0";
					}
				} else {
					return new IfThenElseExpression(loc, leftSmallerZero, 
							new IfThenElseExpression(loc, rightSmallerZero, 
									new BinaryExpression(loc, 
											BinaryExpression.Operator.ARITHMINUS, 
											normalDivision, 
											new IntegerLiteral(loc, SFO.NR1)), 
									new BinaryExpression(loc, 
											BinaryExpression.Operator.ARITHPLUS, 
											normalDivision, 
											new IntegerLiteral(loc, SFO.NR1))), 
						normalDivision);
				}
			}
		case IASTBinaryExpression.op_moduloAssign:
		case IASTBinaryExpression.op_modulo:
			operator = Operator.ARITHMOD;
			/* In C the semantics of integer division is "rounding towards zero".
			 * In Boogie euclidian division is used.
			 * We translate a % b into
			 *  (a < 0) ? ( (b < 0) ? (a%b)-b : (a%b)+b) : a%b
			 */
			//modulo on bigInteger does not seem to follow the "multiply, add, and get the result back"-rule, together with its division..
			if (bothAreIntegerLiterals) {
				if (leftValue.signum() == 1 || leftValue.signum() == 0) {
					if (rightValue.signum() == 1) {
						constantResult = 
								leftValue.mod(rightValue).toString();
					} else if (rightValue.signum() == -1) {
						constantResult = 
								leftValue.mod(rightValue.negate()).toString();
					} else {
						constantResult = "0";
					}
				} else if (leftValue.signum() == -1) {
					if (rightValue.signum() == 1) {
						constantResult = 
								(leftValue.negate().mod(rightValue)).negate().toString();					
					} else if (rightValue.signum() == -1) {
						constantResult = 
								(leftValue.negate().mod(rightValue.negate())).negate().toString();					
					} else {
						constantResult = "0";
					}
				} 
				return new IntegerLiteral(loc, constantResult);
			} else {
				BinaryExpression leftSmallerZero = new BinaryExpression(loc, 
						BinaryExpression.Operator.COMPLT, 
						left,
						new IntegerLiteral(loc, SFO.NR0));
				BinaryExpression rightSmallerZero = new BinaryExpression(loc, 
						BinaryExpression.Operator.COMPLT, 
						right,
						new IntegerLiteral(loc, SFO.NR0));
				BinaryExpression normalModulo = new BinaryExpression(loc, operator, left, right);
				if (left instanceof IntegerLiteral) {
					if (leftValue.signum() == 1) {
						return normalModulo;
					} else if (leftValue.signum() == -1) {
						return new IfThenElseExpression(loc, rightSmallerZero, 
								new BinaryExpression(loc, 
										BinaryExpression.Operator.ARITHPLUS, 
										normalModulo, 
										right), 
										new BinaryExpression(loc, 
												BinaryExpression.Operator.ARITHMINUS, 
												normalModulo, 
												right));
					} else {
						return new IntegerLiteral(loc, SFO.NR0);
					}
				} else if (right instanceof IntegerLiteral) {
					if (rightValue.signum() == 1) {
						return new IfThenElseExpression(loc, leftSmallerZero, 
								new BinaryExpression(loc, 
										BinaryExpression.Operator.ARITHMINUS, 
										normalModulo, 
										right), 
										normalModulo);
					} else if (rightValue.signum() == -1) {
						return new IfThenElseExpression(loc, leftSmallerZero, 
								new BinaryExpression(loc, 
										BinaryExpression.Operator.ARITHPLUS, 
										normalModulo, 
										right), 
										normalModulo);
					} else {
						assert false : "program divides by (constant) 0";
					}
				} else {
					return new IfThenElseExpression(loc, leftSmallerZero, 
							new IfThenElseExpression(loc, rightSmallerZero, 
									new BinaryExpression(loc, 
											BinaryExpression.Operator.ARITHPLUS, 
											normalModulo, 
											right), 
											new BinaryExpression(loc, 
													BinaryExpression.Operator.ARITHMINUS, 
													normalModulo, 
													right)), 
													normalModulo);
				}
			}
		case IASTBinaryExpression.op_plusAssign:
		case IASTBinaryExpression.op_plus:
			operator = Operator.ARITHPLUS;
			if (bothAreIntegerLiterals) {
				constantResult = 
						leftValue
							.add(rightValue).toString();
				return new IntegerLiteral(loc, constantResult);
			} else {
				return new BinaryExpression(loc, operator, left, right);
			}
		default:
			String msg = "Unknown or unsupported arithmetic expression";
			throw new UnsupportedSyntaxException(loc, msg);
		}
//		if (bothAreIntegerLiterals) {
//			return new IntegerLiteral(loc, constantResult);
//		} else {
//			return new BinaryExpression(loc, operator, left, right);
//		}
	}

	/**
	 * Translates bitwise binary expressions.
	 * 
	 * @param op
	 *            the IASTBinaryExpression.Operator
	 * @param left
	 *            the left part of the expression
	 * @param right
	 *            the right part of the expression
	 * @param loc
	 *            the location of the translated node
	 * @return the resulting binary expression
	 */
	private Expression createBitwiseExpression(int op, Expression left, Expression right, ILocation loc) {
		String operatorName;
		boolean isUnary = (left == null && op == IASTUnaryExpression.op_tilde);
		if (isUnary) {
			operatorName = "bitwiseComplement";
		} else {
			switch (op) {
			case IASTBinaryExpression.op_binaryAnd:
			case IASTBinaryExpression.op_binaryAndAssign:
				operatorName = "bitwiseAnd";
				break;
			case IASTBinaryExpression.op_binaryOr:
			case IASTBinaryExpression.op_binaryOrAssign:
				operatorName = "bitwiseOr";
				break;
			case IASTBinaryExpression.op_binaryXor:
			case IASTBinaryExpression.op_binaryXorAssign:
				operatorName = "bitwiseXor";
				break;
			case IASTBinaryExpression.op_shiftLeft:
			case IASTBinaryExpression.op_shiftLeftAssign:
				operatorName = "shiftLeft";
				break;
			case IASTBinaryExpression.op_shiftRight:
			case IASTBinaryExpression.op_shiftRightAssign:
				operatorName = "shiftRight";
				break;
			default:
				String msg = "Unknown or unsupported arithmetic expression";
				throw new UnsupportedSyntaxException(loc, msg);
			}
		}

		if (!this.mFunctions.containsKey(operatorName)) {
			FunctionDeclaration d;
			ASTType intType = new PrimitiveType(loc, SFO.INT);
			VarList b = new VarList(loc, new String[] { "b" }, intType);
			VarList out = new VarList(loc, new String[] { "out" }, intType);
			if (isUnary) {
				d = new FunctionDeclaration(loc, new Attribute[0], "~" + operatorName, new String[0],
						new VarList[] { b }, out);
			} else {
				VarList a = new VarList(loc, new String[] { "a" }, intType);
				d = new FunctionDeclaration(loc, new Attribute[0], "~" + operatorName, new String[0], new VarList[] {
						a, b }, out);
			}
			this.mFunctions.put(operatorName, d);
		}
		Expression[] arguments = new Expression[isUnary ? 1 : 2];
		if (isUnary) {
			arguments[0] = right;
		} else {
			arguments[0] = left;
			arguments[1] = right;
		}
		return new FunctionApplication(loc, "~" + operatorName, arguments);
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
	private Result handleLoops(Dispatcher main, IASTStatement node, Result bodyResult, ResultExpression condResult,
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
				if (initializer instanceof ResultExpression) {
					ResultExpression rExp = (ResultExpression) initializer;
					stmt.addAll(rExp.stmt);
					decl.addAll(rExp.decl);
					overappr.addAll(rExp.overappr);
				} else if (initializer instanceof ResultSkip) {
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
				condResult = (ResultExpression) main.dispatch(cCondExpr);
			else
				condResult = new ResultExpression(new RValue((new BooleanLiteral(loc, true)), new CPrimitive(
						PRIMITIVE.BOOL), true), new LinkedHashMap<VariableDeclaration, ILocation>(0));

			mInnerMostLoopLabel.push(loopLabel);
			bodyResult = main.dispatch(forStmt.getBody());
			mInnerMostLoopLabel.pop();
		}
		assert (main.isAuxVarMapcomplete(condResult.decl, condResult.auxVars));

		ArrayList<Statement> bodyBlock = new ArrayList<Statement>();
		if (bodyResult instanceof ResultExpression) {
			ResultExpression re = (ResultExpression) bodyResult;
			decl.addAll(re.decl);
			overappr.addAll(re.overappr);
			bodyBlock.addAll(re.stmt);
		} else if (bodyResult instanceof Result) {
			if (bodyResult.node instanceof Body) {
				Body body = (Body) (bodyResult.node);
				bodyBlock.addAll(Arrays.asList(body.getBlock()));
				decl.addAll(Arrays.asList(body.getLocalVars()));
			} else if (bodyResult instanceof ResultSkip) {
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
			if (iterator instanceof ResultExpressionList) {
				for (ResultExpression el : ((ResultExpressionList) iterator).list) {
					bodyBlock.addAll(el.stmt);
					decl.addAll(el.decl);
					assert (main.isAuxVarMapcomplete(el.decl, el.auxVars));
					bodyBlock.addAll(createHavocsForNonMallocAuxVars(el.auxVars));
				}
			} else if (iterator instanceof ResultExpression) {
				ResultExpression iteratorRE = (ResultExpression) iterator;
				bodyBlock.addAll(iteratorRE.stmt);
				decl.addAll(iteratorRE.decl);
				overappr.addAll(iteratorRE.overappr);
				assert (main.isAuxVarMapcomplete(iteratorRE.decl, iteratorRE.auxVars));
				bodyBlock.addAll(createHavocsForNonMallocAuxVars(iteratorRE.auxVars));
			} else {
				String msg = "Uninplemented type of loop iterator: " + iterator.getClass();
				throw new UnsupportedSyntaxException(loc, msg);
			}
		}

		condResult = condResult.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
		condResult = ConvExpr.rexIntToBoolIfNecessary(loc, condResult);
		decl.addAll(condResult.decl);
		RValue condRVal = (RValue) condResult.lrVal;
		IfStatement ifStmt;
		{
			Expression cond = new UnaryExpression(loc, UnaryExpression.Operator.LOGICNEG, condRVal.getValue());
			ArrayList<Statement> thenStmt = new ArrayList<Statement>(
					createHavocsForNonMallocAuxVars(condResult.auxVars));
			thenStmt.add(new BreakStatement(loc));
			Statement[] elseStmt = createHavocsForNonMallocAuxVars(condResult.auxVars).toArray(new Statement[0]);
			ifStmt = new IfStatement(loc, cond, thenStmt.toArray(new Statement[0]), elseStmt);
		}

		if (node instanceof IASTWhileStatement || node instanceof IASTForStatement) {
			bodyBlock.add(0, ifStmt);
			if (node instanceof IASTWhileStatement)
				bodyBlock.add(0, new Label(loc, loopLabel));
			bodyBlock.addAll(0, condResult.stmt);
		} else if (node instanceof IASTDoStatement) {
			bodyBlock.addAll(condResult.stmt);
			bodyBlock.add(new Label(loc, loopLabel));
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
					if (retranslateRes instanceof ResultContract) {
						ResultContract resContr = (ResultContract) retranslateRes;
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
				bodyBlock = mMemoryHandler.insertMallocs(main, bodyBlock);
				for (SymbolTableValue stv : mSymbolTable.currentScopeValues())
					if (!stv.isBoogieGlobalVar()) {
						decl.add(stv.getBoogieDecl());
					}
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
		return new ResultExpression(stmt, null, decl, emptyAuxVars, overappr);
	}

	@Override
	public boolean isHeapVar(String boogieId) {
		return mBoogieIdsOfHeapVars.contains(boogieId);
	}

	protected StorageClass scConstant2StorageClass(int storageClass) {
		switch (storageClass) {
		case IASTDeclSpecifier.sc_auto:
			return StorageClass.AUTO;
		case IASTDeclSpecifier.sc_extern:
			return StorageClass.EXTERN;
		case IASTDeclSpecifier.sc_mutable:
			return StorageClass.MUTABLE;
		case IASTDeclSpecifier.sc_register:
			return StorageClass.REGISTER;
		case IASTDeclSpecifier.sc_static:
			return StorageClass.STATIC;
		case IASTDeclSpecifier.sc_typedef:
			return StorageClass.TYPEDEF;
		case IASTDeclSpecifier.sc_unspecified:
			return StorageClass.UNSPECIFIED;
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
	private Result handleEnumDeclaration(Dispatcher main, IASTSimpleDeclaration node) {
		Result r = main.dispatch(node.getDeclSpecifier());
		assert r instanceof ResultTypes;
		ResultTypes rt = (ResultTypes) r;
		assert rt.cType instanceof CEnum;
		CEnum cEnum = (CEnum) rt.cType;
		ILocation loc = LocationFactory.createCLocation(node);
		ASTType at = new PrimitiveType(loc, SFO.INT);
		String enumId = cEnum.getIdentifier();
		Expression oldValue = null;
		Expression[] enumDomain = new Expression[cEnum.getFieldCount()];
		
		ResultDeclaration result = new ResultDeclaration();
		
		for (int i = 0; i < cEnum.getFieldCount(); i++) {
			String fId = cEnum.getFieldIds()[i];
			String bId = enumId + "~" + fId;
			VarList vl = new VarList(loc, new String[] { bId }, at);
			ConstDeclaration cd = new ConstDeclaration(loc, new Attribute[0], false, vl, null, false);
			mDeclarationsGlobalInBoogie.put(cd, new CDeclaration(cEnum, fId));
			Expression l = new IdentifierExpression(loc, bId);
			Expression newValue = oldValue;
			if (oldValue == null && cEnum.getFieldValue(fId) == null) {
				newValue = new IntegerLiteral(loc, SFO.NR0);
			} else if (cEnum.getFieldValue(fId) == null) {
				newValue = createArithmeticExpression(IASTBinaryExpression.op_plus, oldValue, new IntegerLiteral(loc, SFO.NR1), loc);
			} else {
				newValue = cEnum.getFieldValue(fId);
			}
			oldValue = newValue;
			enumDomain[i] = newValue;
			mAxioms.add(new Axiom(loc, new Attribute[0], new BinaryExpression(loc, Operator.COMPEQ, l, newValue)));
			mSymbolTable.put(fId, new SymbolTableValue(bId, cd, new CDeclaration(cEnum, fId), true,
					scConstant2StorageClass(node.getDeclSpecifier().getStorageClass()))); // FIXME
																							// ??
		}
		return result;
	}

	public Result handleLabelCommonCode(Dispatcher main, IASTLabelStatement node, ILocation loc) {

		ArrayList<Statement> stmt = new ArrayList<Statement>();
		ArrayList<Declaration> decl = new ArrayList<Declaration>();
		Map<VariableDeclaration, ILocation> emptyAuxVars = new LinkedHashMap<VariableDeclaration, ILocation>(0);
		List<Overapprox> overappr = new ArrayList<Overapprox>();
		String label = node.getName().toString();
		stmt.add(new Label(loc, label));
		Result r = main.dispatch(node.getNestedStatement());
		if (r instanceof ResultExpression) {
			ResultExpression res = (ResultExpression) r;
			decl.addAll(res.decl);
			stmt.addAll(res.stmt);
			overappr.addAll(res.overappr);
			return new ResultExpression(stmt, res.lrVal, decl, emptyAuxVars, overappr);
		} else if (r instanceof ResultSkip) {
			return new ResultExpression(stmt, null, decl, emptyAuxVars, overappr);
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
			return new ResultExpression(stmt, expr, decl, emptyAuxVars, overappr);
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
	public void completeTypeDeclaration(CStruct incompleteStruct, CStruct cvar) {
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

	@Override
	public RValue castToType(ILocation loc, RValue rValIn, CType expectedTypeRaw) {
		CType expectedType = expectedTypeRaw.getUnderlyingType();
		
		RValue rVal = new RValue(rValIn); //better make a new one, right??

		BigInteger maxPtrValue = new BigInteger("2").pow(mMemoryHandler.typeSizeConstants.sizeOfPointerType * 8);
		IntegerLiteral max_Pointer = new IntegerLiteral(loc, maxPtrValue.toString());
		// cast pointer -> integer/other pointer
		CType rValUlType = rVal.cType.getUnderlyingType();
		if (rValUlType instanceof CPointer) {
			// cast from pointer to integer
			if (expectedType instanceof CPrimitive &&
					((CPrimitive) expectedType).getGeneralType() == GENERALPRIMITIVE.INTTYPE) {
				Expression e = null;
				if (mMemoryHandler.useConstantTypeSizes) {
					e = createArithmeticExpression(IASTBinaryExpression.op_plus,
							createArithmeticExpression(IASTBinaryExpression.op_multiply, 
									MemoryHandler.getPointerBaseAddress(rVal.getValue(),  loc), 
									max_Pointer, 
									loc),
							MemoryHandler.getPointerOffset(rVal.getValue(), loc), 
							loc);
				} else {
					e = MemoryHandler.getPointerOffset(rVal.getValue(), loc);
				}
				rVal = new RValue(e, expectedType);
				rVal.isIntFromPointer = true;
			}
			// type is changed
//			else if (!(expectedType.getUnderlyingType() instanceof CPointer)) { //why did I make this distinction??
			else {
				rVal.cType = expectedType;
			}
		} else if (rValUlType instanceof CPrimitive) {
			CPrimitive cprim = (CPrimitive) rValUlType;
			if (cprim.getGeneralType() == GENERALPRIMITIVE.INTTYPE) {
				if (expectedType instanceof CPointer) {// cast integer -> pointer
					Expression e = null;
					if (mMemoryHandler.useConstantTypeSizes) {
						e = MemoryHandler.constructPointerFromBaseAndOffset(
								createArithmeticExpression(IASTBinaryExpression.op_divide,
										rVal.getValue(),
										max_Pointer, 
										loc),
										createArithmeticExpression(IASTBinaryExpression.op_modulo,
												rVal.getValue(),
												max_Pointer, 
												loc),
												loc);
					} else {
						e = MemoryHandler.constructPointerFromBaseAndOffset(new IntegerLiteral(loc, "0"),
								rVal.getValue(), loc);
					}
					rVal = new RValue(e, expectedType);
				}
			} else if (cprim.getGeneralType() == GENERALPRIMITIVE.FLOATTYPE) { 
				if (expectedType instanceof CPrimitive) {
					if (((CPrimitive) expectedType).getGeneralType() == GENERALPRIMITIVE.INTTYPE) {
						rVal = new RValue(new FunctionApplication(loc, SFO.TO_INT, new Expression[] { rVal.getValue() }), 
								expectedType);
					}
				}
		
			}
		}
		return rVal;
	}

	@Override
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
