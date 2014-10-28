package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;

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
import org.eclipse.cdt.core.dom.ast.IASTDeclarationStatement;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTDefaultStatement;
import org.eclipse.cdt.core.dom.ast.IASTDoStatement;
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
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTNullStatement;
import org.eclipse.cdt.core.dom.ast.IASTParameterDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTPointer;
import org.eclipse.cdt.core.dom.ast.IASTPointerOperator;
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
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.PRFunctionHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.StructHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.PRSymbolTableValue;
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
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultExpression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultExpressionListRec;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultSkip;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultTypes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.ConvExpr;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.ISOIEC9899TC3;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ICHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.model.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.CACSL2BoogieBacktranslator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.UNSIGNED_TREATMENT;
import de.uni_freiburg.informatik.ultimate.result.Check;
import de.uni_freiburg.informatik.ultimate.util.LinkedScopedHashMap;

public class PRCHandler extends CHandler {
	
    private LinkedHashSet<IASTNode> variablesOnHeap;

    public HashSet<IASTNode> getVarsForHeap() {
    	return variablesOnHeap;
    }	

    ////////////
	

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
	private ArrayDeque<ResultTypes> mCurrentDeclaredTypes;

	private Logger mLogger;

	
	public PRCHandler(Dispatcher main, CACSL2BoogieBacktranslator backtranslator, boolean errorLabelWarning,
			Logger logger, ITypeHandler typeHandler) {
		super(main, backtranslator, errorLabelWarning, logger, typeHandler);
		
		variablesOnHeap = new LinkedHashSet<>();

		mLogger = logger;
		this.mTypeHandler = typeHandler;

//		mPreferences= new UltimatePreferenceStore(Activator.s_PLUGIN_ID);
		
//		this.mUnsignedTreatment = mPreferences.getEnum(CACSLPreferenceInitializer.LABEL_UNSIGNED_TREATMENT, 
//				CACSLPreferenceInitializer.UNSIGNED_TREATMENT.class);

		this.mArrayHandler = new ArrayHandler();
		this.mFunctionHandler = new PRFunctionHandler();
		this.mStructHandler = new StructHandler();
//		boolean checkPointerValidity = mPreferences.getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_POINTER_VALIDITY);
		this.mMemoryHandler = new MemoryHandler(mFunctionHandler, false);
//		this.mInitHandler = new InitializationHandler(mFunctionHandler, mStructHandler, mMemoryHandler);
//		this.mPostProcessor = new PostProcessor(main, mLogger);
		
		this.mSymbolTable = new SymbolTable(main);
		this.mFunctions = new LinkedHashMap<String, FunctionDeclaration>();
//		this.mDeclarationsGlobalInBoogie = new LinkedHashMap<Declaration, CDeclaration>();
//		this.mAxioms = new LinkedHashSet<Axiom>();
//		this.mBacktranslator = backtranslator;
		this.mContract = new ArrayList<ACSLNode>();
//		this.mErrorLabelWarning = errorLabelWarning;
//		this.mInnerMostLoopLabel = new Stack<String>();

//		this.mBoogieIdsOfHeapVars = new LinkedHashSet<String>();
		this.mCurrentDeclaredTypes = new ArrayDeque<ResultTypes>();
	}
	
	@Override
	public Result visit(Dispatcher main, IASTTranslationUnit node) {

		ILocation loc = LocationFactory.createCLocation(node);

		for (IASTNode child : node.getChildren()) {
			main.dispatch(child);
		}
		ArrayList<Declaration> decl = new ArrayList<>();

		return new Result(new Unit(loc, decl.toArray(new Declaration[0])));
	}

	@Override
	public Result visit(Dispatcher main, IASTFunctionDefinition node) {
//		LinkedHashSet<IASTDeclaration> reachableDecs = ((MainDispatcher) main).getReachableDeclarationsOrDeclarators();
//		if (reachableDecs != null) {
//			if (!reachableDecs.contains(node))
//				return new ResultSkip();
//		}

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
		ArrayList<Statement> stmt = new ArrayList<Statement>();
		IASTNode parent = node.getParent();

		if (isNewScopeRequired(parent)) {
			this.beginScope();
		}

		for (IASTNode child : node.getChildren()) {
			Result r = main.dispatch(child);
		}
		if (isNewScopeRequired(parent)) {
			this.endScope();
		}
		return new Result(new Body(loc, decl.toArray(new VariableDeclaration[0]), stmt.toArray(new Statement[0])));
	}

	private static boolean isNewScopeRequired(final IASTNode env) {
		return !(env instanceof IASTForStatement) && !(env instanceof IASTFunctionDefinition);
	}

	@Override
	public Result visit(Dispatcher main, IASTSimpleDeclaration node) {

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
					mFunctionHandler.handleFunctionDeclarator(main, LocationFactory.createCLocation(d), null, cDec);
					continue;
				}

				String bId = main.nameHandler.getUniqueIdentifier(node, cDec.getName(),
						mSymbolTable.getCompoundCounter(), false);

				Declaration boogieDec = null;
				boolean globalInBoogie = false;

				// this .put() is only to have a minimal symbolTableEntry
				// (containing boogieID) for
				// translation of the initializer
				mSymbolTable.put(cDec.getName(),
						new PRSymbolTableValue(bId, boogieDec, cDec, globalInBoogie, storageClass, d));
				cDec.translateInitializer(main);

				ASTType translatedType = null;

				translatedType = main.typeHandler.ctype2asttype(loc, cDec.getType());

				if (storageClass == StorageClass.TYPEDEF) {
					boogieDec = new TypeDeclaration(loc, new Attribute[0], false, bId, new String[0], translatedType);
					main.typeHandler.addDefinedType(bId, new ResultTypes(new NamedType(loc, cDec.getName(), null),
							false, false, cDec.getType()));
					// TODO: add a sizeof-constant for the type??
					globalInBoogie = true;
				} else if (storageClass == StorageClass.STATIC && !mFunctionHandler.noCurrentProcedure()) {
					// we have a local static variable -> special treatment
					// global static variables are treated like normal global variables..
					boogieDec = new VariableDeclaration(loc, new Attribute[0],
							new VarList[] { new VarList(loc, new String[] {bId}, 
									translatedType) });
					globalInBoogie = true;
				} else {
					/**
					 * For Variable length arrays we have a "non-real" initializer which just initializes the aux var for the array's
					 * size. We do not want to treat this like other initializers (call initVar and so).
					 */
					boolean hasRealInitializer = cDec.hasInitializer() && 
							!(cDec.getType() instanceof CArray && !(cDec.getInitializer() instanceof ResultExpressionListRec));

					if (!hasRealInitializer && !mFunctionHandler.noCurrentProcedure()
							&& !mTypeHandler.isStructDeclaration()) {


						VariableLHS lhs = new VariableLHS(loc, bId);

					} else if (hasRealInitializer && !mFunctionHandler.noCurrentProcedure() && !mTypeHandler.isStructDeclaration()) { 
						//in case of a local variable declaration with an initializer, the statements and delcs
						// necessary for the initialization are the result
					

					} else {
						assert result instanceof ResultSkip || result instanceof ResultDeclaration;
						if (result instanceof ResultSkip)
							result = new ResultDeclaration();
						((ResultDeclaration) result).addDeclaration(cDec);	
					
					}
					boogieDec = new VariableDeclaration(loc, new Attribute[0], new VarList[] { new VarList(loc,
							new String[] { bId }, translatedType) });
					globalInBoogie |= mFunctionHandler.noCurrentProcedure();
				}

				mSymbolTable.put(cDec.getName(), new PRSymbolTableValue(bId,
						boogieDec, cDec, globalInBoogie,
						storageClass, d)); 
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
	
	
	private Result handleEnumDeclaration(Dispatcher main, IASTSimpleDeclaration node) {
		Result r = main.dispatch(node.getDeclSpecifier());
		assert r instanceof ResultTypes;
		ResultTypes rt = (ResultTypes) r;
		assert rt.cType instanceof CEnum;
//		CEnum cEnum = (CEnum) rt.cType;
//		ILocation loc = LocationFactory.createCLocation(node);
//		ASTType at = new PrimitiveType(loc, SFO.INT);
//		String enumId = cEnum.getIdentifier();
//		Expression oldValue = null;
//		Expression[] enumDomain = new Expression[cEnum.getFieldCount()];
		
		ResultDeclaration result = new ResultDeclaration();
		
//		for (int i = 0; i < cEnum.getFieldCount(); i++) {
//			String fId = cEnum.getFieldIds()[i];
//			String bId = enumId + "~" + fId;
//			VarList vl = new VarList(loc, new String[] { bId }, at);
//			ConstDeclaration cd = new ConstDeclaration(loc, new Attribute[0], false, vl, null, false);
//			mDeclarationsGlobalInBoogie.put(cd, new CDeclaration(cEnum, fId));
//			Expression l = new IdentifierExpression(loc, bId);
//			Expression newValue = oldValue;
//			if (oldValue == null && cEnum.getFieldValue(fId) == null) {
//				newValue = new IntegerLiteral(loc, SFO.NR0);
//			} else if (cEnum.getFieldValue(fId) == null) {
//				newValue = createArithmeticExpression(IASTBinaryExpression.op_plus, oldValue, new IntegerLiteral(loc, SFO.NR1), loc);
//			} else {
//				newValue = cEnum.getFieldValue(fId);
//			}
//			oldValue = newValue;
//			enumDomain[i] = newValue;
//			mAxioms.add(new Axiom(loc, new Attribute[0], new BinaryExpression(loc, Operator.COMPEQ, l, newValue)));
//			mSymbolTable.put(fId, new SymbolTableValue(bId, cd, new CDeclaration(cEnum, fId), true,
//					scConstant2StorageClass(node.getDeclSpecifier().getStorageClass()))); // FIXME
//																							// ??
//		}
		return result;
	}
	
	private StorageClass scConstant2StorageClass(int storageClass) {
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

//				constEx = constEx.switchToRValueIfNecessary(main, // just to be
//																	// safe..
//						mMemoryHandler, mStructHandler, loc);
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

		CType lType = l.lrVal.cType;
		if (lType instanceof CNamed)
			lType = ((CNamed) lType).getUnderlyingType();
		CType rType = r.lrVal.cType;
		if (rType instanceof CNamed)
			rType = ((CNamed) rType).getUnderlyingType();

		switch (node.getOperator()) {
		case IASTBinaryExpression.op_assign: 
			ResultExpression rrToInt = ConvExpr.rexBoolToIntIfNecessary(loc, rr);
			return makeAssignment(main, loc, l.lrVal, (RValue) rrToInt.lrVal);
			default:
				return super.visit(main, node);
		}
	}

	
	@Override
	public Result visit(Dispatcher main, IASTUnaryExpression node) {
		ResultExpression o = (ResultExpression) main.dispatch(node.getOperand());
		ILocation loc = LocationFactory.createCLocation(node);
		Expression nr1 = new IntegerLiteral(loc, SFO.NR1);

		CType oType = o.lrVal.cType;
		if (oType instanceof CNamed)
			oType = ((CNamed) oType).getUnderlyingType();

		switch (node.getOperator()) {
		case IASTUnaryExpression.op_amper:
			//can't really addressof at this point, returning the value instead but wiht pointer type
			ResultExpression rop = o.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);
			return new ResultExpression(new RValue(rop.lrVal.getValue(), new CPointer(rop.lrVal.cType)));
			default:
				return super.visit(main, node);
		}
	}

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

		if (node instanceof IASTForStatement) {
			IASTForStatement forStmt = (IASTForStatement) node;
			IASTStatement cInitStmt = forStmt.getInitializerStatement();
			if (cInitStmt != null) {
				this.beginScope();
				main.dispatch(cInitStmt);
			}
			IASTExpression cItExpr = forStmt.getIterationExpression();
			if (cItExpr != null)
				main.dispatch(cItExpr);
			IASTExpression cCondExpr = forStmt.getConditionExpression();
			if (cCondExpr != null)
				condResult = (ResultExpression) main.dispatch(cCondExpr);

			bodyResult = main.dispatch(forStmt.getBody());
		}


		if (node instanceof IASTForStatement) {
			if (((IASTForStatement) node).getInitializerStatement() != null) {
				this.endScope();
			}
		}

		assert (mSymbolTable.getActiveScopeNum() == scopeDepth);
		return new ResultExpression(stmt, null, decl, emptyAuxVars, overappr);
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
		return null;
	}

	@Override
	public Result visit(Dispatcher main, IASTIfStatement node) {
		main.dispatch(node.getConditionExpression());
		main.dispatch(node.getThenClause());
		if (node.getElseClause() != null)
			main.dispatch(node.getElseClause());
		return new ResultExpression(new RValue(new IdentifierExpression(LocationFactory.createIgnoreCLocation(), SFO.NULL), 
				new CPointer(new CPrimitive(PRIMITIVE.VOID))));
	}

	@Override
	public Result visit(Dispatcher main, IASTWhileStatement node) {
		ResultExpression condResult = (ResultExpression) main.dispatch(node.getCondition());
		String loopLabel = main.nameHandler.getGloballyUniqueIdentifier(SFO.LOOPLABEL);
//		mInnerMostLoopLabel.push(loopLabel);
		Result bodyResult = main.dispatch(node.getBody());
//		mInnerMostLoopLabel.pop();
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
//		mInnerMostLoopLabel.push(loopLabel);
		Result bodyResult = main.dispatch(node.getBody());
//		mInnerMostLoopLabel.pop();
		return handleLoops(main, node, bodyResult, condResult, loopLabel);
	}

	@Override
	public Result visit(Dispatcher main, IASTContinueStatement cs) {
		// TODO Auto-generated method stub
		return null;
	}



	@Override
	public Result visit(Dispatcher main, IASTSwitchStatement node) {
		main.dispatch(node.getControllerExpression());
		this.beginScope();
		for (IASTNode child : node.getBody().getChildren()) {
			Result r = main.dispatch(child);
		}
		this.endScope();
		return null;
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
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Result visit(Dispatcher main, IASTGotoStatement node) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Result visit(Dispatcher main, IASTCastExpression node) {
		ResultExpression expr = (ResultExpression) main.dispatch(node.getOperand()); 
		ILocation loc = LocationFactory.createCLocation(node); 
		expr = expr.switchToRValueIfNecessary(main, mMemoryHandler, mStructHandler, loc);

		// TODO: check validity of cast?

		ResultTypes resTypes = (ResultTypes) main.dispatch(node.getTypeId().getDeclSpecifier());

		mCurrentDeclaredTypes.push(resTypes);
		ResultDeclaration declResult = (ResultDeclaration) main.dispatch(node.getTypeId().getAbstractDeclarator());
		assert declResult.getDeclarations().size() == 1;
		CType newCType = declResult.getDeclarations().get(0).getType();
		mCurrentDeclaredTypes.pop();
		
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
	public Result visit(Dispatcher main, IASTInitializerList node) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Result visit(Dispatcher main, IASTArraySubscriptExpression node) {
		return mArrayHandler.handleArraySubscriptExpression(main, mMemoryHandler, mStructHandler, node);
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
		// TODO Auto-generated method stub
		return null;
	}
//	public ResultExpression makeAssignment(Dispatcher main, ILocation loc, ArrayList<Statement> stmt, LRValue lrVal,
//			RValue rVal, ArrayList<Declaration> decl, Map<VariableDeclaration, ILocation> auxVars,
//			List<Overapprox> overappr) {
//		return makeAssignment(main, loc, stmt, lrVal, rVal, decl, auxVars, overappr, null);
//	}

	public ResultExpression makeAssignment(Dispatcher main, ILocation loc,  LRValue lrVal,
			RValue rVal) {
		RValue rightHandSide = rVal; //we may change the content of the right hand side later

		//do implicit cast -- assume the types are compatible
		rightHandSide = castToType(loc, rightHandSide, lrVal.cType);
		
		if (lrVal.cType.getUnderlyingType() instanceof CPointer
				&& rVal.cType.getUnderlyingType() instanceof CArray) {
//			variablesOnHeap.add(node);
			if (rVal.getValue() instanceof IdentifierExpression) {
				String id = ((IdentifierExpression) rVal.getValue()).getIdentifier();
				variablesOnHeap.add(((PRSymbolTableValue) mSymbolTable.get(mSymbolTable.getCID4BoogieID(id, loc), loc)).decl);
			}
		}

		if (lrVal instanceof HeapLValue) {
			HeapLValue hlv = (HeapLValue) lrVal;
//			stmt.addAll(mMemoryHandler.getWriteCall(loc, hlv, rightHandSide));
//			return new ResultExpression(rightHandSide);
			return new ResultExpression(hlv);
		} else if (lrVal instanceof LocalLValue) {
			LocalLValue lValue = (LocalLValue) lrVal;
//			AssignmentStatement assignStmt = new AssignmentStatement(loc, new LeftHandSide[] { lValue.getLHS() },
//					new Expression[] { rightHandSide.getValue() });
//			Map<String, IAnnotations> annots = assignStmt.getPayload().getAnnotations();
//			for (Overapprox overapprItem : overappr) {
//				annots.put(Overapprox.getIdentifier(), overapprItem);
//			}
//			stmt.add(assignStmt);
//
//			// add havocs if we have a write to a union (which is not on heap,
//			// otherwise the heap model should deal with everything)
//			if (unionFieldsToCType != null) {
//				for (Entry<StructLHS, CType> en : unionFieldsToCType.entrySet()) {
//					//do not havoc when the type of the field is "compatible"
//					if (rightHandSide.cType.equals(en.getValue())
//							|| (rightHandSide.cType instanceof CPrimitive && en.getValue() instanceof CPrimitive
//							 && ((CPrimitive) rightHandSide.cType.getUnderlyingType()).getGeneralType().equals(((CPrimitive) en.getValue()).getGeneralType())
//							 && (mMemoryHandler.calculateSizeOfWithGivenTypeSizes(loc, rightHandSide.cType) 
//									 == mMemoryHandler.calculateSizeOfWithGivenTypeSizes(loc, en.getValue())))) {
//						stmt.add(new AssignmentStatement(loc, new LeftHandSide[] { en.getKey() },
//								new Expression[] { rightHandSide.getValue() }));
//					} else { //otherwise we consider the value undefined, thus havoc it
//						// TODO: maybe not use auxiliary variables so lavishly
//						String tmpId = main.nameHandler.getTempVarUID(SFO.AUXVAR.UNION);
//						VariableDeclaration tVarDec = new VariableDeclaration(loc, new Attribute[0], new VarList[] { new VarList(loc,
//								new String[] { tmpId }, main.typeHandler.ctype2asttype(loc, en.getValue())) });
//						decl.add(tVarDec);
//						auxVars.put(tVarDec, loc); //ensures that the variable will be havoced (necessary only when we are inside a loop)
//
//						stmt.add(new AssignmentStatement(loc, new LeftHandSide[] { en.getKey() },
//								new Expression[] { new IdentifierExpression(loc, tmpId) }));
//					}
//				}
//			}
//
//			if (!mFunctionHandler.noCurrentProcedure())
//				mFunctionHandler.checkIfModifiedGlobal(main, BoogieASTUtil.getLHSId(lValue.getLHS()), loc);
			return new ResultExpression(lValue);
		} else
			throw new AssertionError("Type error: trying to assign to an RValue in Statement" + loc.toString());
	}
	
	
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
	
	public void beginScope() {
//		this.sT.beginScope();
		this.mTypeHandler.beginScope();
		this.mSymbolTable.beginScope();
	}

	public void endScope() {
//		this.sT.endScope();
		this.mTypeHandler.endScope();
		this.mSymbolTable.endScope();
	}

	@Override
	public boolean isHeapVar(String boogieId) {
		// TODO Auto-generated method stub
		return false;
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
	public RValue castToType(ILocation loc, RValue rValIn, CType expectedTypeRaw) {
		CType expectedType = expectedTypeRaw.getUnderlyingType();
		
		RValue rVal = new RValue(rValIn); //better make a new one, right??

//		BigInteger maxPtrValue = new BigInteger("2").pow(mMemoryHandler.typeSizeConstants.sizeOfPointerType * 8);
//		IntegerLiteral max_Pointer = new IntegerLiteral(loc, maxPtrValue.toString());
		// cast pointer -> integer/other pointer
//		CType rValUlType = rVal.cType.getUnderlyingType();
//		if (rValUlType instanceof CPointer) {
//			// cast from pointer to integer
//			if (expectedType instanceof CPrimitive &&
//					((CPrimitive) expectedType).getGeneralType() == GENERALPRIMITIVE.INTTYPE) {
//				Expression e = null;
//				if (mMemoryHandler.useConstantTypeSizes) {
//					e = createArithmeticExpression(IASTBinaryExpression.op_plus,
//							createArithmeticExpression(IASTBinaryExpression.op_multiply, 
//									MemoryHandler.getPointerBaseAddress(rVal.getValue(),  loc), 
//									max_Pointer, 
//									loc),
//							MemoryHandler.getPointerOffset(rVal.getValue(), loc), 
//							loc);
//				} else {
//					e = MemoryHandler.getPointerOffset(rVal.getValue(), loc);
//				}
//				rVal = new RValue(e, expectedType);
//				rVal.isIntFromPointer = true;
//			}
//			// type is changed
////			else if (!(expectedType.getUnderlyingType() instanceof CPointer)) { //why did I make this distinction??
//			else {
//				rVal.cType = expectedType;
//			}
//		} else if (rValUlType instanceof CPrimitive) {
//			CPrimitive cprim = (CPrimitive) rValUlType;
//			if (cprim.getGeneralType() == GENERALPRIMITIVE.INTTYPE) {
//				if (expectedType instanceof CPointer) {// cast integer -> pointer
//					Expression e = null;
//					if (mMemoryHandler.useConstantTypeSizes) {
//						e = MemoryHandler.constructPointerFromBaseAndOffset(
//								createArithmeticExpression(IASTBinaryExpression.op_divide,
//										rVal.getValue(),
//										max_Pointer, 
//										loc),
//										createArithmeticExpression(IASTBinaryExpression.op_modulo,
//												rVal.getValue(),
//												max_Pointer, 
//												loc),
//												loc);
//					} else {
//						e = MemoryHandler.constructPointerFromBaseAndOffset(new IntegerLiteral(loc, "0"),
//								rVal.getValue(), loc);
//					}
//					rVal = new RValue(e, expectedType);
//				}
//			} else if (cprim.getGeneralType() == GENERALPRIMITIVE.FLOATTYPE) { 
//				if (expectedType instanceof CPrimitive) {
//					if (((CPrimitive) expectedType).getGeneralType() == GENERALPRIMITIVE.INTTYPE) {
//						rVal = new RValue(new FunctionApplication(loc, SFO.TO_INT, new Expression[] { rVal.getValue() }), 
//								expectedType);
//					}
//				}
//		
//			}
//		}
		rVal.cType = expectedType;
		return rVal;
	}

	@Override
	public InitializationHandler getInitHandler() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public UNSIGNED_TREATMENT getUnsignedTreatment() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public FunctionHandler getFunctionHandler() {
		// TODO Auto-generated method stub
		return null;
	}

}
