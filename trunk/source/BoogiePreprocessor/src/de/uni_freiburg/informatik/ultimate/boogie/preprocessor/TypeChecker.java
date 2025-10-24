/*
 * Copyright (C) 2008-2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2008-2016 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * Copyright (C) 2018 Lars Nitkze (lars.nitzke@mailfence.com)
 * Copyright (C) 2015-2016 University of Freiburg
 *
 * This file is part of the ULTIMATE BoogiePreprocessor plug-in.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogiePreprocessor plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogiePreprocessor plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BoogiePreprocessor plug-in grant you additional permission
 * to convey the resulting work.
 */
/**
 *
 */
package de.uni_freiburg.informatik.ultimate.boogie.preprocessor;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.Stack;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.annotation.LTLPropertyCheck;
import de.uni_freiburg.informatik.ultimate.boogie.annotation.LTLPropertyCheck.CheckableExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AtomicStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitVectorAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BreakStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ForkStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.JoinStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ParentEdge;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RequiresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Trigger;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WildcardExpression;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieFunctionSignature;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieStructType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.typechecker.FunctionInfo;
import de.uni_freiburg.informatik.ultimate.boogie.typechecker.ITypeErrorReporter;
import de.uni_freiburg.informatik.ultimate.boogie.typechecker.ProcedureInfo;
import de.uni_freiburg.informatik.ultimate.boogie.typechecker.TypeCheckHelper;
import de.uni_freiburg.informatik.ultimate.boogie.typechecker.TypeManager;
import de.uni_freiburg.informatik.ultimate.boogie.typechecker.TypeParameters;
import de.uni_freiburg.informatik.ultimate.boogie.typechecker.VariableInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TypeErrorResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;

/**
 * This class is a AST-Visitor for creating textual representations of the tree. It creates a String.
 *
 * @author Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 */
public class TypeChecker extends BaseObserver {
	private TypeManager mTypeManager;
	private HashMap<String, FunctionInfo> mDeclaredFunctions;
	private HashMap<String, ProcedureInfo> mDeclaredProcedures;
	private HashMap<String, VariableInfo> mDeclaredVars;
	private ScopedHashMap<String, VariableInfo> mVarScopes;

	/**
	 * Maps a procedure identifier to all variables that occur in a modifies clause of this procedure.
	 */
	private final Map<String, Set<String>> mProc2ModfiedGlobals = new HashMap<>();

	/**
	 * Identifier of procedure that is checked at the moment.
	 */
	private String mCurrentProcedure;

	/**
	 * Identifiers of global variables
	 */
	private final Set<String> mGlobals = new HashSet<>();

	/**
	 * Identifiers of the in-parameters of the checked procedure
	 */
	private Set<String> mInParams;

	/**
	 * Identifiers of the out-parameters of the checked procedure
	 */
	private Set<String> mOutParams;

	/**
	 * Identifiers of the local variables of the checked procedure
	 */
	private Set<String> mLocalVars;
	private final IUltimateServiceProvider mServices;

	private final Map<Expression, BoogieType> mCache;
	private final ILogger mLogger;

	public TypeChecker(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mCache = new HashMap<>();
	}

	private VariableInfo findVariable(final String name) {
		final VariableInfo rtr = mVarScopes.get(name);
		if (rtr == null) {
			return mDeclaredVars.get(name);
		}
		return rtr;
	}

	private BoogieType typecheckExpression(final Expression expr) {
		final TypeErrorReporter typeErrorReporter = new TypeErrorReporter(expr);
		BoogieType resultType = mCache.get(expr);
		if (resultType == null) {
			resultType = typecheckExpressionInternal(expr, typeErrorReporter);
			expr.setType(resultType);
			mCache.put(expr, resultType);
		}
		assert expr.getType().equals(resultType);
		return resultType;
	}

	private BoogieType typecheckExpressionInternal(final Expression expr, final TypeErrorReporter typeErrorReporter) {
		return switch (expr) {
		case final BinaryExpression binexp ->
				TypeCheckHelper.typeCheckBinaryExpression(binexp.getOperator(), typecheckExpression(binexp.getLeft()),
						typecheckExpression(binexp.getRight()), new TypeErrorReporter(binexp));
		case final UnaryExpression unexp -> TypeCheckHelper.typeCheckUnaryExpression(unexp.getOperator(),
				typecheckExpression(unexp.getExpr()), new TypeErrorReporter(expr));
		case final BitVectorAccessExpression bvaexpr -> {
			final BoogieType bvType = typecheckExpression(bvaexpr.getBitvec());
			yield TypeCheckHelper.typeCheckBitVectorAccessExpression(TypeCheckHelper.getBitVecLength(bvType),
					bvaexpr.getEnd(), bvaexpr.getStart(), bvType, new TypeErrorReporter(expr));
		}
		case final StructAccessExpression sae -> TypeCheckHelper.typeCheckStructAccessExpressionOrLhs(
				typecheckExpression(sae.getStruct()).getUnderlyingType(), sae.getField(), typeErrorReporter);
		case final ArrayAccessExpression aaexpr -> {
			final BoogieType arrayType = typecheckExpression(aaexpr.getArray()).getUnderlyingType();
			final List<BoogieType> indicesTypes =
					Arrays.stream(aaexpr.getIndices()).map(this::typecheckExpression).toList();
			yield TypeCheckHelper.typeCheckArrayAccessExpressionOrLhs(arrayType, indicesTypes, typeErrorReporter);
		}
		case final ArrayStoreExpression asexpr -> {
			final BoogieType arrayType = typecheckExpression(asexpr.getArray()).getUnderlyingType();
			final List<BoogieType> indicesTypes =
					Arrays.stream(asexpr.getIndices()).map(this::typecheckExpression).toList();
			final BoogieType valueType = typecheckExpression(asexpr.getValue());
			yield TypeCheckHelper.typeCheckArrayStoreExpression(arrayType, indicesTypes, valueType, typeErrorReporter);
		}
		case final BooleanLiteral bLit -> BoogieType.TYPE_BOOL;
		case final IntegerLiteral iLit -> BoogieType.TYPE_INT;
		case final RealLiteral rLit -> BoogieType.TYPE_REAL;
		case final BitvecLiteral bvlit -> BoogieType.createBitvectorType(bvlit.getLength());
		case final StructConstructor struct -> {
			final BoogieType[] fieldTypes =
					Arrays.stream(struct.getFieldValues()).map(this::typecheckExpression).toArray(BoogieType[]::new);
			final boolean hasError = Arrays.asList(fieldTypes).contains(BoogieType.TYPE_ERROR);
			yield hasError ? BoogieType.TYPE_ERROR
					: BoogieType.createStructType(struct.getFieldIdentifiers(), fieldTypes);
		}
		case final IdentifierExpression idexpr -> typecheckIdentifierExpression(idexpr);
		case final FunctionApplication app -> typecheckFunctionApplication(app);
		case final IfThenElseExpression ite -> {
			final BoogieType condType = typecheckExpression(ite.getCondition());
			final BoogieType left = typecheckExpression(ite.getThenPart());
			final BoogieType right = typecheckExpression(ite.getElsePart());
			yield TypeCheckHelper.typeCheckIfThenElseExpression(condType, left, right, typeErrorReporter);
		}
		case final QuantifierExpression quant -> typecheckQuantifierExpression(quant);
		case final WildcardExpression we -> BoogieType.TYPE_BOOL;
		case final StringLiteral strlit ->
				throw new IllegalStateException("String literals must only occur in attributes");
		};
	}

	private BoogieType typecheckIdentifierExpression(final IdentifierExpression idexpr) {
		final String name = idexpr.getIdentifier();
		final VariableInfo info = findVariable(name);
		if (info == null) {
			typeError(idexpr, "Undeclared identifier " + name + " in " + idexpr);
			return BoogieType.TYPE_ERROR;
		}
		final DeclarationInformation declInfo = idexpr.getDeclarationInformation();
		if (declInfo == null) {
			idexpr.setDeclarationInformation(info.getDeclarationInformation());
		} else {
			checkExistingDeclarationInformation(name, declInfo, info.getDeclarationInformation());
		}
		return info.getType().getUnderlyingType();
	}

	private BoogieType typecheckFunctionApplication(final FunctionApplication app) {
		final String name = app.getIdentifier();
		final FunctionInfo fi = mDeclaredFunctions.get(name);
		if (fi == null) {
			typeError(app, "Undeclared function " + name + " in " + app);
			return BoogieType.TYPE_ERROR;
		}
		final BoogieFunctionSignature fs = fi.getSignature();
		final BoogieType[] subst = new BoogieType[fs.getTypeArgCount()];
		final Expression[] appArgs = app.getArguments();
		if (appArgs.length != fs.getParamCount()) {
			typeError(app, "Type check failed (wrong number of arguments): " + app);
			return BoogieType.TYPE_ERROR;
		}
		for (int i = 0; i < appArgs.length; i++) {
			final BoogieType t = typecheckExpression(appArgs[i]);
			if (!t.equals(BoogieType.TYPE_ERROR) && !fs.getParamType(i).unify(t, subst)) {
				typeError(app, "Type check failed (index " + i + "): " + app);
				return BoogieType.TYPE_ERROR;
			}
		}
		return fs.getResultType().substitutePlaceholders(subst);
	}

	private BoogieType typecheckQuantifierExpression(final QuantifierExpression quant) {
		final TypeParameters typeParams = new TypeParameters(quant.getTypeParams());
		mTypeManager.pushTypeScope(typeParams);

		final DeclarationInformation declInfo = new DeclarationInformation(StorageClass.QUANTIFIED, null);
		final VarList[] parameters = quant.getParameters();

		mVarScopes.beginScope();
		for (final VarList p : parameters) {
			final BoogieType type = mTypeManager.resolveType(p.getType());
			for (final String id : p.getIdentifiers()) {
				mVarScopes.put(id, new VariableInfo(true, null, id, type, declInfo));
			}
		}
		if (!typeParams.fullyUsed()) {
			typeError(quant, "Type args not fully used in variable types: " + quant);
			return BoogieType.TYPE_ERROR;
		}

		typecheckAttributes(quant.getAttributes());
		final BoogieType t = typecheckExpression(quant.getSubformula());
		if (!t.equals(BoogieType.TYPE_ERROR) && !t.equals(BoogieType.TYPE_BOOL)) {
			typeError(quant, "Type check error in: " + quant);
			return BoogieType.TYPE_ERROR;
		}
		mVarScopes.endScope();
		mTypeManager.popTypeScope();
		return BoogieType.TYPE_BOOL;
	}

	/**
	 * Compare existingDeclInfo with correctDeclInfo and raise an internalError if both are not equivalent.
	 */
	private static void checkExistingDeclarationInformation(final String id,
			final DeclarationInformation existingDeclInfo, final DeclarationInformation correctDeclInfo) {
		if (!existingDeclInfo.equals(correctDeclInfo)) {
			TypeCheckHelper.internalError("Incorrect DeclarationInformation of \"" + id + "\". Expected: "
					+ correctDeclInfo + "   Found: " + existingDeclInfo);
		}
	}

	private BoogieType typecheckLeftHandSide(final LeftHandSide lhs) {

		final TypeErrorReporter typeErrorReporter = new TypeErrorReporter(lhs);

		BoogieType resultType;
		if (lhs instanceof final VariableLHS vLhs) {
			final String name = vLhs.getIdentifier();
			resultType = checkVarModification(lhs, name);
			final VariableInfo info = findVariable(name);
			if (info != null) {
				final DeclarationInformation declInfo = vLhs.getDeclarationInformation();
				if (declInfo == null) {
					vLhs.setDeclarationInformation(info.getDeclarationInformation());
				} else {
					checkExistingDeclarationInformation(name, declInfo, info.getDeclarationInformation());
				}
			}
		} else if (lhs instanceof final StructLHS slhs) {
			final BoogieType type = typecheckLeftHandSide(slhs.getStruct()).getUnderlyingType();
			if (!(type instanceof final BoogieStructType str)) {
				if (!type.equals(BoogieType.TYPE_ERROR)) {
					typeError(lhs, "Type check failed (not a struct): " + lhs);
				}
				resultType = BoogieType.TYPE_ERROR;
			} else {
				resultType = null;
				for (int i = 0; i < str.getFieldCount(); i++) {
					if (str.getFieldIds()[i].equals(slhs.getField())) {
						resultType = str.getFieldType(i);
					}
				}
				if (resultType == null) {
					typeError(lhs, "Type check failed (field " + slhs.getField() + " not in struct): " + lhs);
					resultType = BoogieType.TYPE_ERROR;
				}
			}
		} else if (lhs instanceof final ArrayLHS alhs) {
			// SFA: Patched to look inside ConstructedType
			final BoogieType arrayType = typecheckLeftHandSide(alhs.getArray()).getUnderlyingType();
			final List<BoogieType> indicesTypes = new ArrayList<>();
			for (int i = 0; i < alhs.getIndices().length; i++) {
				indicesTypes.add(typecheckExpression(alhs.getIndices()[i]));
			}
			resultType =
					TypeCheckHelper.typeCheckArrayAccessExpressionOrLhs(arrayType, indicesTypes, typeErrorReporter);
		} else {
			TypeCheckHelper.internalError("Unknown LHS: " + lhs);
			resultType = BoogieType.TYPE_ERROR;
		}
		lhs.setType(resultType);
		return resultType;
	}

	private void typecheckAttributes(final Attribute[] attributes) {
		if (attributes == null) {
			return;
		}
		for (final Attribute attr : attributes) {
			final Expression[] exprs = switch (attr) {
			case final Trigger trigger -> trigger.getTriggers();
			case final NamedAttribute named -> named.getValues();
			};
			for (final Expression e : exprs) {
				if (!(e instanceof StringLiteral)) {
					typecheckExpression(e);
				}
			}
		}
	}

	private void processVariableDeclaration(final VariableDeclaration varDecl) {
		final DeclarationInformation declInfo = new DeclarationInformation(StorageClass.GLOBAL, null);
		for (final VarList varlist : varDecl.getVariables()) {
			final BoogieType type = mTypeManager.resolveType(varlist.getType());
			for (final String id : varlist.getIdentifiers()) {
				mDeclaredVars.put(id, new VariableInfo(false, varDecl, id, type, declInfo));
				mGlobals.add(id);
			}
		}
	}

	private void processConstDeclaration(final ConstDeclaration constDecl) {
		final DeclarationInformation declInfo = new DeclarationInformation(StorageClass.GLOBAL, null);
		final VarList varList = constDecl.getVarList();
		final BoogieType type = mTypeManager.resolveType(varList.getType());
		for (final String id : varList.getIdentifiers()) {
			mDeclaredVars.put(id, new VariableInfo(true, constDecl, id, type, declInfo));
		}
	}

	private void checkConstDeclaration(final ConstDeclaration constDecl) {
		final ParentEdge[] parents = constDecl.getParentInfo();
		if (parents == null) {
			return;
		}
		final BoogieType type = (BoogieType) constDecl.getVarList().getType().getBoogieType();
		for (final ParentEdge p : parents) {
			final VariableInfo var = mDeclaredVars.get(p.getIdentifier());
			if (var == null || !var.isRigid()) {
				typeError(constDecl, constDecl + ": parent is not a const");
			} else if (!type.equals(var.getType()) && !var.getType().equals(BoogieType.TYPE_ERROR)
					&& !type.equals(BoogieType.TYPE_ERROR)) {
				typeError(constDecl, constDecl + ": parent is not of same type");
			}
		}
	}

	private void processFunctionDeclaration(final FunctionDeclaration funcDecl) {
		final String name = funcDecl.getIdentifier();

		final TypeParameters typeParams = new TypeParameters(funcDecl.getTypeParams());
		mTypeManager.pushTypeScope(typeParams);

		final VarList[] paramNodes = funcDecl.getInParams();
		final String[] paramNames = new String[paramNodes.length];
		final BoogieType[] paramTypes = new BoogieType[paramNodes.length];
		for (int i = 0; i < paramNodes.length; i++) {
			final String[] names = paramNodes[i].getIdentifiers();
			if (names.length > 0) {
				paramNames[i] = names[0];
			}
			paramTypes[i] = mTypeManager.resolveType(paramNodes[i].getType());
		}
		if (!typeParams.fullyUsed()) {
			typeError(funcDecl, "Type args not fully used in function parameter: " + funcDecl);
		}

		String valueName = null;
		final String[] valueNames = funcDecl.getOutParam().getIdentifiers();
		final BoogieType valueType = mTypeManager.resolveType(funcDecl.getOutParam().getType());
		if (valueNames.length > 0) {
			valueName = valueNames[0];
		}

		mTypeManager.popTypeScope();

		final BoogieFunctionSignature fs = new BoogieFunctionSignature(funcDecl.getTypeParams().length, paramNames,
				paramTypes, valueName, valueType);
		mDeclaredFunctions.put(name, new FunctionInfo(funcDecl, name, typeParams, fs));
	}

	private void processFunctionDefinition(final FunctionDeclaration funcDecl) {
		/* type check the body of a function */
		if (funcDecl.getBody() == null) {
			return;
		}

		/* Declare local variables for parameters */
		final String name = funcDecl.getIdentifier();
		final FunctionInfo fi = mDeclaredFunctions.get(name);
		final TypeParameters typeParams = fi.getTypeParameters();

		final DeclarationInformation declInfo = new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, name);
		mTypeManager.pushTypeScope(typeParams);
		final BoogieFunctionSignature fs = fi.getSignature();
		mVarScopes.beginScope();
		final int paramCount = fs.getParamCount();
		for (int i = 0; i < paramCount; i++) {
			final String paramName = fs.getParamName(i);
			if (paramName != null) {
				mVarScopes.put(paramName,
						new VariableInfo(true, null, fs.getParamName(i), fs.getParamType(i), declInfo));
			}
		}
		final BoogieType valueType = typecheckExpression(funcDecl.getBody());
		if (!valueType.equals(BoogieType.TYPE_ERROR) && !valueType.equals(fs.getResultType())) {
			typeError(funcDecl, "Return type of function doesn't match body");
		}
		mVarScopes.endScope();
		mTypeManager.popTypeScope();
	}

	/**
	 * TODO : some meaningful description ...
	 *
	 * @param proc
	 *            the procedure to process.
	 */
	public void processProcedureDeclaration(final Procedure proc) {
		if (proc.getSpecification() == null) {
			/* This is only an implementation. It is checked later. */
			return;
		}

		final String name = proc.getIdentifier();
		final TypeParameters typeParams = new TypeParameters(proc.getTypeParams());
		mTypeManager.pushTypeScope(typeParams);

		final DeclarationInformation declInfoInParam =
				new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, proc.getIdentifier());
		final LinkedList<VariableInfo> inParams = new LinkedList<>();
		for (final VarList vl : proc.getInParams()) {
			final BoogieType type = mTypeManager.resolveType(vl.getType());
			for (final String id : vl.getIdentifiers()) {
				inParams.add(new VariableInfo(true /* in params are rigid */, proc, id, type, declInfoInParam));
			}
		}
		if (!typeParams.fullyUsed()) {
			typeError(proc, "Type args not fully used in procedure parameter: " + proc);
		}
		final DeclarationInformation declInfoOutParam =
				new DeclarationInformation(StorageClass.PROC_FUNC_OUTPARAM, proc.getIdentifier());
		final LinkedList<VariableInfo> outParams = new LinkedList<>();
		for (final VarList vl : proc.getOutParams()) {
			final BoogieType type = mTypeManager.resolveType(vl.getType());
			for (final String id : vl.getIdentifiers()) {
				outParams.add(new VariableInfo(false, proc, id, type, declInfoOutParam));
			}
		}

		mVarScopes.beginScope();
		for (final VariableInfo vi : inParams) {
			mVarScopes.put(vi.getName(), vi);
		}
		for (final VariableInfo vi : outParams) {
			mVarScopes.put(vi.getName(), vi);
		}
		for (final VarList vl : proc.getInParams()) {
			if (vl.getWhereClause() != null) {
				final BoogieType t = typecheckExpression(vl.getWhereClause());
				if (!t.equals(BoogieType.TYPE_BOOL) && !t.equals(BoogieType.TYPE_ERROR)) {
					typeError(vl.getWhereClause(), "Where clause is not boolean: " + vl.getWhereClause());
				}
			}
		}
		for (final VarList vl : proc.getOutParams()) {
			if (vl.getWhereClause() != null) {
				final BoogieType t = typecheckExpression(vl.getWhereClause());
				if (!t.equals(BoogieType.TYPE_BOOL) && !t.equals(BoogieType.TYPE_ERROR)) {
					typeError(vl.getWhereClause(), "Where clause is not boolean: " + vl.getWhereClause());
				}
			}
		}
		mProc2ModfiedGlobals.put(name, new HashSet<>());
		for (final Specification s : proc.getSpecification()) {
			if (s instanceof final RequiresSpecification requires) {
				final BoogieType t = typecheckExpression(requires.getFormula());
				if (!t.equals(BoogieType.TYPE_BOOL) && !t.equals(BoogieType.TYPE_ERROR)) {
					typeError(s, "Requires clause is not boolean: " + s);
				}
			} else if (s instanceof final EnsuresSpecification ensures) {
				final BoogieType t = typecheckExpression(ensures.getFormula());
				if (!t.equals(BoogieType.TYPE_BOOL) && !t.equals(BoogieType.TYPE_ERROR)) {
					typeError(s, "Ensures clause is not boolean: " + s);
				}
			} else if (s instanceof final ModifiesSpecification modifies) {
				final Set<String> modifiedGlobals = mProc2ModfiedGlobals.get(name);
				for (final VariableLHS var : modifies.getIdentifiers()) {
					final DeclarationInformation declInfo = new DeclarationInformation(StorageClass.GLOBAL, null);
					if (var.getDeclarationInformation() == null) {
						var.setDeclarationInformation(declInfo);
					} else {
						checkExistingDeclarationInformation(var.getIdentifier(), var.getDeclarationInformation(),
								declInfo);
					}
					final String id = var.getIdentifier();
					if (mGlobals.contains(id)) {
						modifiedGlobals.add(id);
						var.setType(findVariable(id).getType());
					} else {
						typeError(s, "Modifies clause contains " + id + " which is not a global variable");
					}
				}
			} else {
				TypeCheckHelper.internalError("Unknown Procedure specification: " + s);
			}
		}
		mVarScopes.endScope();
		mTypeManager.popTypeScope();

		final ProcedureInfo pi =
				new ProcedureInfo(proc, typeParams, inParams.toArray(new VariableInfo[inParams.size()]),
						outParams.toArray(new VariableInfo[outParams.size()]));
		mDeclaredProcedures.put(name, pi);
	}

	/**
	 * Collect all labels in the given block and store them in the hash set labels.
	 *
	 * @param labels
	 *            The hash set where the labels are stored.
	 * @param block
	 *            The code block.
	 */
	private void processLabels(final HashSet<String> labels, final Statement[] block) {
		for (final Statement s : block) {
			if (s instanceof final Label label) {
				labels.add(label.getName());
			} else if (s instanceof final IfStatement ifStmt) {
				processLabels(labels, ifStmt.getThenPart());
				processLabels(labels, ifStmt.getElsePart());
			} else if (s instanceof final WhileStatement whileStmt) {
				processLabels(labels, whileStmt.getBody());
			} else if (s instanceof final AtomicStatement atomicStmt) {
				processLabels(labels, atomicStmt.getBody());
			}
		}
	}

	/**
	 * Type check the given statement.
	 *
	 * @param outer
	 *            the labels right before some outer block.
	 * @param allLabels
	 *            all labels appearing in the implementation body.
	 * @param statement
	 *            the code to type check.
	 */
	private void typecheckStatement(final Stack<String> outer, final HashSet<String> allLabels,
			final Statement statement) {

		final TypeErrorReporter typeErrorReporter = new TypeErrorReporter(statement);

		switch (statement) {
		case final AssumeStatement assumeStmt -> {
			final BoogieType t = typecheckExpression(assumeStmt.getFormula());
			if (!t.equals(BoogieType.TYPE_BOOL) && !t.equals(BoogieType.TYPE_ERROR)) {
				typeError(statement, "Assume is not boolean: " + statement);
			}
			typecheckAttributes(assumeStmt.getAttributes());
		}
		case final AssertStatement assertStmt -> {
			final BoogieType t = typecheckExpression(assertStmt.getFormula());
			if (!t.equals(BoogieType.TYPE_BOOL) && !t.equals(BoogieType.TYPE_ERROR)) {
				typeError(statement, "Assert is not boolean: " + statement);
			}
			typecheckAttributes(assertStmt.getAttributes());
		}
		case final BreakStatement breakStmt -> {
			final String label = breakStmt.getLabel();
			if (!outer.contains(label == null ? "*" : label)) {
				typeError(statement, "Break label not found: " + statement);
			}
		}
		case final HavocStatement havocStmt -> {
			for (final VariableLHS id : havocStmt.getIdentifiers()) {
				typecheckLeftHandSide(id);
			}
		}
		case final AssignmentStatement assignStmt -> {
			final LeftHandSide[] lhs = assignStmt.getLhs();
			final Expression[] rhs = assignStmt.getRhs();

			final String[] lhsIds = new String[lhs.length];
			final BoogieType[] lhsTypes = new BoogieType[lhs.length];
			final BoogieType[] rhsTypes = new BoogieType[rhs.length];
			for (int i = 0; i < lhs.length; i++) {
				lhsIds[i] = TypeCheckHelper.getLeftHandSideIdentifier(lhs[i]);
				lhsTypes[i] = typecheckLeftHandSide(lhs[i]);
				rhsTypes[i] = typecheckExpression(rhs[i]);
			}

			TypeCheckHelper.typeCheckAssignStatement(lhsIds, lhsTypes, rhsTypes, typeErrorReporter);
		}
		case final GotoStatement gotoStmt -> {
			for (final String label : gotoStmt.getLabels()) {
				if (!allLabels.contains(label)) {
					typeError(statement, "Goto label not found: " + statement);
				}
			}
		}
		case final Label label -> {
			/* Nothing to check */
		}
		case final ReturnStatement returnStmt -> {
			/* Nothing to check */
		}
		case final IfStatement ifStmt -> {
			final BoogieType t = typecheckExpression(ifStmt.getCondition());
			if (!t.equals(BoogieType.TYPE_BOOL) && !t.equals(BoogieType.TYPE_ERROR)) {
				typeError(statement, "Condition is not boolean: " + statement);
			}
			typecheckBlock(outer, allLabels, ifStmt.getThenPart());
			typecheckBlock(outer, allLabels, ifStmt.getElsePart());
		}
		case final WhileStatement whileStmt -> {
			final BoogieType t = typecheckExpression(whileStmt.getCondition());
			if (!t.equals(BoogieType.TYPE_BOOL) && !t.equals(BoogieType.TYPE_ERROR)) {
				typeError(statement, "Condition is not boolean: " + statement);
			}
			for (final Specification inv : whileStmt.getInvariants()) {
				if (inv instanceof LoopInvariantSpecification) {
					final BoogieType t2 = typecheckExpression(((LoopInvariantSpecification) inv).getFormula());
					if (!t2.equals(BoogieType.TYPE_BOOL) && !t2.equals(BoogieType.TYPE_ERROR)) {
						typeError(statement, "Loop invariant is not boolean: " + statement);
					}
				} else {
					TypeCheckHelper.internalError("Unknown while specification: " + inv);
				}
			}
			outer.push("*");
			typecheckBlock(outer, allLabels, whileStmt.getBody());
			outer.pop();
		}
		case final AtomicStatement atomicStmt -> typecheckBlock(outer, allLabels, atomicStmt.getBody());
		case final CallStatement call -> {
			final ProcedureInfo procInfo = mDeclaredProcedures.get(call.getMethodName());
			if (procInfo == null) {
				typeError(statement, "Calling undeclared procedure " + call);
				return;
			}
			checkModifiesTransitive(call, call.getMethodName());
			if (call.isForall()) {
				final Specification[] spec = procInfo.getDeclaration().getSpecification();
				for (final Specification s : spec) {
					if (s instanceof ModifiesSpecification && !s.isFree()) {
						typeError(statement, "call forall on method with checked modifies: " + statement);
						break;
					}
				}
			}
			final BoogieType[] typeParams = new BoogieType[procInfo.getTypeParameters().getCount()];
			final VariableInfo[] inParams = procInfo.getInParams();
			final Expression[] arguments = call.getArguments();
			if (arguments.length != inParams.length) {
				typeError(statement, "Procedure called with wrong number of arguments: " + call);
				return;
			}
			for (int i = 0; i < arguments.length; i++) {
				/* check for wildcard expression and just skip them. */
				if (call.isForall() && (arguments[i] instanceof WildcardExpression)) {
					arguments[i].setType(inParams[i].getType());
					continue;
				}
				final BoogieType t = typecheckExpression(arguments[i]);
				if (!inParams[i].getType().unify(t, typeParams)) {
					typeError(statement, "Wrong parameter type at index " + i + ": " + call);
				}
			}
			final VariableInfo[] outParams = procInfo.getOutParams();
			final VariableLHS[] lhs = call.getLhs();
			if (lhs.length != outParams.length) {
				typeError(statement, "Number of output variables do not match in " + statement);
			} else {
				for (int i = 0; i < lhs.length; i++) {
					for (int j = 0; j < i; j++) {
						if (lhs[i].getIdentifier().equals(lhs[j].getIdentifier())) {
							typeError(statement, "Variable appears multiple times in assignment: " + statement);
						}
					}
					final BoogieType type = typecheckLeftHandSide(lhs[i]);
					if (!outParams[i].getType().unify(type, typeParams)) {
						typeError(statement, "Type mismatch (output parameter " + i + ") in " + statement);
					}
				}
			}
		}
		case final ForkStatement fork -> {
			final ProcedureInfo procInfo = mDeclaredProcedures.get(fork.getProcedureName());
			if (procInfo == null) {
				typeError(statement, "Forking undeclared procedure " + fork);
				return;
			}
			checkModifiesTransitive(fork, fork.getProcedureName());
			final BoogieType[] typeParams = new BoogieType[procInfo.getTypeParameters().getCount()];
			final VariableInfo[] inParams = procInfo.getInParams();
			final Expression[] arguments = fork.getArguments();
			if (arguments.length != inParams.length) {
				typeError(statement, "Procedure forked with wrong number of arguments: " + fork);
				return;
			}
			for (int i = 0; i < arguments.length; i++) {
				final BoogieType t = typecheckExpression(arguments[i]);
				if (!inParams[i].getType().unify(t, typeParams)) {
					typeError(statement, "Wrong parameter type at index " + i + ": " + fork);
				}
			}
			for (final Expression threadId : fork.getThreadID()) {
				typecheckExpression(threadId);
			}
		}
		case final JoinStatement join -> {
			for (final Expression threadId : join.getThreadID()) {
				if (threadId == null) {
					typeError(statement, "Expression " + threadId + " does not exist.");
				}
				typecheckExpression(threadId);
			}
			for (int i = 0; i < join.getLhs().length; i++) {
				typecheckLeftHandSide(join.getLhs()[i]);
			}
		}
		}
	}

	/**
	 * Type check the given block.
	 *
	 * @param outer
	 *            the labels right before some outer block.
	 * @param allLabels
	 *            all labels appearing in the implementation body.
	 * @param block
	 *            the code to type check.
	 */
	private void typecheckBlock(final Stack<String> outer, final HashSet<String> allLabels, final Statement[] block) {
		int numLabels = 0;
		for (final Statement s : block) {
			if (s instanceof final Label label) {
				outer.push(label.getName());
				numLabels++;
			} else {
				typecheckStatement(outer, allLabels, s);
				while (numLabels-- > 0) {
					outer.pop();
				}
			}
		}
	}

	/**
	 * Check if it is legal to modify variable var and if the variable was declared at all. It is not legal to modify an
	 * in-parameter of a procedure. It is not legal to modify an global variable that does not appear in the modifies
	 * clause of the procedure.
	 *
	 * @param lhs
	 *            location of the checked variable
	 * @return BoogieType of the checked variable. errorType if the variable was not declared.
	 */
	private BoogieType checkVarModification(final BoogieASTNode BoogieASTNode, final String var) {
		if (mInParams.contains(var)) {
			final String message = "Local variable " + var + " modified in " + " procedure " + mCurrentProcedure
					+ " but is an " + "in-parameter of this procedure";
			typeError(BoogieASTNode, message);
			return findVariable(var).getType();
		} else if (mOutParams.contains(var)) {
			// var is out parameter (may shadow global var), modification is
			// legal
			return findVariable(var).getType();
		} else if (mLocalVars.contains(var)) {
			// var is local variable (may shadow global var), modification is
			// legal
			return findVariable(var).getType();
		} else if (mGlobals.contains(var)) {
			final Set<String> modifiedGlobals = mProc2ModfiedGlobals.get(mCurrentProcedure);
			if (!modifiedGlobals.contains(var)) {
				final String message = "Global variable " + var + " modified in " + " procedure " + mCurrentProcedure
						+ " but not " + "contained in procedures modifies clause.";
				typeError(BoogieASTNode, message);
			}
			return findVariable(var).getType();
		} else {
			final String message =
					"Variable " + var + " modified in procedure " + mCurrentProcedure + " but not declared";
			typeError(BoogieASTNode, message);
			return BoogieType.TYPE_ERROR;
		}
	}

	/**
	 * Check if each modified variable of the called procedure is in the modifies clause of the current procedure.
	 */
	private void checkModifiesTransitive(final CallStatement call, final String callee) {
		checkModifiesTransitive((Statement) call, callee);
	}

	/**
	 * Check if each modified variable of the called procedure is in the modifies clause of the current procedure.
	 */
	private void checkModifiesTransitive(final ForkStatement fork, final String callee) {
		checkModifiesTransitive((Statement) fork, callee);
	}

	/**
	 * Check if each modified variable of the called procedure is in the modifies clause of the current procedure.
	 */
	private void checkModifiesTransitive(final Statement stmt, final String callee) {
		final String caller = mCurrentProcedure;
		final Set<String> calleeModifiedGlobals = mProc2ModfiedGlobals.get(callee);
		final Set<String> callerModifiedGlobals = mProc2ModfiedGlobals.get(caller);
		for (final String var : calleeModifiedGlobals) {
			if (!callerModifiedGlobals.contains(var)) {
				final String message = "Procedure " + callee + " may modify " + var + " procedure " + caller
						+ " must not modify " + var + ". " + stmt + " calls " + callee + ". Modifies not transitive";
				typeError(stmt, message);
			}
		}
	}

	private void processBody(final Body body, final String prodecureId) {
		final DeclarationInformation declInfo = new DeclarationInformation(StorageClass.LOCAL, prodecureId);
		mVarScopes.beginScope();
		for (final VariableDeclaration decl : body.getLocalVars()) {
			for (final VarList vl : decl.getVariables()) {
				assert vl.getType() != null : "Variable list without type";
				final BoogieType type = mTypeManager.resolveType(vl.getType());
				if (type.equals(BoogieType.TYPE_ERROR)) {
					typeError(vl, "VarList has unresolveable type " + vl.getType());
				}
				for (final String id : vl.getIdentifiers()) {
					checkIfAlreadyInOutLocal(vl, id);
					mLocalVars.add(id);
					mVarScopes.put(id, new VariableInfo(false, decl, id, type, declInfo));
				}
			}
		}

		/* Now check where clauses */
		for (final VariableDeclaration decl : body.getLocalVars()) {
			for (final VarList vl : decl.getVariables()) {
				if (vl.getWhereClause() != null) {
					final BoogieType t = typecheckExpression(vl.getWhereClause());
					if (!t.equals(BoogieType.TYPE_BOOL) && !t.equals(BoogieType.TYPE_ERROR)) {
						typeError(vl.getWhereClause(), "Where clause is not boolean: " + decl);
					}
				}
			}
		}

		/* Get Labels */
		final HashSet<String> labels = new HashSet<>();
		processLabels(labels, body.getBlock());
		/* Finally check statements */
		typecheckBlock(new Stack<>(), labels, body.getBlock());
		mVarScopes.endScope();
	}

	private void processImplementation(final Procedure impl) {
		if (impl.getBody() == null) {
			/* This is a procedure declaration without body. Nothing to check. */
			return;
		}
		final ProcedureInfo procInfo = mDeclaredProcedures.get(impl.getIdentifier());
		if (procInfo == null) {
			typeError(impl, "Implementation without procedure: " + impl.getIdentifier());
			return;
		}
		final TypeParameters typeParams = new TypeParameters(impl.getTypeParams());
		mTypeManager.pushTypeScope(typeParams);

		mCurrentProcedure = impl.getIdentifier();
		mInParams = new HashSet<>();
		mOutParams = new HashSet<>();
		mLocalVars = new HashSet<>();
		DeclarationInformation declInfoInParam;
		DeclarationInformation declInfoOutParam;
		// We call this procedure object a pure implementation if it contains
		// only the implementation and another procedure object contains the
		// specification
		final boolean isPureImplementation = procInfo.getDeclaration() != impl;
		if (isPureImplementation) {
			declInfoInParam = new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, impl.getIdentifier());
			declInfoOutParam = new DeclarationInformation(StorageClass.IMPLEMENTATION_OUTPARAM, impl.getIdentifier());
		} else {
			declInfoInParam = new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, impl.getIdentifier());
			declInfoOutParam = new DeclarationInformation(StorageClass.PROC_FUNC_OUTPARAM, impl.getIdentifier());
		}
		mVarScopes.beginScope();
		final VariableInfo[] procInParams = procInfo.getInParams();
		final VariableInfo[] procOutParams = procInfo.getOutParams();
		int i = 0;
		for (final VarList vl : impl.getInParams()) {
			final BoogieType type = mTypeManager.resolveType(vl.getType());
			for (final String id : vl.getIdentifiers()) {
				if (i >= procInParams.length) {
					typeError(vl, "Too many input parameters in " + impl);
				} else if (!procInParams[i++].getType().equals(type)) {
					typeError(vl, "Type differs at parameter " + id + " in " + impl);
				}
				checkIfAlreadyInOutLocal(vl, id);
				mInParams.add(id);
				mVarScopes.put(id, new VariableInfo(true /* in params are rigid */, impl, id, type, declInfoInParam));
			}
		}
		if (i < procInParams.length) {
			typeError(impl, "Too few input parameters in " + impl);
		}
		if (!typeParams.fullyUsed()) {
			typeError(impl, "Type args not fully used in implementation: " + impl);
		}
		i = 0;
		for (final VarList vl : impl.getOutParams()) {
			final BoogieType type = mTypeManager.resolveType(vl.getType());
			for (final String id : vl.getIdentifiers()) {
				if (i >= procOutParams.length) {
					typeError(vl, "Too many output parameters in " + impl);
				} else if (!procOutParams[i++].getType().equals(type)) {
					typeError(vl, "Type differs at parameter " + id + " in " + impl);
				}
				checkIfAlreadyInOutLocal(vl, id);
				mOutParams.add(id);
				mVarScopes.put(id, new VariableInfo(false, impl, id, type, declInfoOutParam));

			}
		}
		if (i < procOutParams.length) {
			typeError(impl, "Too few output parameters in " + impl);
		}

		processBody(impl.getBody(), impl.getIdentifier());

		mVarScopes.endScope();
		mTypeManager.popTypeScope();
	}

	/**
	 * Check if identifier id was already used in the definition of an in parameter, out parameter of local variable.
	 */
	private void checkIfAlreadyInOutLocal(final VarList vl, final String id) {
		if (mInParams.contains(id)) {
			typeError(vl, id + " already declared as in parameter");
		}
		if (mOutParams.contains(id)) {
			typeError(vl, id + " already declared as out parameter");
		}
		if (mLocalVars.contains(id)) {
			typeError(vl, id + " already declared as local variable");
		}
	}

	@Override
	public boolean process(final IElement root) {
		if (root instanceof final Unit unit) {
			mDeclaredVars = new HashMap<>();
			mDeclaredFunctions = new HashMap<>();
			mDeclaredProcedures = new HashMap<>();
			mVarScopes = new ScopedHashMap<>();
			// pass1: parse type declarations
			mTypeManager = new TypeManager(unit.getDeclarations(),
					mServices.getLoggingService().getLogger(Activator.PLUGIN_ID));
			mTypeManager.init();
			// pass2: variable, constant and function declarations
			for (final Declaration decl : unit.getDeclarations()) {
				if (decl instanceof final FunctionDeclaration funcdecl) {
					processFunctionDeclaration(funcdecl);
				} else if (decl instanceof final VariableDeclaration vardecl) {
					processVariableDeclaration(vardecl);
				} else if (decl instanceof final ConstDeclaration constdecl) {
					processConstDeclaration(constdecl);
				}
			}

			// pass2,5 :) LTL property declarations
			final LTLPropertyCheck propCheck = LTLPropertyCheck.getAnnotation(unit);
			if (propCheck != null) {
				for (final VariableDeclaration decl : propCheck.getGlobalDeclarations()) {
					processVariableDeclaration(decl);
				}
				for (final Entry<String, CheckableExpression> entry : propCheck.getCheckableAtomicPropositions()
						.entrySet()) {
					// FIXME: what about those statements?
					// for (Statement stmt : entry.getValue().getStatements()) {
					//
					// }
					typecheckExpression(entry.getValue().getExpression());
				}
			}

			// pass3: attributes function definition, axioms,
			// procedure declarations, where clauses
			for (final Declaration decl : unit.getDeclarations()) {
				typecheckAttributes(decl.getAttributes());
				if (decl instanceof final ConstDeclaration constdecl) {
					checkConstDeclaration(constdecl);
				} else if (decl instanceof final FunctionDeclaration funcdecl) {
					processFunctionDefinition(funcdecl);
				} else if (decl instanceof final Axiom axiom) {
					typecheckExpression(axiom.getFormula());
				} else if (decl instanceof final Procedure proc) {
					processProcedureDeclaration(proc);
				} else if (decl instanceof final VariableDeclaration vardecl) {
					/* check where clauses */
					for (final VarList vl : vardecl.getVariables()) {
						if (vl.getWhereClause() != null) {
							final BoogieType t = typecheckExpression(vl.getWhereClause());
							if (!t.equals(BoogieType.TYPE_BOOL) && !t.equals(BoogieType.TYPE_ERROR)) {
								typeError(vl.getWhereClause(), "Where clause is not boolean: " + decl);
							}
						}
					}
				}
			}
			// pass4: procedure definitions, implementations
			for (final Declaration decl : unit.getDeclarations()) {
				if (decl instanceof final Procedure proc) {
					processImplementation(proc);
				}
			}
			return false;
		}
		return true;
	}

	private void typeError(final BoogieASTNode BoogieASTNode, final String message) {
		final TypeErrorResult<BoogieASTNode> result = new TypeErrorResult<>(BoogieASTNode, Activator.PLUGIN_ID,
				mServices.getBacktranslationService(), message);
		mLogger.error(BoogieASTNode.getLocation() + ": " + message);
		mServices.getResultService().reportResult(Activator.PLUGIN_ID, result);
		mServices.getProgressMonitorService().cancelToolchain();
	}

	public class TypeErrorReporter implements ITypeErrorReporter<String> {

		private final BoogieASTNode mReportNode;

		TypeErrorReporter(final BoogieASTNode reportNode) {
			mReportNode = reportNode;
		}

		@Override
		public void report(final Function<String, String> func) {
			// final Pair<BoogieASTNode, String> res = func.apply(mReportNode);
			final String pp;
			if (mReportNode instanceof final Expression expr) {
				pp = BoogiePrettyPrinter.print(expr);
			} else if (mReportNode instanceof final Statement stmt) {
				pp = BoogiePrettyPrinter.print(stmt);
			} else {
				pp = mReportNode.toString();
			}
			typeError(mReportNode, func.apply(pp));
		}

	}

	// class InternalErrorReporter implements ITypeErrorReporter<Object, String> {
	//
	// private final Object mReportNode;
	//
	// InternalErrorReporter(final Object reportNode) {
	// mReportNode = reportNode;
	// }
	//
	// @Override
	// public void report(final Function<Object, String> func) {
	// TypeCheckHelper.internalError(func.apply(mReportNode));
	// }
	//
	// }

}
