package de.uni_freiburg.informatik.ultimate.civlizer;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AtomicStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitVectorAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BreakStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ForkStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.JoinStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RequiresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
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
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.WitnessGhostUpdate;


final class ThreadTemplateVisitor extends BoogieVisitor {

	private String mCurrentProcedure;
	private ILocation mCurrentStatement;

	private Set<String> mGlobalVariables;
	private Map<ILocation, Set<String>> mStatementVariablesMap;
	private Map<ILocation, Set<String>> mStatementParametersMap;
	private Map<String, Map<String, ASTType>> mProcedureVariablesMap;
	
	private Map<String, List<Tid>> mAssociationTidMap;
	private Map<String, List<Tid>> mUsedTidMap;
	private Map<String, List<Tid>> mAllTidMap;
	private Set<Tid> mTids;

	ThreadTemplateVisitor(Unit boogieFile) {
		mCurrentProcedure = null;
		mCurrentStatement = null;

		mGlobalVariables = new HashSet<>();
		mStatementVariablesMap = new HashMap<>();
		mStatementParametersMap = new HashMap<>();
		mProcedureVariablesMap = new HashMap<>();

		mAssociationTidMap = new HashMap<>();
		mUsedTidMap = new HashMap<>();
		mAllTidMap = new HashMap<>();
		mTids = new HashSet<>();

		for (Declaration elem : boogieFile.getDeclarations()) {
			processDeclaration(elem);
        }

		for (String key : mAssociationTidMap.keySet()) {
			mAllTidMap.put(key, new ArrayList<>(mAssociationTidMap.get(key)));
		}

		for (String key : mUsedTidMap.keySet()) {
			mAllTidMap
				.computeIfAbsent(key, k -> new ArrayList<>())
				.addAll(mUsedTidMap.get(key));
		}

		// TODO improve use set instead of list
		// remove duplicates per list
		for (List<Tid> list : mAllTidMap.values()) {
			Set<Tid> dedup = new LinkedHashSet<>(list);
			list.clear();
			list.addAll(dedup);
		}

		for (List<Tid> tidList : mAllTidMap.values()) {
			for (Tid tid : tidList) {
				mTids.add(tid);
			}
		}
	}

	Map<ILocation, Set<String>> getStatementParametersMap() {
		return mStatementParametersMap;
	}

	Map<String, Map<String, ASTType>> getProcedureVariablesMap() {
		return mProcedureVariablesMap;
	}

	Set<Tid> getTids() {
		return mTids;
	}

	Map<String, List<Tid>> getAssociationTidMap() {
		return mAssociationTidMap;
	}

	Map<String, List<Tid>> getUsedTidMap() {
		return mUsedTidMap;
	}

	Map<String, List<Tid>> getAllTidMap() {
		return mAllTidMap;
	}

	boolean containsGlobalVariables(Statement stmt) {
		if (mStatementVariablesMap
			.get(stmt.getLoc()) == null 
			|| mGlobalVariables == null) {
			return false;
		}

		return !Collections.disjoint(
			mStatementVariablesMap
			.get(stmt.getLoc()), 
			mGlobalVariables
		);
	}

	boolean containsLocalVariables(String procName, Statement stmt) {
		if (mStatementVariablesMap
			.get(stmt.getLoc()) == null 
			|| mGlobalVariables == null) {
			return false;
		}

		return !Collections.disjoint(
			mStatementVariablesMap
			.get(stmt.getLoc()), 
			mProcedureVariablesMap.get(procName).keySet()
		);
	}

	@Override
	protected Declaration processDeclaration(final Declaration decl) {
		switch (decl) {
			case final VariableDeclaration varDecl -> {
				for (VarList varList : varDecl.getVariables()) {
					for (String id : varList.getIdentifiers()) {
						mGlobalVariables.add(id);
					}
				}
			}
			case final Procedure proc -> visit(proc);
			default -> {}
		}
		return decl;
	}

	@Override
	protected void visit(final Procedure decl) {
		mCurrentProcedure = decl.getIdentifier();
		Map res = new HashMap<>();

		for (VariableDeclaration varDecl: decl.getBody().getLocalVars()) {
			for (VarList varList : varDecl.getVariables()) {
				for (String id : varList.getIdentifiers()) {
					res.put(id, varList.getType());
				}
			}
		}

		mProcedureVariablesMap.put(mCurrentProcedure, res);
		

		if (!mCurrentProcedure.equals("ULTIMATE.start") && !mAssociationTidMap.containsKey(mCurrentProcedure)) {
			mAssociationTidMap.put(mCurrentProcedure, new ArrayList<>());
		}

		for (Statement stmt : decl.getBody().getBlock()) {

			// TEST

			if (WitnessGhostUpdate.getAnnotation(stmt) != null) {
				Map<?, ?> update = WitnessGhostUpdate.getAnnotation(stmt).getUpdate();
				if (update != null) {
					for (Map.Entry<?, ?> entryUpdate : update.entrySet()) {
						Object key = entryUpdate.getKey();
						Object value = entryUpdate.getValue();

						System.out.println(key + " -> " + value);
					}
				}
			}

			// TEST

			processStatement(stmt);

			Set<String> parameters = new HashSet<>();

			for (String id : mStatementVariablesMap.getOrDefault(stmt.getLoc(), new HashSet<>())) {
				if (mProcedureVariablesMap
					.get(mCurrentProcedure)
					.keySet()
					.contains(id)) {

					parameters.add(id);
				}
			}

			mStatementParametersMap.put(stmt.getLoc(), parameters);
		}
	}

	@Override
	protected Statement processStatement(final Statement statement) {

		mCurrentStatement = statement.getLoc();

		switch (statement) {
			case final AssertStatement assertStmt -> visit(assertStmt);
			case final AssignmentStatement assignStmt -> visit(assignStmt);
			case final AssumeStatement assumeStmt -> visit(assumeStmt);
			case final AtomicStatement atomicStmt -> visit(atomicStmt);
			case final BreakStatement breakStmt -> visit(breakStmt);
			case final CallStatement callStmt -> visit(callStmt);
			case final ForkStatement forkStmt -> visit(forkStmt);
			case final GotoStatement gotoStmt -> visit(gotoStmt);
			case final HavocStatement havocStmt -> visit(havocStmt);
			case final IfStatement ifStmt -> visit(ifStmt);
			case final JoinStatement joinStmt -> visit(joinStmt);
			case final Label label -> visit(label);
			case final ReturnStatement returnStmt -> visit(returnStmt);
			case final WhileStatement whileStmt -> visit(whileStmt);
		}

		return statement;
	}

	@Override
	protected void visit(final WhileStatement statement) {
		for (Statement stmt : statement.getBody()) {
			processStatement(stmt);
		}
	}

	@Override
	protected void visit(final AtomicStatement statement) {
		for (Statement stmt : statement.getBody()) {
			processStatement(stmt);
			Set<String> res = mStatementVariablesMap
				.getOrDefault(statement.getLoc(), new HashSet());
			res.addAll(mStatementVariablesMap
				.getOrDefault(stmt.getLoc(), new HashSet())
			);
			mStatementVariablesMap.put(statement.getLoc(), res);
		}
	}

	@Override
	protected void visit(final IfStatement statement) {
		for (Statement stmt : statement.getThenPart()) {
			processStatement(stmt);
		}

		for (Statement stmt : statement.getElsePart()) {
			processStatement(stmt);
		}
	}

	@Override
	protected void visit(final ForkStatement statement) {

		Tid tid = new Tid(statement.getThreadID());
		List<Tid> tids = mAssociationTidMap.getOrDefault(statement.getProcedureName(), new ArrayList<>());

		if (!mAssociationTidMap.containsKey(tid)) {
			if (tids == null) {
				mAssociationTidMap.put(
					statement.getProcedureName(),
					new ArrayList<>(Collections.singletonList(tid))
				);
			}
			else {
				tids.add(tid);
			}
		}

		tids = mUsedTidMap.get(mCurrentProcedure);

		if (!mUsedTidMap.containsKey(tid)) {
			if (tids == null) {
				mUsedTidMap.put(
					mCurrentProcedure,
					new ArrayList<>(Collections.singletonList(tid))
				);
			}
			else {
				tids.add(tid);
			}
		}
	}

	@Override
	protected void visit(final JoinStatement statement) {

		Tid tid = new Tid(statement.getThreadID());
		List<Tid> tids = mAssociationTidMap.get(mCurrentProcedure);

		if (!mAssociationTidMap.containsKey(tid)) {
			if (tids == null) {
				mAssociationTidMap.put(
					mCurrentProcedure,
					new ArrayList<>(Collections.singletonList(tid))
				);
			}
			else {
				tids.add(tid);
			}
		}
	}

	@Override
	protected void visit(final HavocStatement statement) {
		// empty because it may be overridden (but does not have to)
		Set<String> res;
		for (VariableLHS var : statement.getIdentifiers()) {
			res = mStatementVariablesMap
				.getOrDefault(mCurrentStatement, new HashSet());
			res.add(var.getIdentifier());
			mStatementVariablesMap.put(mCurrentStatement, res);
		}
	}

	/*protected void visit(final CallStatement statement) {
		// empty because it may be overridden (but does not have to)
	}*/

	@Override
	protected void visit(final AssignmentStatement statement) {
		for (LeftHandSide lhs : statement.getLhs()) {
			processLeftHandSide(lhs);
		}

		for (Expression rhs : statement.getRhs()) {
			processExpression(rhs);
		}
	}

	@Override
	protected void visit(final AssumeStatement statement) {
		processExpression(statement.getFormula());
	}

	@Override
	protected void visit(final AssertStatement statement) {
		processExpression(statement.getFormula());
	}

	@Override
	protected void visit(final VariableLHS lhs) {
		Set<String> res = mStatementVariablesMap
			.getOrDefault(mCurrentStatement, new HashSet());
		res.add(lhs.getIdentifier());
		mStatementVariablesMap.put(mCurrentStatement, res);
	}

	@Override
	protected void visit(final StructLHS lhs) {
		// empty because it may be overridden (but does not have to)
	}

	@Override
	protected void visit(final ArrayLHS lhs) {
		// empty because it may be overridden (but does not have to)
	}

	@Override
	protected void visit(final RequiresSpecification spec) {
		// empty because it may be overridden (but does not have to)
	}

	@Override
	protected void visit(final ModifiesSpecification spec) {
		// empty because it may be overridden (but does not have to)
	}

	@Override
	protected void visit(final LoopInvariantSpecification spec) {
		// empty because it may be overridden (but does not have to)
	}

	@Override
	protected void visit(final EnsuresSpecification spec) {
		// empty because it may be overridden (but does not have to)
	}

	@Override
	protected void visit(final NamedAttribute attr) {
		// empty because it may be overridden (but does not have to)
	}

	@Override
	protected void visit(final Trigger attr) {
		// empty because it may be overridden (but does not have to)
	}

	@Override
	protected void visit(final WildcardExpression expr) {
		// empty because it may be overridden (but does not have to)
	}

	@Override
	protected void visit(final UnaryExpression expr) {
		processExpression(expr.getExpr());
	}

	@Override
	protected void visit(final StructConstructor expr) {
		for (Expression fieldExpr : expr.getFieldValues()) {
			processExpression(fieldExpr);
		}
	}

	@Override
	protected void visit(final StructAccessExpression expr) {
		processExpression(expr.getStruct());
	}

	@Override
	protected void visit(final QuantifierExpression expr) {

		for (VarList varList : expr.getParameters()) {
			for (String id : varList.getIdentifiers()) {

				Set<String> res = mStatementVariablesMap
					.getOrDefault(mCurrentStatement, new HashSet<>());

				res.add(id);
				mStatementVariablesMap.put(mCurrentStatement, res);
			}
		}

		processExpression(expr.getSubformula());
	}

	@Override
	protected void visit(final IfThenElseExpression expr) {
		processExpression(expr.getCondition());
		processExpression(expr.getThenPart());
		processExpression(expr.getElsePart());
	}

	@Override
	protected void visit(final IdentifierExpression expr) {

		Set<String> res = mStatementVariablesMap
			.getOrDefault(mCurrentStatement, new HashSet<>());

		res.add(expr.getIdentifier());
		mStatementVariablesMap.put(mCurrentStatement, res);
	}

	@Override
	protected void visit(final FunctionApplication expr) {

		for (Expression arg : expr.getArguments()) {
			processExpression(arg);
		}
	}

	@Override
	protected void visit(final BinaryExpression expr) {
		processExpression(expr.getLeft());
		processExpression(expr.getRight());
	}

	@Override
	protected void visit(final ArrayStoreExpression expr) {

		//processExpression(expr.getArray());
		//processExpression(expr.getIndex());
		//processExpression(expr.getValue());
	}

	@Override
	protected void visit(final ArrayAccessExpression expr) {

		processExpression(expr.getArray());

		for (Expression index : expr.getIndices()) {
			processExpression(index);
		}
	}

	@Override
	protected void visit(final BitVectorAccessExpression expr) {
		processExpression(expr.getBitvec());
	}
}