/*
 * Copyright (C) 2026 Dominik Klumpp (klumpp@lix.polytechnique.fr)
 * Copyright (C) 2026 École Polytechnique
 *
 * This file is part of the ULTIMATE Civlizer plug-in.
 *
 * The ULTIMATE Civlizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Civlizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Civlizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Civlizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Civlizer plug-in grant you additional permission
 * to convey the resulting work.
 */
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
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AtomicStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitVectorAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BreakStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
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
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.WitnessGhostUpdate;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.WitnessInvariant;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;

/**
 * Visitor over a Boogie AST that extracts thread-related metadata, variable usage information and annotation data from
 * a program.
 *
 * <p>
 * This visitor builds several internal mappings while traversing a Boogie program, including:
 * <ul>
 * <li>Global and procedure-local variable usage per statement location</li>
 * <li>Procedure parameter usage derived from statements</li>
 * <li>Thread identifiers (TIDs) associated or used in thread template</li>
 * <li>Entry, exit, and final invariants extracted from witness annotations</li>
 * </ul>
 *
 * <p>
 * The collected information is later used by the Civlizer analysis pipeline to reason about concurrency structure and
 * thread associations.
 *
 * <p>
 * Thread identifiers are represented using {@link Tid}, and are tracked in association, usage, and global TID sets.
 */
final class ThreadTemplateVisitor extends BoogieVisitor {

	private final BoogieIcfgContainer mIcfg;
	private String mCurrentProcedure;
	private ILocation mCurrentStatement;

	private final Set<String> mGlobalVariables;
	private final Map<ILocation, Set<String>> mStatementVariablesMap;
	private final Map<ILocation, Set<String>> mStatementParametersMap;
	private final Map<String, Map<String, ASTType>> mProcedureVariablesMap;

	private final Map<String, Expression> mEntryAnnotationMap;
	private final Map<String, Expression> mExitAnnotationMap;
	private final Map<String, Expression> mFinalAnnotationMap;

	private final Map<String, List<Tid>> mAssociationTidMap;
	private final Map<String, List<Tid>> mUsedTidMap;
	private final Map<String, List<Tid>> mAllTidMap;
	private final Set<Tid> mTids;

	ThreadTemplateVisitor(final Unit boogieFile, final BoogieIcfgContainer icfg) {
		mIcfg = icfg;
		mCurrentProcedure = null;
		mCurrentStatement = null;

		mGlobalVariables = new HashSet<>();
		mStatementVariablesMap = new HashMap<>();
		mStatementParametersMap = new HashMap<>();
		mProcedureVariablesMap = new HashMap<>();

		mEntryAnnotationMap = new HashMap<>();
		mExitAnnotationMap = new HashMap<>();
		mFinalAnnotationMap = new HashMap<>();

		mAssociationTidMap = new HashMap<>();
		mUsedTidMap = new HashMap<>();
		mAllTidMap = new HashMap<>();
		mTids = new HashSet<>();

		for (final Declaration elem : boogieFile.getDeclarations()) {
			processDeclaration(elem);
		}

		for (final String key : mAssociationTidMap.keySet()) {
			mAllTidMap.put(key, new ArrayList<>(mAssociationTidMap.get(key)));
		}

		for (final String key : mUsedTidMap.keySet()) {
			final List<Tid> tids = mAllTidMap.computeIfAbsent(key, k -> new ArrayList<>());

			for (final Tid tid : mUsedTidMap.get(key)) {
				if (!tids.contains(tid)) {
					tids.add(tid);
				}
			}
		}

		// remove duplicates per list
		for (final List<Tid> list : mAllTidMap.values()) {
			final Set<Tid> dedup = new LinkedHashSet<>(list);
			list.clear();
			list.addAll(dedup);
		}

		for (final List<Tid> tidList : mAllTidMap.values()) {
			mTids.addAll(tidList);
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

	Map<String, Expression> getEntryAnnotationMap() {
		return mEntryAnnotationMap;
	}

	Map<String, Expression> getExitAnnotationMap() {
		return mExitAnnotationMap;
	}

	Map<String, Expression> getFinalAnnotationMap() {
		return mFinalAnnotationMap;
	}

	boolean containsGlobalVariables(final Statement stmt) {
		if (mStatementVariablesMap.get(stmt.getLoc()) == null || mGlobalVariables == null) {
			return false;
		}

		return !Collections.disjoint(mStatementVariablesMap.get(stmt.getLoc()), mGlobalVariables);
	}

	boolean containsLocalVariables(final String procName, final Statement stmt) {
		if (mStatementVariablesMap.get(stmt.getLoc()) == null || mGlobalVariables == null) {
			return false;
		}

		return !Collections.disjoint(mStatementVariablesMap.get(stmt.getLoc()),
				mProcedureVariablesMap.get(procName).keySet());
	}

	@Override
	protected Declaration processDeclaration(final Declaration decl) {
		switch (decl) {
		case final VariableDeclaration varDecl -> {
			for (final VarList varList : varDecl.getVariables()) {
				Collections.addAll(mGlobalVariables, varList.getIdentifiers());
			}
		}
		case final Procedure proc -> visit(proc);
		default -> {
		}
		}
		return decl;
	}

	@Override
	protected void visit(final Procedure decl) {
		mCurrentProcedure = decl.getIdentifier();

		final var icfgEntryLoc = mIcfg.getProcedureEntryNodes().get(mCurrentProcedure);
		final Expression entryInvariant = (Expression) WitnessInvariant.getAnnotation(icfgEntryLoc).getInvariant();
		mEntryAnnotationMap.put(mCurrentProcedure, entryInvariant);

		final var icfgExitLoc = mIcfg.getProcedureExitNodes().get(mCurrentProcedure);
		final Expression exitInvariant = (Expression) WitnessInvariant.getAnnotation(icfgExitLoc).getInvariant();
		mExitAnnotationMap.put(mCurrentProcedure, exitInvariant);

		// final on declaration
		if (WitnessInvariant.getAnnotation(decl) != null) {
			final Expression finalInvariant = (Expression) WitnessInvariant.getAnnotation(decl).getInvariant();
			mFinalAnnotationMap.put(mCurrentProcedure, finalInvariant);
		}

		final Map res = new HashMap<>();

		for (final VariableDeclaration varDecl : decl.getBody().getLocalVars()) {
			for (final VarList varList : varDecl.getVariables()) {
				for (final String id : varList.getIdentifiers()) {
					res.put(id, varList.getType());
				}
			}
		}

		mProcedureVariablesMap.put(mCurrentProcedure, res);

		if (!mCurrentProcedure.equals("ULTIMATE.start") && !mAssociationTidMap.containsKey(mCurrentProcedure)) {
			mAssociationTidMap.put(mCurrentProcedure, new ArrayList<>());
		}

		for (final Statement stmt : decl.getBody().getBlock()) {

			// TEST

			if (WitnessGhostUpdate.getAnnotation(stmt) != null) {
				final Map<?, ?> update = WitnessGhostUpdate.getAnnotation(stmt).getUpdate();
				if (update != null) {
					for (final Map.Entry<?, ?> entryUpdate : update.entrySet()) {
						final Object key = entryUpdate.getKey();
						final Object value = entryUpdate.getValue();

						System.out.println(key + " -> " + value);
					}
				}
			}

			// TEST

			processStatement(stmt);

			final Set<String> parameters = new HashSet<>();

			for (final String id : mStatementVariablesMap.getOrDefault(stmt.getLoc(), new HashSet<>())) {
				if (mProcedureVariablesMap.get(mCurrentProcedure).containsKey(id)) {

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
		processExpression(statement.getCondition());
		for (final Statement stmt : statement.getBody()) {
			processStatement(stmt);
		}
	}

	@Override
	protected void visit(final AtomicStatement statement) {
		for (final Statement stmt : statement.getBody()) {
			processStatement(stmt);
			final Set<String> res = mStatementVariablesMap.getOrDefault(statement.getLoc(), new HashSet());
			res.addAll(mStatementVariablesMap.getOrDefault(stmt.getLoc(), new HashSet()));
			mStatementVariablesMap.put(statement.getLoc(), res);
		}
	}

	@Override
	protected void visit(final IfStatement statement) {
		processExpression(statement.getCondition());
		for (final Statement stmt : statement.getThenPart()) {
			processStatement(stmt);
		}
		for (final Statement stmt : statement.getElsePart()) {
			processStatement(stmt);
		}
	}

	@Override
	protected void visit(final ForkStatement statement) {

		final Tid tid = new Tid(statement.getThreadID());

		List<Tid> tids = mAssociationTidMap.getOrDefault(statement.getProcedureName(), new ArrayList<>());

		if (!tids.contains(tid)) {
			tids.add(tid);
		}

		mAssociationTidMap.put(statement.getProcedureName(), tids);

		tids = mUsedTidMap.getOrDefault(mCurrentProcedure, new ArrayList<>());

		if (!tids.contains(tid)) {
			tids.add(tid);
		}

		mUsedTidMap.put(mCurrentProcedure, tids);
	}

	@Override
	protected void visit(final JoinStatement statement) {

		final Tid tid = new Tid(statement.getThreadID());

		final List<Tid> tids = mUsedTidMap.getOrDefault(mCurrentProcedure, new ArrayList<>());

		if (!tids.contains(tid)) {
			tids.add(tid);
		}

		mUsedTidMap.put(mCurrentProcedure, tids);
	}

	@Override
	protected void visit(final HavocStatement statement) {
		// empty because it may be overridden (but does not have to)
		Set<String> res;
		for (final VariableLHS var : statement.getIdentifiers()) {
			res = mStatementVariablesMap.getOrDefault(mCurrentStatement, new HashSet());
			res.add(var.getIdentifier());
			mStatementVariablesMap.put(mCurrentStatement, res);
		}
	}

	/*
	 * protected void visit(final CallStatement statement) { // empty because it may be overridden (but does not have
	 * to) }
	 */

	@Override
	protected void visit(final AssignmentStatement statement) {
		for (final LeftHandSide lhs : statement.getLhs()) {
			processLeftHandSide(lhs);
		}

		for (final Expression rhs : statement.getRhs()) {
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
		final Set<String> res = mStatementVariablesMap.getOrDefault(mCurrentStatement, new HashSet());
		res.add(lhs.getIdentifier());
		mStatementVariablesMap.put(mCurrentStatement, res);
	}

	@Override
	protected void visit(final UnaryExpression expr) {
		processExpression(expr.getExpr());
	}

	@Override
	protected void visit(final StructConstructor expr) {
		for (final Expression fieldExpr : expr.getFieldValues()) {
			processExpression(fieldExpr);
		}
	}

	@Override
	protected void visit(final StructAccessExpression expr) {
		processExpression(expr.getStruct());
	}

	@Override
	protected void visit(final QuantifierExpression expr) {

		for (final VarList varList : expr.getParameters()) {
			for (final String id : varList.getIdentifiers()) {

				final Set<String> res = mStatementVariablesMap.getOrDefault(mCurrentStatement, new HashSet<>());

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

		final Set<String> res = mStatementVariablesMap.getOrDefault(mCurrentStatement, new HashSet<>());

		res.add(expr.getIdentifier());
		mStatementVariablesMap.put(mCurrentStatement, res);
	}

	@Override
	protected void visit(final FunctionApplication expr) {

		for (final Expression arg : expr.getArguments()) {
			processExpression(arg);
		}
	}

	@Override
	protected void visit(final BinaryExpression expr) {
		processExpression(expr.getLeft());
		processExpression(expr.getRight());
	}

	@Override
	protected void visit(final ArrayAccessExpression expr) {

		processExpression(expr.getArray());

		for (final Expression index : expr.getIndices()) {
			processExpression(index);
		}
	}

	@Override
	protected void visit(final BitVectorAccessExpression expr) {
		processExpression(expr.getBitvec());
	}
}