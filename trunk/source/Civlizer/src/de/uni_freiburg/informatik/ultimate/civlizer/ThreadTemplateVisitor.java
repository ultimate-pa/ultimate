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

import de.uni_freiburg.informatik.ultimate.boogie.BoogieUtils;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AtomicStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ForkStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.JoinStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
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

	private final Set<String> mGlobalVariables = new HashSet<>();
	private final Map<ILocation, Set<String>> mStatementVariablesMap = new HashMap<>();
	private final Map<ILocation, Set<String>> mStatementParametersMap = new HashMap<>();
	private final Map<String, Map<String, ASTType>> mProcedureVariablesMap = new HashMap<>();

	private final Map<String, Expression> mEntryAnnotationMap = new HashMap<>();
	private final Map<String, Expression> mExitAnnotationMap = new HashMap<>();

	private final Map<String, List<Tid>> mAssociationTidMap = new HashMap<>();
	private final Map<String, List<Tid>> mUsedTidMap = new HashMap<>();
	private final Map<String, List<Tid>> mAllTidMap = new HashMap<>();
	private final Set<Tid> mTids;

	ThreadTemplateVisitor(final Unit boogieFile, final BoogieIcfgContainer icfg) {
		mIcfg = icfg;
		mCurrentProcedure = null;
		mCurrentStatement = null;

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

	// TODO instead of collecting global variables, check the type of variables
	boolean containsGlobalVariables(final Statement stmt) {
		if (mStatementVariablesMap.get(stmt.getLoc()) == null || mGlobalVariables == null) {
			return false;
		}

		return !Collections.disjoint(mStatementVariablesMap.get(stmt.getLoc()), mGlobalVariables);
	}

	// TODO instead of collecting the local variables of each procedure, inspect the variables
	//
	// TODO beyond just a boolean, it might be useful to know WHICH local vars are READ and which are ASSIGNED
	// TODO but this is probably already implemented somewhere in Ultimate (?)
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
				// TODO doesn't this also catch local variable declarations?
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

		final Map<String, ASTType> res = new HashMap<>();

		for (final VariableDeclaration varDecl : decl.getBody().getLocalVars()) {
			for (final VarList varList : varDecl.getVariables()) {
				for (final String id : varList.getIdentifiers()) {
					res.put(id, varList.getType());
				}
			}
		}

		mProcedureVariablesMap.put(mCurrentProcedure, res);

		if (!mCurrentProcedure.equals(BoogieUtils.START_PROCEDURE)
				&& !mAssociationTidMap.containsKey(mCurrentProcedure)) {
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
		return super.processStatement(statement);
	}

	@Override
	protected void visit(final AtomicStatement statement) {
		for (final Statement stmt : statement.getBody()) {
			processStatement(stmt);

			mStatementVariablesMap.computeIfAbsent(statement.getLoc(), x -> new HashSet<>())
					.addAll(mStatementVariablesMap.getOrDefault(stmt.getLoc(), new HashSet<>()));
		}
	}

	@Override
	protected void visit(final ForkStatement statement) {
		final Tid tid = new Tid(statement.getThreadID());

		List<Tid> tids = mAssociationTidMap.computeIfAbsent(statement.getProcedureName(), x -> new ArrayList<>());
		if (!tids.contains(tid)) {
			tids.add(tid);
		}

		tids = mUsedTidMap.computeIfAbsent(mCurrentProcedure, x -> new ArrayList<>());
		if (!tids.contains(tid)) {
			tids.add(tid);
		}
	}

	@Override
	protected void visit(final JoinStatement statement) {
		final Tid tid = new Tid(statement.getThreadID());

		final List<Tid> tids = mUsedTidMap.computeIfAbsent(mCurrentProcedure, x -> new ArrayList<>());
		if (!tids.contains(tid)) {
			tids.add(tid);
		}
	}

	@Override
	protected void visit(final HavocStatement statement) {
		for (final VariableLHS var : statement.getIdentifiers()) {
			mStatementVariablesMap.computeIfAbsent(mCurrentStatement, x -> new HashSet<>()).add(var.getIdentifier());
		}
	}

	@Override
	protected void visit(final VariableLHS lhs) {
		mStatementVariablesMap.computeIfAbsent(mCurrentStatement, x -> new HashSet<>()).add(lhs.getIdentifier());
	}

	@Override
	protected void visit(final QuantifierExpression expr) {
		for (final VarList varList : expr.getParameters()) {
			Collections.addAll(mStatementVariablesMap.computeIfAbsent(mCurrentStatement, x -> new HashSet<>()),
					varList.getIdentifiers());
		}

		processExpression(expr.getSubformula());
	}

	@Override
	protected void visit(final IdentifierExpression expr) {
		mStatementVariablesMap.computeIfAbsent(mCurrentStatement, x -> new HashSet<>()).add(expr.getIdentifier());
	}
}
