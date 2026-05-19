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
import de.uni_freiburg.informatik.ultimate.boogie.ast.AtomicStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BreakStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ForkStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.JoinStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;

final class ThreadTemplateVisitor extends BoogieVisitor {

	private String mCurrentProcedure;

	private Map<String, List<Tid>> mAssociationTidMap;
	private Map<String, List<Tid>> mUsedTidMap;
	private Map<String, List<Tid>> mAllTidMap;
	private Set<Tid> mTids;

	ThreadTemplateVisitor(Unit boogieFile) {
		mCurrentProcedure = null;
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

	@Override
	protected Declaration processDeclaration(final Declaration decl) {
		switch (decl) {
			case final Procedure proc -> visit(proc);
			default -> {}
		}
		return decl;
	}

	@Override
	protected void visit(final Procedure decl) {
		mCurrentProcedure = decl.getIdentifier();

		if (!mCurrentProcedure.equals("ULTIMATE.start") && !mAssociationTidMap.containsKey(mCurrentProcedure)) {
			mAssociationTidMap.put(mCurrentProcedure, new ArrayList<>());
		}

		for (Statement stmt : decl.getBody().getBlock()) {
			processStatement(stmt);
		}
	}

	@Override
	protected Statement processStatement(final Statement statement) {
		switch (statement) {
			case final AtomicStatement atomicStmt -> visit(atomicStmt);
			case final BreakStatement breakStmt -> visit(breakStmt); // not allow
			case final CallStatement callStmt -> visit(callStmt); // not allow
			case final ForkStatement forkStmt -> visit(forkStmt);
			case final JoinStatement joinStmt -> visit(joinStmt);
			case final GotoStatement gotoStmt -> visit(gotoStmt); // not allow
			case final IfStatement ifStmt -> visit(ifStmt);
			case final Label label -> visit(label); // not allow
			case final ReturnStatement returnStmt -> visit(returnStmt); // not allow
			case final WhileStatement whileStmt -> visit(whileStmt);
			default -> {}
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
		List<Tid> tids = mAssociationTidMap.get(statement.getProcedureName());

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
}