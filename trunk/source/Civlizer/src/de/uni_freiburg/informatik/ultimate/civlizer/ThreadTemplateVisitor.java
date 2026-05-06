package de.uni_freiburg.informatik.ultimate.civlizer;

import java.util.Collections;
import java.util.Arrays;
import java.util.Map;
import java.util.List;
import java.util.HashMap;
import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AtomicStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BreakStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ForkStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieVisitor;

final class ThreadTemplateVisitor extends BoogieVisitor {

	private HashMap<String, List<Tid>> mMap;

	private ThreadTemplateVisitor() {
		mMap = new HashMap<>();
	}

	static Map<String, List<Tid>> getMapToTid(Unit boogieFile) {
		ThreadTemplateVisitor visitor = new ThreadTemplateVisitor();

		for (Declaration elem : boogieFile.getDeclarations()) {
			visitor.processDeclaration(elem);
        }

		return visitor.mMap;
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
		if (decl.getIdentifier() != "ULTIMATE.start" && !mMap.containsKey(decl.getIdentifier())) {
			mMap.put(decl.getIdentifier(), new ArrayList<>());
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

		Tid result = new Tid(statement.getThreadID());
		List<Tid> tids = mMap.get(statement.getProcedureName());

		if (tids == null) {
			mMap.put(
				statement.getProcedureName(),
				new ArrayList<>(Collections.singletonList(result))
			);
		}
		else {
			tids.add(result);
		}
	}
}