package de.uni_freiburg.informatik.ultimate.reachingdefinitions.annotations;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RCFGEdgeVisitor;

public class ReachDefEdgeAnnotation extends ReachDefBaseAnnotation {

	private static final long serialVersionUID = 1L;

	private RCFGEdge mEdge;
	private DefCollector mDefCollector;
	private UseCollector mUseCollector;

	public ReachDefEdgeAnnotation(RCFGEdge e) {
		mEdge = e;
	}

	@Override
	protected HashMap<String, HashSet<Statement>> getDefs() {
		if (mEdge == null) {
			return new HashMap<>();
		}

		if (mDefCollector == null) {
			mDefCollector = new DefCollector();
			mDefCollector.collect();
		}

		return mDefCollector.mDefs;
	}

	@Override
	protected HashMap<String, HashSet<Statement>> getUse() {
		if (mEdge == null) {
			return new HashMap<>();
		}
		if (mUseCollector == null) {
			mUseCollector = new UseCollector();
			mUseCollector.collect();
		}

		return mUseCollector.mUse;
	}

	private class DefCollector extends RCFGEdgeVisitor {

		private HashMap<String, HashSet<Statement>> mDefs;

		private void collect() {
			mDefs = new HashMap<>();
			visit(mEdge);
		}

		@Override
		protected void visit(SequentialComposition c) {
			CodeBlock[] blck = c.getCodeBlocks();
			if (blck == null || blck.length == 0) {
				return;
			}
			super.visit(blck[blck.length - 1]);
		}

		@Override
		protected void visit(StatementSequence c) {
			super.visit(c);

			List<Statement> stmts = c.getStatements();

			if (stmts == null || stmts.size() == 0) {
				return;
			}

			ReachDefBaseAnnotation annot = ReachDefStatementAnnotation.getAnnotation(stmts.get(stmts.size() - 1));
			if (annot != null) {
				mDefs = annot.getDefs();
			}
		}

	}

	private class UseCollector extends RCFGEdgeVisitor {

		private HashMap<String, HashSet<Statement>> mUse;

		private void collect() {
			mUse = new HashMap<>();
			visit(mEdge);
		}

		@Override
		protected void visit(StatementSequence c) {
			super.visit(c);

			List<Statement> stmts = c.getStatements();

			if (stmts == null || stmts.size() == 0) {
				return;
			}

			ReachDefBaseAnnotation annot = ReachDefStatementAnnotation.getAnnotation(stmts.get(stmts.size() - 1));
			if (annot != null) {
				unionUse(annot);
			}
		}

		private void unionUse(ReachDefBaseAnnotation other) {
			if (other == null) {
				return;
			}

			HashMap<String, HashSet<Statement>> otheruse = other.getUse();

			if (otheruse == null || otheruse == mUse) {
				return;
			}

			for (String key : otheruse.keySet()) {
				for (Statement stmt : otheruse.get(key)) {
					addUse(key, stmt);
				}
			}

		}

		private void addUse(String variableName, Statement stmt) {
			HashSet<Statement> rtr = mUse.get(variableName);
			if (rtr == null) {
				rtr = new HashSet<>();
				mUse.put(variableName, rtr);

			}
			rtr.add(stmt);
		}

	}

}
