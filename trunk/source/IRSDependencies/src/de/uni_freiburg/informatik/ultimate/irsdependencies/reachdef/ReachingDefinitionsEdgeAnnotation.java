package de.uni_freiburg.informatik.ultimate.irsdependencies.reachdef;

import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.irsdependencies.rcfg.visitors.RCFGEdgeVisitor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;

public class ReachingDefinitionsEdgeAnnotation extends ReachingDefinitionsBaseAnnotation {

	private static final long serialVersionUID = 1L;

	private RCFGEdge mEdge;

	public ReachingDefinitionsEdgeAnnotation(RCFGEdge e) {
		mEdge = e;
	}

	@Override
	protected HashMap<String, HashSet<Statement>> getDefs() {
		if (mEdge == null) {
			return new HashMap<>();
		}
		Collector c = new Collector();
		c.collect();
		return c.mDefs;
	}

	@Override
	protected HashMap<String, HashSet<Statement>> getUse() {
		if (mEdge == null) {
			return new HashMap<>();
		}
		Collector c = new Collector();
		c.collect();
		return c.mUse;
	}

	private class Collector extends RCFGEdgeVisitor {

		private HashMap<String, HashSet<Statement>> mDefs;
		private HashMap<String, HashSet<Statement>> mUse;

		private void collect() {
			mDefs = new HashMap<>();
			mUse = new HashMap<>();
			visit(mEdge);
		}

		@Override
		protected void visit(StatementSequence c) {
			super.visit(c);
			
			//TODO: Do it faster, it is always the last (afaik) 
			
			for (Statement stmt : c.getStatements()) {
				ReachingDefinitionsStatementAnnotation annot = ReachingDefinitionsStatementAnnotation
						.getAnnotation(stmt);
				if (annot != null) {
					mDefs = annot.getDefs();
					mUse = annot.getUse();
				}
			}
		}

	}

}
