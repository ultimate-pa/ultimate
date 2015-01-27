package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie.ScopedBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RCFGEdgeVisitor;

class UseCollector extends RCFGEdgeVisitor {
	private HashMap<ScopedBoogieVar, HashSet<IndexedStatement>> mUse;
	private final IAnnotationProvider<ReachDefStatementAnnotation> mAnnotationProvider;
	private final String mKey;

	UseCollector(IAnnotationProvider<ReachDefStatementAnnotation> provider, String key) {
		mAnnotationProvider = provider;
		mKey = key;
	}

	HashMap<ScopedBoogieVar, HashSet<IndexedStatement>> collect(RCFGEdge edge) {
		if (mUse == null) {
			mUse = new HashMap<>();
			visit(edge);
		}
		return mUse;
	}

	@Override
	protected void visit(StatementSequence c) {
		super.visit(c);

		List<Statement> stmts = c.getStatements();

		if (stmts == null || stmts.size() == 0) {
			return;
		}

		for (Statement stmt : stmts) {
			ReachDefBaseAnnotation annot = getAnnotation(stmt);
			if (annot != null) {
				unionUse(annot);
			}
		}
	}

	private ReachDefBaseAnnotation getAnnotation(Statement stmt) {
		if (mKey == null) {
			return mAnnotationProvider.getAnnotation(stmt);
		} else {
			return mAnnotationProvider.getAnnotation(stmt, mKey);
		}
	}

	private void unionUse(ReachDefBaseAnnotation other) {
		if (other == null) {
			return;
		}

		HashMap<ScopedBoogieVar, HashSet<IndexedStatement>> otheruse = other.getUse();

		if (otheruse == null || otheruse == mUse) {
			return;
		}

		for (ScopedBoogieVar key : otheruse.keySet()) {
			for (IndexedStatement stmt : otheruse.get(key)) {
				addUse(key, stmt.getStatement(), stmt.getKey());
			}
		}

	}

	private void addUse(ScopedBoogieVar variable, Statement stmt, String key) {
		HashSet<IndexedStatement> rtr = mUse.get(variable);
		if (rtr == null) {
			rtr = new HashSet<>();
			mUse.put(variable, rtr);

		}
		rtr.add(new IndexedStatement(stmt, key));
	}
}
