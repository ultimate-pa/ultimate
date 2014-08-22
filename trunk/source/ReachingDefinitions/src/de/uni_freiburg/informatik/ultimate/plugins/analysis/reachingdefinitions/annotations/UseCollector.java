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
	private HashMap<ScopedBoogieVar, HashSet<Statement>> mUse;
	private final IAnnotationProvider<ReachDefStatementAnnotation> mAnnotationProvider;

	UseCollector(IAnnotationProvider<ReachDefStatementAnnotation> provider) {
		mAnnotationProvider = provider;
	}

	HashMap<ScopedBoogieVar, HashSet<Statement>> collect(RCFGEdge edge) {
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

		for(Statement stmt : stmts){
			ReachDefBaseAnnotation annot = mAnnotationProvider.getAnnotation(stmt);
			if (annot != null) {
				unionUse(annot);
			}
		}
	}

	private void unionUse(ReachDefBaseAnnotation other) {
		if (other == null) {
			return;
		}

		HashMap<ScopedBoogieVar, HashSet<Statement>> otheruse = other.getUse();

		if (otheruse == null || otheruse == mUse) {
			return;
		}

		for (ScopedBoogieVar key : otheruse.keySet()) {
			for (Statement stmt : otheruse.get(key)) {
				addUse(key, stmt);
			}
		}

	}

	private void addUse(ScopedBoogieVar variable, Statement stmt) {
		HashSet<Statement> rtr = mUse.get(variable);
		if (rtr == null) {
			rtr = new HashSet<>();
			mUse.put(variable, rtr);

		}
		rtr.add(stmt);
	}
}
