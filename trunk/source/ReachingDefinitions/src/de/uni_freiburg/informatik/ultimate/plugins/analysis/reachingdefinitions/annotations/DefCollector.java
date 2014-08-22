package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie.ScopedBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RCFGEdgeVisitor;

class DefCollector extends RCFGEdgeVisitor {

	private HashMap<ScopedBoogieVar, HashSet<Statement>> mDefs;
	private final IAnnotationProvider<ReachDefStatementAnnotation> mAnnotationProvider;

	DefCollector(IAnnotationProvider<ReachDefStatementAnnotation> provider) {
		mAnnotationProvider = provider;
	}

	HashMap<ScopedBoogieVar, HashSet<Statement>> collect(RCFGEdge edge) {
		if (mDefs == null) {
			mDefs = new HashMap<>();
			visit(edge);
		}
		return mDefs;
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

		ReachDefBaseAnnotation annot = mAnnotationProvider.getAnnotation(stmts.get(stmts.size() - 1));
		if (annot != null) {
			mDefs = annot.getDefs();
		}
	}

}
