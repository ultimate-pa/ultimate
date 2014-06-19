package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util;

import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ParallelComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CfgBuilder.GotoEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

public class RCFGEdgeVisitor {

	protected void visit(RCFGEdge e) {
		if (e instanceof CodeBlock) {
			visit((CodeBlock) e);
		} else if (e instanceof RootEdge) {
			visit((RootEdge) e);
		} else {
			throw new UnsupportedOperationException("Extend the new type");
		}
	}

	protected void visit(RootEdge e) {

	}

	protected void visit(CodeBlock c) {
		if (c instanceof Call) {
			visit((Call) c);
		} else if (c instanceof GotoEdge) {
			visit((GotoEdge) c);
		} else if (c instanceof ParallelComposition) {
			visit((ParallelComposition) c);
		} else if (c instanceof Return) {
			visit((Return) c);
		} else if (c instanceof SequentialComposition) {
			visit((SequentialComposition) c);
		} else if (c instanceof Summary) {
			visit((Summary) c);
		} else if (c instanceof StatementSequence) {
			visit((StatementSequence) c);
		} else {
			throw new UnsupportedOperationException("Extend the new type");
		}
	}

	protected void visit(Call c) {
	}

	protected void visit(GotoEdge c) {
	}

	protected void visit(ParallelComposition c) {
	}

	protected void visit(Return c) {

	}

	protected void visit(SequentialComposition c) {
		for(CodeBlock b : c.getCodeBlocks()){
			visit(b);
		}
	}

	protected void visit(Summary c) {

	}

	protected void visit(StatementSequence c) {

	}

}
