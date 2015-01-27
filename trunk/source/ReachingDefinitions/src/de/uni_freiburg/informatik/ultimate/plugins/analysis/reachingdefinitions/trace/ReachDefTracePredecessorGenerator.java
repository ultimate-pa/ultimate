package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.trace;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.IAnnotationProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefStatementAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ParallelComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RCFGEdgeVisitor;

public class ReachDefTracePredecessorGenerator extends RCFGEdgeVisitor {

	private final IAnnotationProvider<ReachDefStatementAnnotation> mProvider;
	private final String mKey;

	public ReachDefTracePredecessorGenerator(IAnnotationProvider<ReachDefStatementAnnotation> provider) {
		this(provider, null);
	}

	public ReachDefTracePredecessorGenerator(IAnnotationProvider<ReachDefStatementAnnotation> provider, String key) {
		mProvider = provider;
		mKey = key;
	}

	private List<ReachDefStatementAnnotation> rtr;

	/**
	 * Returns all {@link ReachDefStatementAnnotation}s from the predecessor
	 * 
	 * @param e
	 * @return
	 */
	public List<ReachDefStatementAnnotation> process(CodeBlock predecessor) {
		rtr = new ArrayList<ReachDefStatementAnnotation>();
		visit(predecessor);
		return rtr;
	}

	@Override
	protected void visit(SequentialComposition c) {
		CodeBlock[] cb = c.getCodeBlocks();
		if (cb == null || cb.length == 0) {
			return;
		}
		visit(cb[cb.length - 1]);
	}

	@Override
	protected void visit(ParallelComposition c) {
		throw new UnsupportedOperationException("Parallel composition is not supported");
	}

	@Override
	protected void visit(StatementSequence stmtSeq) {
		ReachDefStatementAnnotation annot = getAnnotation(stmtSeq);
		if (annot != null) {
			rtr.add(annot);
		}
		super.visit(stmtSeq);
	}

	private ReachDefStatementAnnotation getAnnotation(StatementSequence stmtSeq) {
		if (mKey == null) {
			return mProvider.getAnnotation(stmtSeq.getStatements().get(stmtSeq.getStatements().size() - 1));
		} else {
			return mProvider.getAnnotation(stmtSeq.getStatements().get(stmtSeq.getStatements().size() - 1), mKey);
		}
	}
}
