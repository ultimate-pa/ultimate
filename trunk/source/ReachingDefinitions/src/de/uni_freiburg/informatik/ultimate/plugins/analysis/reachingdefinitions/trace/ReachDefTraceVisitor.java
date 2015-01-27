package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.trace;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.IAnnotationProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefEdgeAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefStatementAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie.ReachDefBoogieAnnotator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie.ScopedBoogieVarBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.util.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RCFGEdgeVisitor;

/**
 * @author dietsch
 * 
 */
public class ReachDefTraceVisitor extends RCFGEdgeVisitor {

	private final Logger mLogger;
	private final CodeBlock mPredecessor;
	private final IAnnotationProvider<ReachDefStatementAnnotation> mStatementProvider;
	private final IAnnotationProvider<ReachDefEdgeAnnotation> mEdgeProvider;
	private final ScopedBoogieVarBuilder mBuilder;
	private final int mKey;

	public ReachDefTraceVisitor(IAnnotationProvider<ReachDefStatementAnnotation> stmtProvider,
			IAnnotationProvider<ReachDefEdgeAnnotation> edgeProvider, CodeBlock predecessor, Logger logger,
			ScopedBoogieVarBuilder builder, int index) {
		mLogger = logger;
		mPredecessor = predecessor;
		mStatementProvider = stmtProvider;
		mEdgeProvider = edgeProvider;
		mBuilder = builder;
		mKey = index;
	}

	public void process(CodeBlock current) {
		String key = String.valueOf(mKey);
		ReachDefEdgeAnnotation annot = mEdgeProvider.getAnnotation(current, key);
		if (annot == null) {
			annot = new ReachDefEdgeAnnotation(current, mStatementProvider, key);
			mEdgeProvider.annotate(current, annot, key);
		}
		visit(current);
	}

	@Override
	protected void visit(SequentialComposition c) {
		List<Statement> stmts = new ArrayList<>();
		for (CodeBlock cb : c.getCodeBlocks()) {
			if (cb instanceof StatementSequence) {
				stmts.addAll(((StatementSequence) cb).getStatements());
			} else {
				throw new UnsupportedOperationException("Cannot unwrap SequentialComposition because I dont know "
						+ cb.getClass().getSimpleName());
			}
		}
		processEdge(c, stmts);
		super.visit(c);
	}

	@Override
	protected void visit(StatementSequence edge) {
		processEdge(edge, edge.getStatements());
		super.visit(edge);
	}

	private void processEdge(RCFGEdge edge, List<Statement> stmts) {
		String key = String.valueOf(mKey);
		for (Statement stmt : stmts) {
			ReachDefStatementAnnotation annot = mStatementProvider.getAnnotation(stmt, key);
			if (annot == null) {
				annot = new ReachDefStatementAnnotation();
				mStatementProvider.annotate(stmt, annot, key);
			}
			ReachDefBoogieAnnotator generator = createBoogieAnnotator(stmts, stmt, annot);
			try {
				generator.annotate(stmt);
				if (mLogger.isDebugEnabled()) {
					String pre = "            " + edge.hashCode() + " " + BoogiePrettyPrinter.print(stmt);
					mLogger.debug(pre + Util.repeat((40 - pre.length()), " ") + " New Use: " + annot.getUseAsString());
					mLogger.debug(pre + Util.repeat((40 - pre.length()), " ") + " New Def: " + annot.getDefAsString());
				}
			} catch (Throwable e) {
				// Fail fast after fatal error
				mLogger.fatal("Fatal error occured", e);
				return;
			}
		}
	}

	private ReachDefBoogieAnnotator createBoogieAnnotator(List<Statement> stmts, Statement currentStmt,
			ReachDefStatementAnnotation stmtAnnotation) {

		Collection<ReachDefStatementAnnotation> predecessors;

		int currentIndex = stmts.indexOf(currentStmt);
		predecessors = new ArrayList<>();

		if (currentIndex != 0) {
			// its not the first statement, so we only need the straight line
			// predecessor
			String key = String.valueOf(mKey);
			ReachDefStatementAnnotation annot = (ReachDefStatementAnnotation) mStatementProvider.getAnnotation(
					stmts.get(currentIndex - 1), key);
			predecessors.add(annot);
		} else if (mPredecessor != null) {
			// it is the first statement, we only need one predecessor
			// from the trace and only if this is not the first codeblock
			String key = String.valueOf(mKey - 1);
			ReachDefTracePredecessorGenerator generator = new ReachDefTracePredecessorGenerator(mStatementProvider, key);
			predecessors = generator.process(mPredecessor);
		}

		assert predecessors.size() < 2;

		return new ReachDefBoogieAnnotator(predecessors, stmtAnnotation, mLogger, mBuilder, String.valueOf(mKey));
	}

}