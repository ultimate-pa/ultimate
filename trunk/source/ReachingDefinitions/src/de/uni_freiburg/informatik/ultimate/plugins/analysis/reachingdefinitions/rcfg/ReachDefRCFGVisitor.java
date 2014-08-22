package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.rcfg;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogieStatementPrettyPrinter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.IAnnotationProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefEdgeAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefStatementAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie.ReachDefBoogieAnnotator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie.ScopedBoogieVarBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.util.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RCFGEdgeVisitor;

/**
 * ReachDefRCFGVisitor handles the different types of the RCFG and annotates
 * meta-annotations ({@link ReachDefEdgeAnnotation}) to edges.
 * 
 * It also delegates calls to the actual ReachingDefinition algorithm
 * 
 * @author dietsch
 * 
 */
public class ReachDefRCFGVisitor extends RCFGEdgeVisitor {

	private boolean mFixpointReached;
	private RCFGNode mCurrentSourceNode;
	private final Logger mLogger;
	private final IAnnotationProvider<ReachDefEdgeAnnotation> mEdgeProvider;
	private final IAnnotationProvider<ReachDefStatementAnnotation> mStatementProvider;
	private final ScopedBoogieVarBuilder mBuilderTable;

	public ReachDefRCFGVisitor(IAnnotationProvider<ReachDefEdgeAnnotation> provider,
			IAnnotationProvider<ReachDefStatementAnnotation> stmtProvider, Logger logger, ScopedBoogieVarBuilder builder) {
		mLogger = logger;
		mEdgeProvider = provider;
		mStatementProvider = stmtProvider;
		mBuilderTable = builder;
	}

	/**
	 * 
	 * @param e
	 * @return true iff a fixpoint was reached
	 */
	public boolean process(RCFGEdge e) {
		mFixpointReached = true;
		visit(e);
		return mFixpointReached;
	}

	@Override
	protected void visit(RootEdge e) {
		// root edges are never on a cycle, and we want to expand the
		// following edges
		mFixpointReached = false;
		super.visit(e);
	}

	@Override
	protected void visit(CodeBlock c) {
		ReachDefEdgeAnnotation annot = mEdgeProvider.getAnnotation(c);
		if (annot == null) {
			annot = new ReachDefEdgeAnnotation(c, mStatementProvider);
			mEdgeProvider.annotate(c, annot);
		}
		super.visit(c);
	}

	@Override
	protected void visit(StatementSequence edge) {
		boolean somethingChanged = false;

		if (edge.getSource() != null) {
			mCurrentSourceNode = edge.getSource();
		}

		for (Statement s : edge.getStatements()) {
			ReachDefStatementAnnotation annot = mStatementProvider.getAnnotation(s);
			if (annot == null) {
				annot = new ReachDefStatementAnnotation();
				mStatementProvider.annotate(s, annot);
				// if we need a new annotation it is definitely not a
				// fixpoint
				somethingChanged = true;
			}
			ReachDefBoogieAnnotator generator = createBoogieAnnotator(edge, s, annot);
			try {
				boolean gen = generator.annotate(s);
				if (mLogger.isDebugEnabled()) {
					String pre = "            " + edge.hashCode() + " " + BoogieStatementPrettyPrinter.print(s);
					mLogger.debug(pre + Util.repeat((40 - pre.length()), " ") + " New Use: " + annot.getUseAsString());
					mLogger.debug(pre + Util.repeat((40 - pre.length()), " ") + " New Def: " + annot.getDefAsString());
				}

				somethingChanged = gen || somethingChanged;
			} catch (Throwable e) {
				// Fail fast after fatal error
				mLogger.fatal("Fatal error occured", e);
				mFixpointReached = true;
				return;
			}
		}

		mFixpointReached = !somethingChanged && mFixpointReached;

		super.visit(edge);
	}

	@Override
	protected void visit(SequentialComposition c) {
		mCurrentSourceNode = c.getSource();
		super.visit(c);
	}

	/**
	 * 
	 * @param currentSeq
	 *            The statement sequence we currently process
	 * @param currentStmt
	 *            The statement of the sequence we currently process
	 * @param stmtAnnotation
	 *            The {@link ReachDefStatementAnnotation} annotation of
	 *            currentStmt
	 * @return A generator that considers (a) where we are in the statement
	 *         sequence and (b) loops and stuff.
	 */
	private ReachDefBoogieAnnotator createBoogieAnnotator(StatementSequence currentSeq, Statement currentStmt,
			ReachDefStatementAnnotation stmtAnnotation) {

		Collection<ReachDefStatementAnnotation> predecessors;

		int currentIndex = currentSeq.getStatements().indexOf(currentStmt);
		if (currentIndex != 0) {
			// its not the first statement, so we only need the straight line
			// predecessor
			predecessors = new ArrayList<>();
			predecessors.add((ReachDefStatementAnnotation) mStatementProvider.getAnnotation(currentSeq.getStatements()
					.get(currentIndex - 1)));
		} else {
			// it is the first statement, we only need loop predecessors
			// as statements may be duplicated, we build a map from rcfgedge to
			// predecessors which we update

			if (mCurrentSourceNode != null) {
				if (mPreMap == null) {
					mPreMap = new HashMap<>();
				}

				HashSet<ReachDefStatementAnnotation> pres = mPreMap.get(currentSeq);
				if (pres == null) {
					pres = new HashSet<>();
					mPreMap.put(currentSeq, pres);
				}

				pres.addAll(new ReachDefRCFGPredecessorGenerator(mStatementProvider, mLogger)
						.process(mCurrentSourceNode));
				predecessors = pres;
			} else {
				predecessors = new ArrayList<>();
			}

		}

		return new ReachDefBoogieAnnotator(predecessors, stmtAnnotation, mStatementProvider, mLogger, mBuilderTable);
	}

	private HashMap<RCFGEdge, HashSet<ReachDefStatementAnnotation>> mPreMap;

}