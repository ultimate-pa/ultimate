package de.uni_freiburg.informatik.ultimate.buchiprogramproduct.optimizeproduct;

import java.util.ArrayList;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ParallelComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RCFGEdgeVisitor;

	public class StatementExtractor extends RCFGEdgeVisitor {

		private final Logger mLogger;
		private List<Statement> mStatements;
		private boolean mHasSummary;

		public StatementExtractor(Logger logger){
			mLogger = logger;
		}
		
		public List<Statement> process(RCFGEdge edge) {
			mStatements = new ArrayList<>();
			mHasSummary = false;
			visit(edge);
			if (mHasSummary) {
				mLogger.debug(edge + " contains summaries, skipping...");
				return new ArrayList<>();
			}
			return mStatements;
		}
		
		public boolean hasSummary(){
			return mHasSummary;
		}

		@Override
		protected void visit(ParallelComposition c) {
			throw new UnsupportedOperationException("Cannot merge ParallelComposition");
		}

		@Override
		protected void visit(StatementSequence c) {
			mStatements.addAll(c.getStatements());
			super.visit(c);
		}

		@Override
		protected void visit(Summary c) {
			mHasSummary = true;
			super.visit(c);
		}
	}
