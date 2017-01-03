/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ReachingDefinitions plug-in.
 * 
 * The ULTIMATE ReachingDefinitions plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ReachingDefinitions plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ReachingDefinitions plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ReachingDefinitions plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE ReachingDefinitions plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.trace;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.IAnnotationProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefEdgeAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefStatementAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie.ReachDefBoogieAnnotator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie.ScopedBoogieVarBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.util.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RCFGEdgeVisitor;

/**
 * @author dietsch
 * 
 */
public class ReachDefTraceVisitor extends RCFGEdgeVisitor {

	private final ILogger mLogger;
	private final CodeBlock mPredecessor;
	private final IAnnotationProvider<ReachDefStatementAnnotation> mStatementProvider;
	private final IAnnotationProvider<ReachDefEdgeAnnotation> mEdgeProvider;
	private final ScopedBoogieVarBuilder mBuilder;
	private final int mKey;

	public ReachDefTraceVisitor(IAnnotationProvider<ReachDefStatementAnnotation> stmtProvider,
			IAnnotationProvider<ReachDefEdgeAnnotation> edgeProvider, CodeBlock predecessor, ILogger logger,
			ScopedBoogieVarBuilder builder, int index) {
		mLogger = logger;
		mPredecessor = predecessor;
		mStatementProvider = stmtProvider;
		mEdgeProvider = edgeProvider;
		mBuilder = builder;
		mKey = index;
	}

	public void process(CodeBlock current) {
		final String key = String.valueOf(mKey);
		ReachDefEdgeAnnotation annot = mEdgeProvider.getAnnotation(current, key);
		if (annot == null) {
			annot = new ReachDefEdgeAnnotation(current, mStatementProvider, key);
			mEdgeProvider.annotate(current, annot, key);
		}
		visit(current);
	}

	@Override
	protected void visit(SequentialComposition c) {
		final List<Statement> stmts = new ArrayList<>();
		for (final CodeBlock cb : c.getCodeBlocks()) {
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

	private void processEdge(CodeBlock edge, List<Statement> stmts) {
		final String key = String.valueOf(mKey);
		for (final Statement stmt : stmts) {
			ReachDefStatementAnnotation annot = mStatementProvider.getAnnotation(stmt, key);
			if (annot == null) {
				annot = new ReachDefStatementAnnotation();
				mStatementProvider.annotate(stmt, annot, key);
			}
			final ReachDefBoogieAnnotator generator = createBoogieAnnotator(stmts, stmt, annot);
			try {
				generator.annotate(stmt, edge.getTransformula());
				if (mLogger.isDebugEnabled()) {
					final String pre = "            " + edge.hashCode() + " " + BoogiePrettyPrinter.print(stmt);
					mLogger.debug(pre + Util.repeat((40 - pre.length()), " ") + " New Use: " + annot.getUseAsString());
					mLogger.debug(pre + Util.repeat((40 - pre.length()), " ") + " New Def: " + annot.getDefAsString());
				}
			} catch (final Throwable e) {
				// Fail fast after fatal error
				mLogger.fatal("Fatal error occured", e);
				return;
			}
		}
	}

	private ReachDefBoogieAnnotator createBoogieAnnotator(List<Statement> stmts, Statement currentStmt,
			ReachDefStatementAnnotation stmtAnnotation) {

		Collection<ReachDefStatementAnnotation> predecessors;

		final int currentIndex = stmts.indexOf(currentStmt);
		predecessors = new ArrayList<>();

		if (currentIndex != 0) {
			// its not the first statement, so we only need the straight line
			// predecessor
			final String key = String.valueOf(mKey);
			final ReachDefStatementAnnotation annot = mStatementProvider.getAnnotation(
					stmts.get(currentIndex - 1), key);
			predecessors.add(annot);
		} else if (mPredecessor != null) {
			// it is the first statement, we only need one predecessor
			// from the trace and only if this is not the first codeblock
			final String key = String.valueOf(mKey - 1);
			final ReachDefTracePredecessorGenerator generator = new ReachDefTracePredecessorGenerator(mStatementProvider, key);
			predecessors = generator.process(mPredecessor);
		}

		assert predecessors.size() < 2;

		return new ReachDefBoogieAnnotator(predecessors, stmtAnnotation, mLogger, mBuilder, String.valueOf(mKey));
	}

}
