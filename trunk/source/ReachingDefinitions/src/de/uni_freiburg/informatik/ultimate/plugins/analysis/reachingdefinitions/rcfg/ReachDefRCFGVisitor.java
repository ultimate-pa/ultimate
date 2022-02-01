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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.rcfg;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.IAnnotationProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefEdgeAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefStatementAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie.ReachDefBoogieAnnotator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie.ScopedBoogieVarBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.util.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
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
	private IcfgLocation mCurrentSourceNode;
	private final ILogger mLogger;
	private final IAnnotationProvider<ReachDefEdgeAnnotation> mEdgeProvider;
	private final IAnnotationProvider<ReachDefStatementAnnotation> mStatementProvider;
	private final ScopedBoogieVarBuilder mVarBuilder;

	public ReachDefRCFGVisitor(IAnnotationProvider<ReachDefEdgeAnnotation> provider,
			IAnnotationProvider<ReachDefStatementAnnotation> stmtProvider, ILogger logger, ScopedBoogieVarBuilder builder) {
		mLogger = logger;
		mEdgeProvider = provider;
		mStatementProvider = stmtProvider;
		mVarBuilder = builder;
	}

	/**
	 * 
	 * @param e
	 * @return true iff a fixpoint was reached
	 */
	public boolean process(IcfgEdge e) {
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

		for (final Statement s : edge.getStatements()) {
			ReachDefStatementAnnotation annot = mStatementProvider.getAnnotation(s);
			if (annot == null) {
				annot = new ReachDefStatementAnnotation();
				mStatementProvider.annotate(s, annot);
				// if we need a new annotation it is definitely not a
				// fixpoint
				somethingChanged = true;
			}
			final ReachDefBoogieAnnotator generator = createBoogieAnnotator(edge, s, annot);
			try {
				final boolean gen = generator.annotate(s,edge.getTransformula());
				if (mLogger.isDebugEnabled()) {
					final String pre = "            " + edge.hashCode() + " " + BoogiePrettyPrinter.print(s);
					mLogger.debug(pre + Util.repeat((40 - pre.length()), " ") + " New Use: " + annot.getUseAsString());
					mLogger.debug(pre + Util.repeat((40 - pre.length()), " ") + " New Def: " + annot.getDefAsString());
				}

				somethingChanged = gen || somethingChanged;
			} catch (final Throwable e) {
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

		final int currentIndex = currentSeq.getStatements().indexOf(currentStmt);
		if (currentIndex != 0) {
			// its not the first statement, so we only need the straight line
			// predecessor
			predecessors = new ArrayList<>();
			predecessors.add(mStatementProvider.getAnnotation(currentSeq.getStatements()
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

		return new ReachDefBoogieAnnotator(predecessors, stmtAnnotation, mLogger, mVarBuilder);
	}

	private HashMap<IcfgEdge, HashSet<ReachDefStatementAnnotation>> mPreMap;

}
