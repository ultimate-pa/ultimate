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
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.IAnnotationProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefStatementAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.util.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RCFGEdgeVisitor;

public class ReachDefRCFGPredecessorGenerator extends RCFGEdgeVisitor {

	private final ILogger mLogger;
	private final IAnnotationProvider<ReachDefStatementAnnotation> mProvider;

	public ReachDefRCFGPredecessorGenerator(IAnnotationProvider<ReachDefStatementAnnotation> provider, ILogger logger) {
		mLogger = logger;
		mProvider = provider;
	}

	private List<ReachDefStatementAnnotation> rtr;

	/**
	 * Returns all preceeding {@link ReachDefStatementAnnotation}s
	 * 
	 * @param e
	 * @return
	 */
	public List<ReachDefStatementAnnotation> process(IcfgLocation currentNode) {
		rtr = new ArrayList<ReachDefStatementAnnotation>();
		if (currentNode == null) {
			return rtr;
		}

		for (final IcfgEdge pre : currentNode.getIncomingEdges()) {
			visit(pre);
		}

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Predecessors: "
					+ Util.prettyPrintIterable(currentNode.getIncomingEdges(), Util.<IcfgEdge> createHashCodePrinter()));
		}

		return rtr;
	}

	@Override
	protected void visit(SequentialComposition c) {
		final List<CodeBlock> blck = c.getCodeBlocks();
		if (blck == null || blck.isEmpty()) {
			return;
		}
		super.visit(blck.get(blck.size() - 1));
	}

	@Override
	protected void visit(StatementSequence stmtSeq) {
		final ReachDefStatementAnnotation annot = mProvider.getAnnotation(stmtSeq.getStatements().get(
				stmtSeq.getStatements().size() - 1));
		if (annot != null) {
			rtr.add(annot);
		}

		super.visit(stmtSeq);
	}
}
