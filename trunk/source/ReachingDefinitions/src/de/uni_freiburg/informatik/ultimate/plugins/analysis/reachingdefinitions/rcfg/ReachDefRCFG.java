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

import java.util.LinkedHashSet;

import de.uni_freiburg.informatik.ultimate.boogie.preprocessor.PreprocessorAnnotation;
import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.IAnnotationProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefEdgeAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefStatementAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie.ScopedBoogieVarBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.util.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;

/**
 * 
 * {@link ReachDefRCFG} computes a DefUse set that is expressed as
 * {@link ReachDefStatementAnnotation} annotation for each edge of an RCFG.
 * 
 * It makes the following assumptions:
 * <ul>
 * <li>A
 * </ul>
 * 
 * @author dietsch
 * 
 */
public class ReachDefRCFG extends BaseObserver {

	private final ILogger mLogger;
	private final IAnnotationProvider<ReachDefStatementAnnotation> mStatementProvider;
	private final IAnnotationProvider<ReachDefEdgeAnnotation> mEdgeProvider;

	public ReachDefRCFG(final ILogger logger, final IAnnotationProvider<ReachDefStatementAnnotation> stmtProvider,
			final IAnnotationProvider<ReachDefEdgeAnnotation> edgeProvider) {
		mLogger = logger;
		mStatementProvider = stmtProvider;
		mEdgeProvider = edgeProvider;
	}

	@Override
	public boolean process(final IElement root) throws Throwable {
		if (root instanceof BoogieIcfgContainer) {
			final BoogieIcfgContainer rootNode = (BoogieIcfgContainer) root;

			if (mLogger.isDebugEnabled()) {
				mLogger.debug("Loops: " + rootNode.getLoopLocations().size());
			}

			process(rootNode);
		}
		return false;
	}

	private void process(final BoogieIcfgContainer node) throws Throwable {

		final PreprocessorAnnotation pa = PreprocessorAnnotation.getAnnotation(node);
		if (pa == null || pa.getSymbolTable() == null) {
			final String errorMsg = "No symbol table found on given RootNode.";
			mLogger.fatal(errorMsg);
			throw new UnsupportedOperationException(errorMsg);
		}
		final ScopedBoogieVarBuilder builder = new ScopedBoogieVarBuilder(pa.getSymbolTable());

		final LinkedHashSet<IcfgEdge> remaining = new LinkedHashSet<>();

		for (final IcfgEdge next : BoogieIcfgContainer.extractStartEdges(node)) {
			remaining.add(next);
		}

		while (!remaining.isEmpty()) {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("");
				mLogger.debug("                    Open: "
						+ Util.prettyPrintIterable(remaining, Util.<IcfgEdge> createHashCodePrinter()));
			}
			final IcfgEdge current = remaining.iterator().next();
			remaining.remove(current);
			final ReachDefRCFGVisitor v = new ReachDefRCFGVisitor(mEdgeProvider, mStatementProvider, mLogger, builder);

			final boolean fxpReached = v.process(current);
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("                    Fixpoint reached: " + fxpReached);
			}
			if (!fxpReached) {
				for (final IcfgEdge next : current.getTarget().getOutgoingEdges()) {
					remaining.add(next);
				}
			}
		}
		
		mLogger.debug("bla");
	}
}
