package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.rcfg;

import java.util.LinkedHashSet;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.BaseObserver;
import de.uni_freiburg.informatik.ultimate.boogie.type.PreprocessorAnnotation;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.IAnnotationProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefEdgeAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefStatementAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie.ScopedBoogieVarBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.util.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

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

	private final Logger mLogger;
	private final IAnnotationProvider<ReachDefStatementAnnotation> mStatementProvider;
	private final IAnnotationProvider<ReachDefEdgeAnnotation> mEdgeProvider;

	public ReachDefRCFG(Logger logger, IAnnotationProvider<ReachDefStatementAnnotation> stmtProvider,
			IAnnotationProvider<ReachDefEdgeAnnotation> edgeProvider) {
		mLogger = logger;
		mStatementProvider = stmtProvider;
		mEdgeProvider = edgeProvider;
	}

	@Override
	public boolean process(IElement root) throws Throwable {
		if (root instanceof RootNode) {
			RootNode rootNode = (RootNode) root;

			if (mLogger.isDebugEnabled()) {
				mLogger.debug("Loops: " + rootNode.getRootAnnot().getLoopLocations().size());
			}

			process(rootNode);
		}
		return false;
	}

	private void process(RootNode node) throws Throwable {

		PreprocessorAnnotation pa = PreprocessorAnnotation.getAnnotation(node);
		if (pa == null || pa.getSymbolTable() == null) {
			String errorMsg = "No symbol table found on given RootNode.";
			mLogger.fatal(errorMsg);
			throw new UnsupportedOperationException(errorMsg);
		}
		ScopedBoogieVarBuilder builder = new ScopedBoogieVarBuilder(pa.getSymbolTable());

		LinkedHashSet<RCFGEdge> remaining = new LinkedHashSet<>();

		for (RCFGEdge next : node.getOutgoingEdges()) {
			remaining.add(next);
		}

		while (!remaining.isEmpty()) {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("");
				mLogger.debug("                    Open: "
						+ Util.prettyPrintIterable(remaining, Util.<RCFGEdge> createHashCodePrinter()));
			}
			RCFGEdge current = remaining.iterator().next();
			remaining.remove(current);
			ReachDefRCFGVisitor v = new ReachDefRCFGVisitor(mEdgeProvider, mStatementProvider, mLogger, builder);

			boolean fxpReached = v.process(current);
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("                    Fixpoint reached: " + fxpReached);
			}
			if (!fxpReached) {
				for (RCFGEdge next : current.getTarget().getOutgoingEdges()) {
					remaining.add(next);
				}
			}
		}
		
		mLogger.debug("bla");
	}
}
