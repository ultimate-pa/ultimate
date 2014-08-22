package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.dataflowdag;

import java.util.LinkedHashMap;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.BaseObserver;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.IAnnotationProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefEdgeAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefStatementAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

public class DataflowDAGGenerator extends BaseObserver {

	private final Logger mLogger;
	private final IAnnotationProvider<ReachDefStatementAnnotation> mStatementProvider;
	private final IAnnotationProvider<ReachDefEdgeAnnotation> mEdgeProvider;
	private final LinkedHashMap<RCFGEdge, List<AssumeStatement>> mEdgesWithAssumes;

	public DataflowDAGGenerator(Logger logger, IAnnotationProvider<ReachDefStatementAnnotation> stmtProvider,
			IAnnotationProvider<ReachDefEdgeAnnotation> edgeProvider,
			LinkedHashMap<RCFGEdge, List<AssumeStatement>> edgesWithAssumes) {
		mLogger = logger;
		mStatementProvider = stmtProvider;
		mEdgeProvider = edgeProvider;
		mEdgesWithAssumes = edgesWithAssumes;
	}

	@Override
	public boolean process(IElement root) throws Throwable {
		if (root instanceof RootNode) {
			RootNode rootNode = (RootNode) root;
			process(rootNode);

			if (mLogger.isDebugEnabled()) {
				mLogger.debug("DataflowDAGGenerator results:");
			}
		}
		return false;
	}

	private void process(RootNode node) {

		for (RCFGEdge edge : mEdgesWithAssumes.keySet()) {
			for (AssumeStatement assm : mEdgesWithAssumes.get(edge)) {
				buildDAG(edge,assm);
			}
		}

	}

	private void buildDAG(RCFGEdge edge, AssumeStatement assm) {
		ReachDefStatementAnnotation annot = mStatementProvider.getAnnotation(assm);
		assert annot != null;
		
		DataflowDAG current = new DataflowDAG(assm);
		
		annot.getDefs();
		
	}

}
