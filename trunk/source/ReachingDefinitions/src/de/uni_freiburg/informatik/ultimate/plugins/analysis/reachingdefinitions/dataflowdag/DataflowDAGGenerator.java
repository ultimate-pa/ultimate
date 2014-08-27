package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.dataflowdag;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.BaseObserver;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.IAnnotationProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefEdgeAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefStatementAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie.ScopedBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

public class DataflowDAGGenerator extends BaseObserver {

	private final Logger mLogger;
	private final IAnnotationProvider<ReachDefStatementAnnotation> mStatementProvider;
	private final IAnnotationProvider<ReachDefEdgeAnnotation> mEdgeProvider;
	private final LinkedHashMap<RCFGEdge, List<AssumeStatement>> mEdgesWithAssumes;
	private List<DataflowDAG<Statement>> mForest;

	public DataflowDAGGenerator(Logger logger, IAnnotationProvider<ReachDefStatementAnnotation> stmtProvider,
			IAnnotationProvider<ReachDefEdgeAnnotation> edgeProvider,
			LinkedHashMap<RCFGEdge, List<AssumeStatement>> edgesWithAssumes) {
		mLogger = logger;
		mStatementProvider = stmtProvider;
		mEdgeProvider = edgeProvider;
		mEdgesWithAssumes = edgesWithAssumes;
	}

	// TODO: Nur für traces machen

	@Override
	public boolean process(IElement root) throws Throwable {
		if (mEdgesWithAssumes == null || mEdgesWithAssumes.size() == 0) {
			return false;
		}

		if (root instanceof RootNode) {
			RootNode rootNode = (RootNode) root;
			mForest = process(rootNode);

			if (mLogger.isDebugEnabled()) {
				mLogger.debug("DataflowDAGGenerator results:");
				mLogger.debug("#" + mForest.size() + " trees generated");
				printDebugForest();
			}
		}
		return false;
	}

	public List<DataflowDAG<Statement>> getDAGs() {
		return mForest;
	}

	private List<DataflowDAG<Statement>> process(RootNode node) {
		List<DataflowDAG<Statement>> forest = new ArrayList<DataflowDAG<Statement>>();
		for (RCFGEdge edge : mEdgesWithAssumes.keySet()) {
			for (AssumeStatement assm : mEdgesWithAssumes.get(edge)) {
				forest.add(buildDAG(edge, assm));
			}
		}
		return forest;
	}

	private DataflowDAG<Statement> buildDAG(RCFGEdge edge, AssumeStatement assm) {
		LinkedList<DataflowDAG<Statement>> store = new LinkedList<>();

		DataflowDAG<Statement> current = new DataflowDAG<Statement>(assm);
		DataflowDAG<Statement> root = current;
		store.add(current);

		while (!store.isEmpty()) {
			current = store.removeFirst();
			Set<Entry<ScopedBoogieVar, HashSet<Statement>>> uses = getUse(current);
			for (Entry<ScopedBoogieVar, HashSet<Statement>> use : uses) {
				for (Statement stmt : use.getValue()) {
					DataflowDAG<Statement> next = new DataflowDAG<Statement>(stmt);
					current.addOutgoingNode(next, use.getKey());
					store.addFirst(next); // use last for BFS
				}
			}
		}
		return root;

	}

	private Set<Entry<ScopedBoogieVar, HashSet<Statement>>> getUse(DataflowDAG<Statement> current) {
		ReachDefStatementAnnotation annot = mStatementProvider.getAnnotation(current.getNodeLabel());
		assert annot != null;
		HashMap<ScopedBoogieVar, HashSet<Statement>> use = annot.getUse();
		assert use != null;
		return use.entrySet();
	}

	private void printDebugForest() {
		if (mForest == null) {
			return;
		}

		for (DataflowDAG<Statement> dag : mForest) {
			dag.printGraphDebug(mLogger);
		}
	}

}
