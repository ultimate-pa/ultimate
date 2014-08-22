package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.dataflowdag;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.BaseObserver;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogieStatementPrettyPrinter;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RCFGEdgeVisitor;

/**
 * 
 * @author dietsch
 * 
 */
public class AssumeFinder extends BaseObserver {

	private final Logger mLogger;
	private final LinkedHashMap<RCFGEdge, List<AssumeStatement>> mEdgesWithAssumes;

	public AssumeFinder(Logger logger) {
		mLogger = logger;
		mEdgesWithAssumes = new LinkedHashMap<>();
	}

	@Override
	public boolean process(IElement root) throws Throwable {
		if (root instanceof RootNode) {
			RootNode rootNode = (RootNode) root;

			process(rootNode);
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("AssumeFinder result (edge.hashCode(), pretty-printed assume statement):");
				for (RCFGEdge e : mEdgesWithAssumes.keySet()) {
					for (AssumeStatement ass : mEdgesWithAssumes.get(e)) {
						mLogger.debug(e.hashCode() + " " + BoogieStatementPrettyPrinter.print(ass));
					}
				}
			}
		}
		return false;
	}

	public LinkedHashMap<RCFGEdge, List<AssumeStatement>> getEdgesWithAssumes() {
		return mEdgesWithAssumes;
	}

	private void process(RootNode node) {
		Queue<RCFGEdge> openEdges = new LinkedList<>();
		HashSet<RCFGEdge> completed = new HashSet<>();
		AssumeFinderVisitor visitor = new AssumeFinderVisitor();

		openEdges.addAll(node.getOutgoingEdges());

		while (!openEdges.isEmpty()) {
			RCFGEdge current = openEdges.poll();

			visitor.start(current);
			completed.add(current);

			RCFGNode target = current.getTarget();
			if (target == null) {
				mLogger.warn("Empty target for edge " + current.hashCode());
				continue;
			}

			for (RCFGEdge next : target.getOutgoingEdges()) {
				if (!completed.contains(next)) {
					openEdges.add(next);
				}
			}
		}
	}

	private List<AssumeStatement> getAssumeList(RCFGEdge edge) {
		List<AssumeStatement> rtr = mEdgesWithAssumes.get(edge);
		if (rtr == null) {
			rtr = new ArrayList<AssumeStatement>();
			mEdgesWithAssumes.put(edge, rtr);
		}
		return rtr;
	}

	private class AssumeFinderVisitor extends RCFGEdgeVisitor {

		private RCFGEdge mMotherEdge;

		public void start(RCFGEdge edge) {
			mMotherEdge = edge;
			visit(edge);
		}

		@Override
		protected void visit(StatementSequence sequence) {
			super.visit(sequence);
			for (Statement s : sequence.getStatements()) {
				if (s instanceof AssumeStatement) {
					getAssumeList(mMotherEdge).add((AssumeStatement) s);
				}
			}
		}
	}

}
