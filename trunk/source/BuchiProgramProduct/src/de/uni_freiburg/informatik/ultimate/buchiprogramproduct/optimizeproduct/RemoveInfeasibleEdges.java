package de.uni_freiburg.informatik.ultimate.buchiprogramproduct.optimizeproduct;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import org.apache.log4j.Logger;
import de.uni_freiburg.informatik.ultimate.buchiprogramproduct.Activator;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

public class RemoveInfeasibleEdges {

	private final RootNode mResult;
	private final Logger mLogger;

	private int mRemovedEdges;
	private int mRemovedLocations;

	public RemoveInfeasibleEdges(RootNode product, IUltimateServiceProvider services) {
		assert services != null;
		assert product != null;

		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mRemovedEdges = 0;
		mRemovedLocations = 0;
		mResult = process(product);
		mLogger.info("Removed " + mRemovedEdges + " edges and " + mRemovedLocations
				+ " locations because of local infeasibility");
	}

	private RootNode process(RootNode root) {
		ArrayDeque<RCFGEdge> edges = new ArrayDeque<>();
		HashSet<RCFGEdge> closed = new HashSet<>();

		edges.addAll(root.getOutgoingEdges());

		while (!edges.isEmpty()) {
			RCFGEdge current = edges.removeFirst();
			if (closed.contains(current)) {
				continue;
			}
			closed.add(current);
			edges.addAll(current.getTarget().getOutgoingEdges());

			if (current instanceof CodeBlock) {
				checkCodeblock((CodeBlock) current);
			}
		}

		removeDisconnectedLocations(root);

		return root;
	}

	private void checkCodeblock(CodeBlock cb) {
		if (cb instanceof Call || cb instanceof Return) {
			return;
		}

		Infeasibility result = cb.getTransitionFormula().isInfeasible();
		mLogger.debug(result + ": " + cb);

		switch (result) {
		case INFEASIBLE:
			cb.disconnectSource();
			cb.disconnectTarget();
			mRemovedEdges++;
			break;
		case NOT_DETERMINED:
			// TODO: determine it?
			break;
		case UNPROVEABLE:
			// fail fast;
			// TODO: this should be a result!
			break;
		}
	}

	private void removeDisconnectedLocations(RootNode root) {

		ArrayDeque<ProgramPoint> toRemove = new ArrayDeque<>();

		for (Entry<String, Map<String, ProgramPoint>> procPair : root.getRootAnnot().getProgramPoints().entrySet()) {
			for (Entry<String, ProgramPoint> pointPair : procPair.getValue().entrySet()) {
				if (pointPair.getValue().getIncomingEdges().size() == 0) {
					toRemove.add(pointPair.getValue());
				}
			}
		}

		while(!toRemove.isEmpty()){
			ProgramPoint current = toRemove.removeFirst();
			List<RCFGEdge> outEdges = new ArrayList<>(current.getOutgoingEdges());
			for(RCFGEdge out : outEdges){
				ProgramPoint target = (ProgramPoint) out.getTarget();
				if(target.getIncomingEdges().size() == 1){
					toRemove.addLast(target);
				}
				out.disconnectSource();
				out.disconnectTarget();
				mRemovedEdges++;
			}
			removeDisconnectedLocation(root, current);
		}
		
	}

	private void removeDisconnectedLocation(RootNode root, ProgramPoint toRemove) {
		// TODO: remove stuff from the root annotation
		mRemovedLocations++;
	}

	public RootNode getResult() {
		return mResult;
	}

}
