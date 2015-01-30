package de.uni_freiburg.informatik.ultimate.buchiprogramproduct.optimizeproduct;

import java.util.ArrayDeque;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

public class RemoveInfeasibleEdges extends BaseProductOptimizer {

	public RemoveInfeasibleEdges(RootNode product, IUltimateServiceProvider services) {
		super(product, services);
		mLogger.info("Removed " + mRemovedEdges + " edges and " + mRemovedLocations
				+ " locations because of local infeasibility");
	}

	@Override
	protected void init(RootNode root, IUltimateServiceProvider services) {

	}

	@Override
	protected RootNode process(RootNode root) {
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
	
	public boolean IsGraphChanged() {
		return mRemovedEdges > 0 || mRemovedLocations > 0;
	}

}
