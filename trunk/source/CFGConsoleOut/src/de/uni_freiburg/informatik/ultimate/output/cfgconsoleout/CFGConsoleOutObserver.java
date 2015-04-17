package de.uni_freiburg.informatik.ultimate.output.cfgconsoleout;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.structure.IWalkable;

public class CFGConsoleOutObserver implements IUnmanagedObserver {

	private Map<IElement, String> mSeenList;
	private int mNumRoots;
	private Logger mLogger;
	private final IUltimateServiceProvider mServices;

	public CFGConsoleOutObserver(IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public void init(GraphType modelType, int currentModelIndex, int numberOfModels) throws Throwable {
		mSeenList = new HashMap<IElement, String>();
		mNumRoots = -1;
	}

	@Override
	public boolean process(IElement root) {
		if (root instanceof IWalkable) {
			dfstraverse((IWalkable) root, "" + (++mNumRoots));
		}
		return false;
	}

	@Override
	public void finish() {
	}

	private void dfstraverse(IWalkable node, String numbering) {
		mSeenList.put(node, numbering);
		mLogger.info("Node " + numbering + "; Name: " + node.getPayload().getName() + ";Annotations: "
				+ node.getPayload().getAnnotations());
		List<IWalkable> newnodes = new ArrayList<IWalkable>();
		List<IWalkable> children = node.getSuccessors();
		int num = -1;
		// Add new nodes and detect back edges...
		for (IWalkable n : children) {
			String backedge = mSeenList.get(n);
			if (backedge != null)
				mLogger.info("Back edge from " + numbering + " to " + backedge);
			else {
				String newnumbering = numbering + "." + (++num);
				mSeenList.put(n, newnumbering);
				newnodes.add(n);
			}
		}
		for (IWalkable n : newnodes)
			dfstraverse(n, mSeenList.get(n));
	}

	@Override
	public boolean performedChanges() {
		return false;
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		return null;
	}
}
