package local.stalin.plugins.output.cfgconsoleout;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import local.stalin.access.IUnmanagedObserver;
import local.stalin.access.WalkerOptions;
import local.stalin.core.api.StalinServices;
import local.stalin.model.IElement;
import local.stalin.model.INode;

import org.apache.log4j.Logger;

public class CFGConsoleOutObserver implements IUnmanagedObserver {

	private Map<IElement,String> mseenlist;
	private int mnumroots;
    private Logger m_Logger;
	
	@Override
	public boolean process(IElement root) {
		dfstraverse((INode)root, "" + (++mnumroots));
		return false;
	}

	@Override
	public void finish() {
		// Nothing to be done here...
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		// Not needed...
		return null;
	}

	@Override
	public void init() {
		mseenlist = new HashMap<IElement, String>();
		mnumroots = -1;
        m_Logger = StalinServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	}

	private void dfstraverse(INode node,String numbering) {
		mseenlist.put(node, numbering);
		m_Logger.info("Node " + numbering + "; Name: " + node.getPayload().getName() + ";Annotations: " + node.getPayload().getAnnotations());
		List<INode> newnodes = new ArrayList<INode>();
		List<INode> children = node.getOutgoingNodes();
		int num = -1;
		// Add new nodes and detect back edges...
		for( INode n : children ) {
			String backedge = mseenlist.get(n);
			if( backedge != null )
				m_Logger.info("Back edge from " + numbering + " to " + backedge);
			else {
				String newnumbering = numbering + "." + (++num);
				mseenlist.put(n,newnumbering);
				newnodes.add(n);
			}
		}
		for( INode n : newnodes )
			dfstraverse(n, mseenlist.get(n));
	}

	@Override
	public boolean performedChanges() {
		return false;
	}	
}
