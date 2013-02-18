package local.stalin.plugins.output.nodecounter;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.Stack;

import local.stalin.access.IUnmanagedObserver;
import local.stalin.access.WalkerOptions;
import local.stalin.core.api.StalinServices;
import local.stalin.model.IElement;
import local.stalin.model.INode;

import org.apache.log4j.Logger;

public class NodeCounterObserver implements IUnmanagedObserver {

	private Set<IElement> mseenlist;
	private Stack<IElement> mcurpath;
    private Logger m_Logger;
	private boolean mloopcheck = true;
	private int numnodes;
	private int numbackedges;
	private int numloops;
	
	public void setLoopCheck(boolean lc) {
		mloopcheck = lc;
	}
	
	@Override
	public boolean process(IElement root) {
		numnodes = 0;
		numbackedges = 0;
		numloops = 0;
		if( mloopcheck )
			dfstraverselc((INode)root);
		else
			dfstraverse((INode)root);
		m_Logger.info("Graph contains " + numnodes + " Nodes");
		if( mloopcheck ) {
			m_Logger.info("Graph contains " + numloops + " cycles");
			m_Logger.info("Graph contains " + numbackedges + " nodes with in-degree > 1");
		}
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
		mseenlist = new HashSet<IElement>();
		mcurpath = new Stack<IElement>();
        m_Logger = StalinServices.getInstance().getLogger(Activator.PLUGIN_ID);
	}

	private void dfstraverselc(INode node) {
		++numnodes;
		mseenlist.add(node);
		mcurpath.push(node);
		List<INode> children = node.getOutgoingNodes();
		for( INode n : children )
			if( !mseenlist.contains(n) )
				dfstraverselc(n);
			else {
				++numbackedges;
				if( mcurpath.contains(n) )
					++numloops;
			}
		mcurpath.pop();
	}
	
	private void dfstraverse(INode node) {
		++numnodes;
		List<INode> children = node.getOutgoingNodes();
		for( INode n : children )
			dfstraverse(n);
	}

	@Override
	public boolean performedChanges() {
		// TODO Auto-generated method stub
		return false;
	}
	
}
