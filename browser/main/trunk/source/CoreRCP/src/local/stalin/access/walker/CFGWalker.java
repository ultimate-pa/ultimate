package local.stalin.access.walker;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import local.stalin.access.IManagedObserver;
import local.stalin.access.IObserver;
import local.stalin.access.IUnmanagedObserver;
import local.stalin.access.WalkerOptions;
import local.stalin.access.WalkerOptions.Command;
import local.stalin.core.api.StalinServices;
import local.stalin.core.coreplugin.Activator;
import local.stalin.model.IElement;
import local.stalin.model.INode;

import org.apache.log4j.Logger;

public class CFGWalker implements IWalker {

	/**
	 * The default console or logging output should go here
	 */
	private static Logger s_Logger = StalinServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	/**
	 * The list of all visited node of the graph
	 */
	private LinkedList<INode> m_visitedNodes = new LinkedList<INode>();
    /**
     * The List of observers
     */
    private List<IObserver> m_Observers;

    /**
     * Standard constructor
     */
    public CFGWalker() {
        m_Observers = new LinkedList<IObserver>();
    }

    /**
     * Adds a Visitor
     * 
     * @param observer
     *            the Visitor to be added
     * @return True if the Visitor is adds, false if it was already there
     */
    public boolean addObserver(IObserver observer) {
        if (!m_Observers.contains(observer)) {
            this.m_Observers.add(observer);
            return true;
        }
        return false;
    }

	//@Override
	public boolean containsObserver(IObserver observer) {
		return this.m_Observers.contains(observer);
	}

	//@Override
	public void removeAllObservers() {
		this.m_Observers = null;
		this.m_Observers = new LinkedList<IObserver>();
		
	}
    
    /**
     * Removes a Visitor from the list
     * 
     * @param observer
     *            The Visitor to be removed
     * @return True if it was removed
     */
    public boolean removeObserver(IObserver observer) {
        if (m_Observers.contains(observer)) {
            this.m_Observers.remove(observer);
            return true;
        }
        return false;
    }

    /**
	 * The walker will traverse the given subtree for each observer sequentially
	 * in the order of their insertion.
	 * 
	 * @param inode
	 *            usually the starting point
	 */
    public void run(INode inode) {
        for (IObserver observer : m_Observers) {
        	runObserver(inode, observer);	
        }
    }
   
    private void runObserver(INode root, IObserver observer){
    	if(observer instanceof IUnmanagedObserver){
    		runObserver (root,(IUnmanagedObserver)observer);
    	}
    	else if(observer instanceof IManagedObserver){
    		runObserver (root,(IManagedObserver)observer);
    	}
    	else {
    		s_Logger.error("Illegal observer type supplied, aborting...");
    	}
    }

    /**
	 * Does the actual walking for IManagedObservers. Has to handle all logic
	 * with respect to managed mode.
	 * 
	 * Currently not complete!
	 * 
	 * @param element
	 *            start INode
	 * @param observer
	 *            The Visitor
	 */
    private void runObserver(INode element, IManagedObserver observer) {
    	//TODO implement correct usage of walker states 
    	//TODO implement correct interpretation of walker commands
    	
    	this.m_visitedNodes.add(element);
    	
    	ArrayList<Command> cmds = new ArrayList<Command>();
    	for (Command cmd : observer.process(element.getPayload(),WalkerOptions.State.OUTER,element.getChildCount())){
    		cmds.add(cmd);
    	}
    	
    	if (cmds.toString().equals(WalkerOptions.Command.SKIP.toString())){
        	s_Logger.debug("Skipping "+element.getPayload().getName());
        }
    	else if (cmds.contains(WalkerOptions.Command.DESCEND)) {
			for (IElement i : element.getOutgoingNodes()) {
				//TODO handle labeled trees
				if (i instanceof INode) {
			    	if (!this.m_visitedNodes.contains(i)){
			    		runObserver((INode) i, observer);
			    	} else {
			    		s_Logger.info("CFGWalker >> Found Potenial CutPoint: " + i.getPayload().getName());
			    	}
				}
			}
		}
        
    }
    
    private void runObserver(INode element, IUnmanagedObserver observer) {
        if (observer.process(element)) {
        	if (this.m_visitedNodes.contains(element)){
        		return;
        	} else {
        		this.m_visitedNodes.add(element);
        		for (IElement i : element.getOutgoingNodes()) {
    				if (i instanceof INode) {
    					runObserver((INode) i, observer);
    				}
    			}
        	}
		}
    }
    
}
