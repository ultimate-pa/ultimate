package local.stalin.model;

import java.util.LinkedList;
import java.util.List;

import local.stalin.core.api.StalinServices;
import local.stalin.core.coreplugin.Activator;

import org.apache.log4j.Logger;

/**
 * This is a basic tree walker. it does breadth first search. For a depth first
 * search you might want to implement your own walkers DD: I think it does
 * depth-first ;)
 * 
 * @author bisser
 * @version 0.1.3 $LastChangedDate: 2010-04-12 10:18:09 +0200 (Mo, 12. Apr 2010) $
 *          $LastChangedBy: christj $ $LastChangedRevision: 2254 $
 */
public class TreeWalker {
	
	// TODO: Create multiple modes for this treewalker, like depth first / breath first / fields only / replace subtree / etc. 
	
	/**
	 * The default console or logging output should go here
	 */
	private static Logger s_Logger = StalinServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
    /**
     * The List of Visitors
     */
    private List<Visitor> m_Visitors;

    /**
     * Standard constructor
     */
    public TreeWalker() {
        m_Visitors = new LinkedList<Visitor>();
    }

    /**
     * Constructs a new TreeWalker with one Visitor
     * 
     * @param v
     *            The Visitor
     */
    public TreeWalker(Visitor v) {
        m_Visitors = new LinkedList<Visitor>();
        m_Visitors.add(v);
    }

    /**
     * Contructs a new TreeWalker with a list of Visitors
     * 
     * @param vs
     *            The Visitors
     */
    public TreeWalker(List<Visitor> vs) {
        m_Visitors = vs;
    }

    /**
     * @return a the first Visitor
     * @deprecated use getVisitors
     */
    public Visitor getVisitor() {
        return m_Visitors.get(0);
    }

    /**
	 * Gets a list of Visitors
	 * @return  List of Visitors
	 * @uml.property  name="visitors"
	 */
    public List<Visitor> getVisitors() {
        return m_Visitors;
    }

    /**
	 * Set the Visitors
	 * @param Visitors  The list of visitors
	 * @uml.property  name="visitors"
	 */
    public void setVisitors(List<Visitor> Visitors) {
        m_Visitors = Visitors;
    }

    /**
     * Adds a Visitor
     * 
     * @param visitor
     *            the Visitor to be added
     * @deprecated use addVisitor and removeVisitor
     */
    public void setVisitor(Visitor visitor) {
        addVisitor(visitor);
    }

    /**
     * Adds a Visitor
     * 
     * @param v
     *            the Visitor to be added
     * @return True if the Visitor is addes, false if it was already there
     */
    public boolean addVisitor(Visitor v) {
        if (!m_Visitors.contains(v)) {
            this.m_Visitors.add(v);
            return true;
        }
        return false;
    }

    /**
     * Removes a Visitor from the list
     * 
     * @param v
     *            The Visitor to be removed
     * @return True if it was removed
     */
    public boolean removeVisitor(Visitor v) {
        if (m_Visitors.contains(v)) {
            this.m_Visitors.remove(v);
            return true;
        }
        return false;
    }

    /**
     * Lets the walker walk in a recursive way
     * 
     * @param inode
     *            usually the starting point
     */
    public void run(INode inode) {
        for (Visitor v : m_Visitors) {
            v.reset();
            runVisitor(inode, v);
        }
    }

    /**
     * Does the actual walking
     * 
     * @param element
     *            start INode
     * @param v
     *            The Visitor
     */
    protected void runVisitor(INode element, Visitor v) {
        if (v.process(element.getPayload())) {
			for (IElement i : element.getOutgoingNodes()) {
				if (i instanceof INode) {
					runVisitor((INode) i, v);
				}
			}
		}
    }

    /**
	 * Lets the walker walk in a recursive way
	 * 
	 * @param inode
	 *            usually the starting point
	 * @param params
	 *            Array of type Object which is passed to the Visitors. The
	 *            first field should contain a boolean to indicate if the
	 *            TreeWalker should continue walking the current subgraph or not
	 */
    public void run(INode inode, Object[] params) {
        for (Visitor v : m_Visitors) {
            v.reset();
            runVisitor(inode, v, params);
        }
    }

    /**
	 * Does the actual walking
	 * 
	 * @param inode
	 *            start INode
	 * @param v
	 *            The Visitor
	 * @param params
	 *            Array of type Object which is passed to the Visitors. The first field
	 *            should contain a boolean to indicate if the TreeWalker should
	 *            continue walking the current subgraph or not
	 */
    protected void runVisitor(INode inode, Visitor v, Object[] params) {
		boolean choice;
		Object[] rtrValue = v.process(inode.getPayload(), params);
		try {
			choice = ((Boolean) (rtrValue[0])).booleanValue();
		} catch (ClassCastException cce) {
			choice = false;
			s_Logger
					.warn("First field in Visitor return value (Object[]) is no boolean ! Setting value to false...");
		}
		if (choice) {
			for (IElement i : inode.getOutgoingNodes()) {
				if (i instanceof INode) {
					runVisitor((INode) i, v, params);
				}
			}
		}
	}
}
