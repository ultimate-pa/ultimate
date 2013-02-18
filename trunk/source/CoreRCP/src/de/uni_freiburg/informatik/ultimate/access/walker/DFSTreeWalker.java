package de.uni_freiburg.informatik.ultimate.access.walker;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.access.IManagedObserver;
import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions.Command;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.INode;
import de.uni_freiburg.informatik.ultimate.model.structure.IWalkable;

import org.apache.log4j.Logger;

/**
 * This is a basic tree walker. it does breadth first search. For a depth first
 * search you might want to implement your own walkers DD: I think it does
 * depth-first ;)
 * 
 * @author bisser
 * @version 0.1.3 $LastChangedDate: 2008-02-09 23:14:39 +0100 (Sa, 09 Feb 2008)
 *          $ $LastChangedBy: bisser $ $LastChangedRevision: 473 $
 */
public class DFSTreeWalker implements IWalker {

	// TODO: Create multiple modes for this treewalker, like depth first /
	// breath first / fields only / replace subtree / etc.

	/**
	 * The default console or logging output should go here
	 */
	private static Logger s_Logger = UltimateServices.getInstance().getLogger(
			Activator.s_PLUGIN_ID);
	/**
	 * The List of observers
	 */
	private List<IObserver> m_Observers;

	/**
	 * Standard constructor
	 */
	public DFSTreeWalker() {
		m_Observers = new LinkedList<IObserver>();
	}

	/**
	 * Adds a Visitor
	 * 
	 * @param v
	 *            the Visitor to be added
	 * @return True if the Visitor is adds, false if it was already there
	 */
	public boolean addObserver(IObserver v) {
		if (!m_Observers.contains(v)) {
			this.m_Observers.add(v);
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
	public boolean removeObserver(IObserver v) {
		if (m_Observers.contains(v)) {
			this.m_Observers.remove(v);
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
	public void run(IElement inode) {
		if (inode != null) {
			for (IObserver v : m_Observers) {
				runObserver(inode, v);
			}
		}
	}

	private void runObserver(IElement root, IObserver observer) {
		if (observer instanceof IUnmanagedObserver) {
			runObserver(root, (IUnmanagedObserver) observer);
		} else if (observer instanceof IManagedObserver) {
			runObserver(root, (IManagedObserver) observer);
		} else {
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
	 * @param v
	 *            The Visitor
	 */
	private void runObserver(IElement element, IManagedObserver v) {
		// TODO implement correct usage of walker states
		// TODO implement correct interpretation of walker commands

		if (element instanceof IWalkable) {
			IWalkable node = (IWalkable) element;

			ArrayList<Command> cmds = new ArrayList<Command>();
			for (Command cmd : v.process(node.getPayload(),
					WalkerOptions.State.OUTER, node.getSuccessors().size())) {
				cmds.add(cmd);
			}

			if (cmds.toString().equals(WalkerOptions.Command.SKIP.toString())) {
				s_Logger.debug("Skipping " + node.getPayload().getName());
			} else if (cmds.contains(WalkerOptions.Command.DESCEND)) {
				for (IWalkable i : node.getSuccessors()) {
					// TODO handle labeled trees
					runObserver(i, v);
				}
			}
		} else {
			s_Logger.error("Unsupported model type");
		}

	}

	private void runObserver(IElement element, IUnmanagedObserver v) {
		if (element instanceof IWalkable) {
			IWalkable node = (IWalkable) element;

			if (v.process(node)) {
				List<IWalkable> outgoings = node.getSuccessors();
				if (outgoings != null) {
					for (IWalkable i : outgoings) {
						runObserver(i, v);
					}
				}
			}
		} else {
			s_Logger.error("Unsupported model type");
		}
	}

	// @Override
	public boolean containsObserver(IObserver observer) {
		return this.m_Observers.contains(observer);
	}

	// @Override
	public void removeAllObservers() {
		this.m_Observers = null;
		this.m_Observers = new LinkedList<IObserver>();

	}

}
