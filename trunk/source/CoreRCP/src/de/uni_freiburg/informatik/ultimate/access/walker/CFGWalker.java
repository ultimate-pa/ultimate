package de.uni_freiburg.informatik.ultimate.access.walker;

import java.util.ArrayList;
import java.util.HashSet;
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

public class CFGWalker implements IWalker {

	/**
	 * The default console or logging output should go here
	 */
	private static Logger s_Logger = UltimateServices.getInstance().getLogger(
			Activator.s_PLUGIN_ID);
	/**
	 * The list of all visited node of the graph
	 */
	private HashSet<IWalkable> mVisitedNodes = new HashSet<IWalkable>();
	/**
	 * The List of observers
	 */
	private List<IObserver> mObservers;

	/**
	 * Standard constructor
	 */
	public CFGWalker() {
		mObservers = new LinkedList<IObserver>();
	}

	/**
	 * Adds a Visitor
	 * 
	 * @param observer
	 *            the Visitor to be added
	 * @return True if the Visitor is adds, false if it was already there
	 */
	public boolean addObserver(IObserver observer) {
		if (!mObservers.contains(observer)) {
			this.mObservers.add(observer);
			return true;
		}
		return false;
	}

	// @Override
	public boolean containsObserver(IObserver observer) {
		return this.mObservers.contains(observer);
	}

	// @Override
	public void removeAllObservers() {
		this.mObservers = new LinkedList<IObserver>();
	}

	/**
	 * Removes a Visitor from the list
	 * 
	 * @param observer
	 *            The Visitor to be removed
	 * @return True if it was removed
	 */
	public boolean removeObserver(IObserver observer) {
		return this.mObservers.remove(observer);
	}

	/**
	 * The walker will traverse the given subtree for each observer sequentially
	 * in the order of their insertion.
	 * 
	 * @param inode
	 *            usually the starting point
	 */
	public void run(IElement inode) {
		for (IObserver observer : mObservers) {
			runObserver(inode, observer);
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
	 * @param observer
	 *            The Visitor
	 */
	private void runObserver(IElement element, IManagedObserver observer) {
		// TODO implement correct usage of walker states
		// TODO implement correct interpretation of walker commands

		if (element instanceof IWalkable) {
			IWalkable node = (IWalkable) element;
			this.mVisitedNodes.add(node);

			ArrayList<Command> cmds = new ArrayList<Command>();
			for (Command cmd : observer.process(node.getPayload(),
					WalkerOptions.State.OUTER, node.getSuccessors().size())) {
				cmds.add(cmd);
			}

			if (cmds.toString().equals(WalkerOptions.Command.SKIP.toString())) {
				s_Logger.debug("Skipping " + node.getPayload().getName());
			} else if (cmds.contains(WalkerOptions.Command.DESCEND)
					&& node.getSuccessors() != null) {
				for (IWalkable i : node.getSuccessors()) {
					if (!this.mVisitedNodes.contains(i)) {
						runObserver((INode) i, observer);
					} else {
						s_Logger.debug("CFGWalker >> Found Potential CutPoint: "
								+ i.getPayload().getName());
					}
				}
			}
		} else {
			s_Logger.error("Unsupported model type");
		}

	}

	private void runObserver(IElement element, IUnmanagedObserver observer) {
		if (element instanceof IWalkable) {
			IWalkable node = (IWalkable) element;
			if (observer.process(node)) {
				if (this.mVisitedNodes.contains(node)) {
					return;
				} else {
					this.mVisitedNodes.add(node);
					for (IWalkable i : node.getSuccessors()) {
						runObserver(i, observer);
					}
				}
			}
		} else {
			s_Logger.error("Unsupported model type");
		}
	}

}
