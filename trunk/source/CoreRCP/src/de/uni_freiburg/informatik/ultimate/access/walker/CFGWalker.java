package de.uni_freiburg.informatik.ultimate.access.walker;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IManagedObserver;
import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions.Command;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.structure.IWalkable;
import de.uni_freiburg.informatik.ultimate.model.structure.WrapperNode;

public class CFGWalker extends BaseWalker {

	private HashSet<IWalkable> mVisitedNodes = new HashSet<IWalkable>();

	public CFGWalker(Logger logger) {
		super(logger);
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
	protected void runObserver(IElement element, IManagedObserver observer) {
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
				mLogger.debug("Skipping " + node.getPayload().getName());
			} else if (cmds.contains(WalkerOptions.Command.DESCEND)
					&& node.getSuccessors() != null) {
				for (IWalkable i : node.getSuccessors()) {
					if (!this.mVisitedNodes.contains(i)) {
						runObserver(i, observer);
					} else {
						mLogger.debug("CFGWalker >> Found Potential CutPoint: "
								+ i.getPayload().getName());
					}
				}
			}
		} else {
			mLogger.error("Unsupported model type");
		}

	}

	protected void runObserver(IElement element, IUnmanagedObserver observer) throws Throwable {
		IElement tobeproccessed = element;
		if (element instanceof WrapperNode) {
			WrapperNode wnode = (WrapperNode) element;
			if (wnode.getBacking() instanceof IElement) {
				tobeproccessed = (IElement) wnode.getBacking();
			}
		}

		if (observer.process(tobeproccessed)) {
			if (element instanceof IWalkable) {
				IWalkable node = (IWalkable) element;

				if (mVisitedNodes.contains(node)) {
					return;
				} else {
					mVisitedNodes.add(node);
					List<IWalkable> outgoings = node.getSuccessors();
					if (outgoings != null) {
						for (IWalkable i : outgoings) {
							runObserver(i, observer);
						}
					}
				}

			}
		}
	}

}
