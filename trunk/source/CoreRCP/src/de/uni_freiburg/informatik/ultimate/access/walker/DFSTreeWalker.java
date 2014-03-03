package de.uni_freiburg.informatik.ultimate.access.walker;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.access.IManagedObserver;
import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions.Command;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.structure.IWalkable;
import de.uni_freiburg.informatik.ultimate.model.structure.WrapperNode;

/**
 * This is a basic tree walker. it does breadth first search. For a depth first
 * search you might want to implement your own walkers.
 * 
 * @author dietsch
 */
public class DFSTreeWalker extends BaseWalker {

	public DFSTreeWalker() {
		super();
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
	protected void runObserver(IElement element, IManagedObserver v) {
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
				sLogger.debug("Skipping " + node.getPayload().getName());
			} else if (cmds.contains(WalkerOptions.Command.DESCEND)) {
				for (IWalkable i : node.getSuccessors()) {
					// TODO handle labeled trees
					runObserver(i, v);
				}
			}
		} else {
			sLogger.error("Unsupported model type");
		}

	}

	protected void runObserver(IElement element, IUnmanagedObserver v) throws Throwable {

		if(element == null || v == null){
			return;
		}
		
		IElement tobeproccessed = element;

		if (element instanceof WrapperNode) {
			WrapperNode wnode = (WrapperNode) element;
			if (wnode.getBacking() instanceof IElement) {
				tobeproccessed = (IElement) wnode.getBacking();
			}
		}

		if (v.process(tobeproccessed)) {
			if (element instanceof IWalkable) {
				IWalkable node = (IWalkable) element;
				List<IWalkable> outgoings = node.getSuccessors();
				if (outgoings != null) {
					for (IWalkable i : outgoings) {
						runObserver(i, v);
					}
				}

			}
		}
	}

}
