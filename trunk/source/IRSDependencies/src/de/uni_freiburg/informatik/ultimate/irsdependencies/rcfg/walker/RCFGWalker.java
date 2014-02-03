package de.uni_freiburg.informatik.ultimate.irsdependencies.rcfg.walker;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.irsdependencies.Activator;
import de.uni_freiburg.informatik.ultimate.irsdependencies.rcfg.visitors.RCFGVisitor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;

/**
 * The abstract class RCFGWalker provides standard observer handling (add,
 * remove, removeAll, contains) for all traversals of RCFG graphs. Basic usage
 * is as follows:
 * 
 * Create object with desired ObserverDispatcher.
 * 
 * Attach desired observers.
 * 
 * Call "run" on RCFG.
 * 
 * As walkers are responsible for the traversal, they normally contain the
 * algorithm necessary for searches and heuristics. The actual work is then done
 * by observers.
 * 
 * Please note that if you do not attach a observer to a walker, the dispatcher
 * will prevent executing the walking code.
 * 
 * @author dietsch
 * 
 */
public abstract class RCFGWalker implements IRCFGWalker {

	protected ObserverDispatcher mDispatcher;
	protected static Logger sLogger = UltimateServices.getInstance().getLogger(
			Activator.PLUGIN_ID).getLogger("RCFGWalker");

	public RCFGWalker(ObserverDispatcher dispatcher) {
		mDispatcher = dispatcher;
	}

	@Override
	public boolean addObserver(IObserver observer) {
		return mDispatcher.addObserver(observer);
	}

	@Override
	public boolean removeObserver(IObserver observer) {
		return mDispatcher.removeObserver(observer);
	}

	@Override
	public void removeAllObservers() {
		mDispatcher.removeAllObservers();
	}

	@Override
	public boolean containsObserver(IObserver observer) {
		return mDispatcher.containsObserver(observer);
	}

	@Override
	public void run(RCFGNode rootNode) {
		mDispatcher.run(rootNode);
	}

	protected void programExitReached() {
		mDispatcher.callObservers(new IRCFGVisitorDispatcher() {
			public void dispatch(RCFGVisitor visitor) {
				visitor.endOfTrace();
			}
		});
	}

	protected void pre(final RCFGNode node) {
		mDispatcher.callObservers(new IRCFGVisitorDispatcher() {
			public void dispatch(RCFGVisitor visitor) {
				visitor.pre(node);
			}
		});
	}

	protected void pre(final RCFGEdge edge) {
		mDispatcher.callObservers(new IRCFGVisitorDispatcher() {
			public void dispatch(RCFGVisitor visitor) {
				visitor.pre(edge);
			}
		});
	}

	protected void post(final RCFGNode node) {
		mDispatcher.callObservers(new IRCFGVisitorDispatcher() {
			public void dispatch(RCFGVisitor visitor) {
				visitor.post(node);
			}
		});
	}

	protected void post(final RCFGEdge edge) {
		mDispatcher.callObservers(new IRCFGVisitorDispatcher() {
			public void dispatch(RCFGVisitor visitor) {
				visitor.post(edge);
			}
		});
	}
	
	protected void level(final RCFGNode node) {
		mDispatcher.callObservers(new IRCFGVisitorDispatcher() {
			public void dispatch(RCFGVisitor visitor) {
				visitor.level(node);
			}
		});
	}

	protected void level(final RCFGEdge edge) {
		mDispatcher.callObservers(new IRCFGVisitorDispatcher() {
			public void dispatch(RCFGVisitor visitor) {
				visitor.level(edge);
			}
		});
	}
}
