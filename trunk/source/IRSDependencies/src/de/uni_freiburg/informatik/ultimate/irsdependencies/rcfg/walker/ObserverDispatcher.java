package de.uni_freiburg.informatik.ultimate.irsdependencies.rcfg.walker;

import java.util.LinkedList;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.irsdependencies.rcfg.visitors.SimpleRCFGVisitor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;

/**
 * 
 * ObserverDispatcher provides a flexible way to combine a certain way of graph
 * traversal (in,pre,postorder, breadth-first) with a certain order of observer
 * execution (either for each observer a own traversal, or in each node all
 * observers are called one after another).
 * 
 * This class and its descendants should only be used in conjunction with RCFGWalker
 * 
 * @author dietsch
 * 
 */
public abstract class ObserverDispatcher {
	protected List<SimpleRCFGVisitor> mObservers;
	
	protected final Logger mLogger ;
	protected IRCFGWalker mWalker;

	public ObserverDispatcher(Logger logger) {
		mObservers = new LinkedList<>();
		mLogger = logger;
	}

	public void setWalker(IRCFGWalker walker) {
		mWalker = walker;
	}

	public boolean addObserver(IObserver observer) {
		if (!(observer instanceof SimpleRCFGVisitor)) {
			mLogger.error("RCFGWalker only accepts RCFGVisitors");
			return false;
		}
		return mObservers.add((SimpleRCFGVisitor) observer);
	}

	public boolean removeObserver(IObserver observer) {
		return mObservers.remove(observer);
	}

	public void removeAllObservers() {
		mObservers.clear();
	}

	public boolean containsObserver(IObserver observer) {
		return mObservers.contains(observer);
	}

	public abstract void run(RCFGNode rootNode);

	protected abstract void callObservers(IRCFGVisitorDispatcher dispatcher);

	public abstract boolean abortCurrentBranch();

	public abstract boolean abortAll();

}
