package de.uni_freiburg.informatik.ultimate.irsdependencies.rcfg.walker;

import java.util.HashMap;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.irsdependencies.rcfg.visitors.SimpleRCFGVisitor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

public class ObserverDispatcherParallel extends ObserverDispatcher
{
	private HashMap<SimpleRCFGVisitor, Boolean> mVisitorStateAbortCurrent;
	private HashMap<SimpleRCFGVisitor, Boolean> mVisitorStateAbortAll;

	public ObserverDispatcherParallel(Logger logger)
	{
		super(logger);
		mVisitorStateAbortCurrent = new HashMap<>();
		mVisitorStateAbortAll = new HashMap<>();
	}

	public void run(RCFGNode node)
	{
		if (!(node instanceof RootNode)) {
			mLogger.error("RCFGWalker can only process models created by RCFGBuilder");
			return;
		}

		for (SimpleRCFGVisitor visitor : mObservers) {
			mVisitorStateAbortCurrent.put(visitor, true);
			visitor.init();
		}

		mWalker.startFrom((RootNode) node);
		
		for (SimpleRCFGVisitor visitor : mObservers) {
			visitor.finish();
		}
	}

	protected void callObservers(IRCFGVisitorDispatcher dispatcher)
	{
		for (SimpleRCFGVisitor visitor : mObservers) {
			if (mVisitorStateAbortCurrent.get(visitor)) {
				dispatcher.dispatch(visitor);
				if (visitor.abortCurrentBranch()) {
					mVisitorStateAbortCurrent.put(visitor, false);
				}
				if(visitor.abortAll()){
					mVisitorStateAbortAll.put(visitor, false);
				}
			}
		}
	}

	@Override
	public boolean abortCurrentBranch()
	{
		boolean rtr = false;
		for(boolean vis : mVisitorStateAbortCurrent.values()){
			rtr = rtr || vis;
		}
		return rtr;
	}

	@Override
	public boolean abortAll()
	{
		boolean rtr = false;
		for(boolean vis : mVisitorStateAbortAll.values()){
			rtr = rtr || vis;
		}
		return rtr;
	}
}
