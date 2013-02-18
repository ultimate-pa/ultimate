package de.uni_freiburg.informatik.ultimate.irs.dependencies.rcfg.walker;

import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.irs.dependencies.rcfg.visitors.RCFGVisitor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

public class ObserverDispatcherParallel extends ObserverDispatcher
{
	private HashMap<RCFGVisitor, Boolean> mVisitorStateAbortCurrent;
	private HashMap<RCFGVisitor, Boolean> mVisitorStateAbortAll;

	public ObserverDispatcherParallel()
	{
		super();
		mVisitorStateAbortCurrent = new HashMap<>();
		mVisitorStateAbortAll = new HashMap<>();
	}

	public void run(RCFGNode node)
	{
		if (!(node instanceof RootNode)) {
			sLogger.error("RCFGWalker can only process models created by RCFGBuilder");
			return;
		}

		for (RCFGVisitor visitor : mObservers) {
			mVisitorStateAbortCurrent.put(visitor, true);
			visitor.init();
		}

		mWalker.processProgram((RootNode) node);
		
		for (RCFGVisitor visitor : mObservers) {
			visitor.finish();
		}
	}

	protected void callObservers(IRCFGVisitorDispatcher dispatcher)
	{
		for (RCFGVisitor visitor : mObservers) {
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
