package de.uni_freiburg.informatik.ultimate.irsdependencies.rcfg.walker;

import de.uni_freiburg.informatik.ultimate.irsdependencies.rcfg.visitors.RCFGVisitor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

public class ObserverDispatcherSequential extends ObserverDispatcher
{

	private RCFGVisitor mCurrentVisitor;

	public void run(RCFGNode node)
	{
		if (!(node instanceof RootNode)) {
			sLogger.error("RCFGWalker can only process models created by RCFGBuilder");
			return;
		}
		for (RCFGVisitor visitor : mObservers) {
			mCurrentVisitor = visitor;
			mCurrentVisitor.init();
			mWalker.processProgram((RootNode) node);
			mCurrentVisitor.finish();
		}

	}

	protected void callObservers(IRCFGVisitorDispatcher dispatcher)
	{
		dispatcher.dispatch(mCurrentVisitor);
	}

	@Override
	public boolean abortCurrentBranch()
	{
		return mCurrentVisitor.abortCurrentBranch();
	}
	
	public boolean abortAll()
	{
		return mCurrentVisitor.abortAll();
	}
}
