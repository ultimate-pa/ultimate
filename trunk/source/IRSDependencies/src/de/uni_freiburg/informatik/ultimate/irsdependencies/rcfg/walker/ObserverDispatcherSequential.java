package de.uni_freiburg.informatik.ultimate.irsdependencies.rcfg.walker;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.irsdependencies.rcfg.visitors.SimpleRCFGVisitor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

public class ObserverDispatcherSequential extends ObserverDispatcher
{

	public ObserverDispatcherSequential(Logger logger) {
		super(logger);
	}

	private SimpleRCFGVisitor mCurrentVisitor;

	public void run(RCFGNode node)
	{
		if (!(node instanceof RootNode)) {
			mLogger.error("RCFGWalker can only process models created by RCFGBuilder");
			return;
		}
		for (SimpleRCFGVisitor visitor : mObservers) {
			mCurrentVisitor = visitor;
			mCurrentVisitor.init();
			mWalker.startFrom((RootNode) node);
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
