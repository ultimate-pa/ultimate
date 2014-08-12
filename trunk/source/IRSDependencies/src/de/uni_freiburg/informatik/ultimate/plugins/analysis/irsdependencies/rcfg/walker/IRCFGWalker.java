package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.rcfg.walker;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

public interface IRCFGWalker
{
	void startFrom(RootNode node);
	
	public boolean addObserver(IObserver observer);
	
	public boolean removeObserver(IObserver observer);
	
	public void removeAllObservers();
	
	public boolean containsObserver(IObserver observer);
	
	public void run(RCFGNode node);
	
}
