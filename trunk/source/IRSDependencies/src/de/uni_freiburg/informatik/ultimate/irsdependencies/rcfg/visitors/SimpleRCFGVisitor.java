package de.uni_freiburg.informatik.ultimate.irsdependencies.rcfg.visitors;


import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.irsdependencies.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;

/**
 * 
 * 
 * @author dietsch
 * 
 */
public abstract class SimpleRCFGVisitor implements IObserver {

	protected static Logger sLogger = UltimateServices.getInstance().getLogger(
			Activator.PLUGIN_ID);
	
	public void endOfTrace() {
	}

	public void pre(RCFGNode node) {
	}

	public void pre(RCFGEdge edge) {
	}

	public void post(RCFGNode node) {
	}

	public void post(RCFGEdge edge) {
	}

	public void level(RCFGNode node) {
	}

	public void level(RCFGEdge edge) {
	}

	public abstract boolean abortCurrentBranch();

	public abstract boolean abortAll();

	@Override
	public void init() {
	}

	@Override
	public void finish() {
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		return null;
	}
}
