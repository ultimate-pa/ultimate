package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector;

import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class RCFGLoopDetectorObserver extends BaseObserver{

	private final RCFGLoopDetector mLoopDetector;

	public RCFGLoopDetectorObserver(final IUltimateServiceProvider services) {
		mLoopDetector = new RCFGLoopDetector(services);
	}
	
	@Override
	public boolean process(final IElement root) throws Throwable {
		if(root instanceof BoogieIcfgContainer){
			mLoopDetector.process((BoogieIcfgContainer) root);
			return false;
		}
		return true;
	}

}
