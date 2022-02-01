package de.uni_freiburg.informatik.ultimate.witnessprinter;

import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;

public class RCFGCatcher extends BaseObserver{

	private BoogieIcfgContainer mRoot;
	
	@Override
	public boolean process(final IElement root) throws Throwable {
		if(root instanceof BoogieIcfgContainer){
			mRoot = (BoogieIcfgContainer) root;	
		}
		return false;
	}
	
	BoogieIcfgContainer getModel(){
		return mRoot;
	}
}
