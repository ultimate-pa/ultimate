package de.uni_freiburg.informatik.ultimate.witnessprinter;

import de.uni_freiburg.informatik.ultimate.access.BaseObserver;
import de.uni_freiburg.informatik.ultimate.models.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

public class RCFGCatcher extends BaseObserver{

	private RootNode mRoot;
	
	@Override
	public boolean process(IElement root) throws Throwable {
		if(root instanceof RootNode){
			mRoot = (RootNode) root;	
		}
		return false;
	}
	
	RootNode getModel(){
		return mRoot;
	}
}
