package de.uni_freiburg.informatik.ultimate.reqtotestpowerset;

import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

public class ReqToTestPowersetObserver extends BaseObserver{

	public ReqToTestPowersetObserver(ILogger mLogger, IUltimateServiceProvider mServices, IToolchainStorage mStorage) {
		// TODO Auto-generated constructor stub
	}

	@Override
	public boolean process(IElement root) throws Throwable {
		// TODO Auto-generated method stub
		return false;
	}

	public IElement getAst() {
		// TODO Auto-generated method stub
		return null;
	}


}
