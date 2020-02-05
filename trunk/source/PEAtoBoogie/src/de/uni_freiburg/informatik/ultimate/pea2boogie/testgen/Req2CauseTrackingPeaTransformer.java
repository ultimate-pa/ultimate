package de.uni_freiburg.informatik.ultimate.pea2boogie.testgen;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InitializationPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.IReq2Pea;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.IReq2PeaTransformer;

public class Req2CauseTrackingPeaTransformer implements IReq2PeaTransformer {
	
	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	
	public Req2CauseTrackingPeaTransformer(final IUltimateServiceProvider services, final ILogger logger) {
		mLogger = logger;
		mServices = services;
	}

	@Override
	public IReq2Pea transform(IReq2Pea req2pea, List<InitializationPattern> init, List<PatternType> requirements) {
		IReq2Pea req2CauseTracking = new Req2CauseTrackingPea(mServices, mLogger , init);	
		req2CauseTracking.transform(req2pea);
		return req2CauseTracking;
	}

}
