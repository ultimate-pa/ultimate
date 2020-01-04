package de.uni_frieburg.informatik.ultimate.pea2boogie.testgen;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InitializationPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.IReq2Pea;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.IReq2PeaTransformer;

public class Req2CauseTrackingPeaTransformer implements IReq2PeaTransformer {
	
	private final ILogger mLogger;
	
	public Req2CauseTrackingPeaTransformer(final ILogger logger) {
		mLogger = logger;
	}

	@Override
	public IReq2Pea transform(IReq2Pea req2pea, List<InitializationPattern> init, List<PatternType> requirements) {
		IReq2Pea req2CauseTracking = new Req2CauseTrackingPea(mLogger , init, requirements);	
		req2CauseTracking.transform(req2pea);
		return req2CauseTracking;
	}

}
