package de.uni_freiburg.informatik.ultimate.pea2boogie.testgen;

import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.DeclarationPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.IReq2Pea;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.IReq2PeaTransformer;

public class Req2CauseTrackingPeaTransformer implements IReq2PeaTransformer {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private Map<PhaseEventAutomata<CDD>, ReqEffectStore> mPea2EffectStore;

	public Req2CauseTrackingPeaTransformer(final IUltimateServiceProvider services, final ILogger logger) {
		mLogger = logger;
		mServices = services;
	}

	public Map<PhaseEventAutomata<CDD>, ReqEffectStore> getEffectStore() {
		return mPea2EffectStore;
	}

	@Override
	public IReq2Pea transform(final IReq2Pea req2pea, final List<DeclarationPattern> init,
			final List<PatternType<?>> requirements) {
		final Req2CauseTrackingPea req2CauseTracking = new Req2CauseTrackingPea(mServices, mLogger, init);
		req2CauseTracking.transform(req2pea);
		// TODO: find a more elegant way to access this data for postprocessing
		mPea2EffectStore = req2CauseTracking.getEffectStore();
		return req2CauseTracking;
	}

}
