package de.uni_freiburg.informatik.ultimate.pea2boogie.translator;

import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.DeclarationPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.IReq2Pea;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.IReq2PeaTransformer;
import de.uni_freiburg.informatik.ultimate.pea2boogie.testgen.ReqEffectStore;

public class ComplementTransformer implements IReq2PeaTransformer {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private Map<PhaseEventAutomata, ReqEffectStore> mPea2EffectStore;

	public ComplementTransformer(final IUltimateServiceProvider services, final ILogger logger) {
		mLogger = logger;
		mServices = services;
	}

	public Map<PhaseEventAutomata, ReqEffectStore> getEffectStore() {
		return mPea2EffectStore;
	}

	@Override
	public IReq2Pea transform(final IReq2Pea req2pea, final List<DeclarationPattern> init,
			final List<PatternType<?>> requirements) {
		ComplementTransformerReq2Pea complementTransformerReq2Pea = new ComplementTransformerReq2Pea(mServices, mLogger, init);
		complementTransformerReq2Pea.transform(req2pea);
		return complementTransformerReq2Pea;
	}
}

