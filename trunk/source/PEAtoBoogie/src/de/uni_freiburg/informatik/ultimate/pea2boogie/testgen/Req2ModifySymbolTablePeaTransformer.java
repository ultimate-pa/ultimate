package de.uni_freiburg.informatik.ultimate.pea2boogie.testgen;

import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.DeclarationPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.IReq2Pea;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.IReq2PeaTransformer;

public class Req2ModifySymbolTablePeaTransformer implements IReq2PeaTransformer {
	
	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	
	public Req2ModifySymbolTablePeaTransformer(final IUltimateServiceProvider services, final ILogger logger) {
		mLogger = logger;
		mServices = services;
	}

	@Override
	public IReq2Pea transform(final IReq2Pea req2pea, final List<DeclarationPattern> init, final List<PatternType<?>> requirements) {
		final Req2ModifySymbolTablePea req2ModifySymbolTablePea = new Req2ModifySymbolTablePea(mServices, mLogger, init);
		
		req2ModifySymbolTablePea.transform(req2pea);
		return req2ModifySymbolTablePea;
	}

}
