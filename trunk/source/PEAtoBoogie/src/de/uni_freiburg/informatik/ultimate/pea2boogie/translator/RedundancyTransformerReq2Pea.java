package de.uni_freiburg.informatik.ultimate.pea2boogie.translator;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.srparse.Durations;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.DeclarationPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType.ReqPeas;
import de.uni_freiburg.informatik.ultimate.pea2boogie.IReqSymbolTable;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.IReq2Pea;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.IReq2PeaAnnotator;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.IReq2PeaTransformer;
import de.uni_freiburg.informatik.ultimate.pea2boogie.testgen.ReqEffectStore;


public class RedundancyTransformerReq2Pea implements IReq2Pea {

	private final ILogger mLogger;
	private final List<DeclarationPattern> mInitPattern;
	private final List<ReqPeas> mReqPeas;
	private IReqSymbolTable mSymbolTable;
	private boolean mHasErrors;
	private final IUltimateServiceProvider mServices;
	private final Durations mDurations;
	
	public  RedundancyTransformerReq2Pea(final IUltimateServiceProvider services, final ILogger logger, final List<DeclarationPattern> init) {
		mServices = services;
		mLogger = logger;
		mInitPattern = init;
		mReqPeas = new ArrayList<>();
		mDurations = new Durations();
	}
	
	@Override
	public List<ReqPeas> getReqPeas() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IReqSymbolTable getSymboltable() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Durations getDurations() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void transform(IReq2Pea req2pea) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public boolean hasErrors() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public IReq2PeaAnnotator getAnnotator() {
		// TODO Auto-generated method stub
		return null;
	}
	
}