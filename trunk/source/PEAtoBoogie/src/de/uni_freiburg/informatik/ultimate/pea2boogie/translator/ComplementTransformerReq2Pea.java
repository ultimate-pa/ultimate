package de.uni_freiburg.informatik.ultimate.pea2boogie.translator;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.pea.ComplementPEA;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.srparse.Durations;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.DeclarationPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType.ReqPeas;
import de.uni_freiburg.informatik.ultimate.pea2boogie.IReqSymbolTable;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.IReq2Pea;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.IReq2PeaAnnotator;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.ReqCheckAnnotator;
import de.uni_freiburg.informatik.ultimate.pea2boogie.testgen.Req2CauseTrackingCDD;
import de.uni_freiburg.informatik.ultimate.pea2boogie.testgen.ReqEffectStore;
import de.uni_freiburg.informatik.ultimate.pea2boogie.testgen.ReqTestAnnotator;

public class ComplementTransformerReq2Pea implements IReq2Pea {
	private final ILogger mLogger;
	private final List<DeclarationPattern> mInitPattern;
	private final List<ReqPeas> mReqPeas;
	private IReqSymbolTable mSymbolTable;
	private boolean mHasErrors;
	private final IUltimateServiceProvider mServices;
	private final Req2CauseTrackingCDD mCddTransformer;
	private final Durations mDurations;


	public ComplementTransformerReq2Pea(final IUltimateServiceProvider services, final ILogger logger,
			final List<DeclarationPattern> init) {
		mServices = services;
		mLogger = logger;
		mInitPattern = init;
		mReqPeas = new ArrayList<>();
		mCddTransformer = new Req2CauseTrackingCDD(mLogger);
		mDurations = new Durations();
	}


	@Override
	public void transform(IReq2Pea req2pea) {
		final List<ReqPeas> simplePeas = req2pea.getReqPeas();
		final IReqSymbolTable symbolTable = req2pea.getSymboltable();
		PhaseEventAutomata peaToComplement = simplePeas.get(0).getCounterTrace2Pea().get(0).getValue();
		ComplementPEA complementPEA = new ComplementPEA(peaToComplement);
		PhaseEventAutomata complementAutomaton = complementPEA.complement();
		
	}

	@Override
	public IReq2PeaAnnotator getAnnotator() {
		return new ReqCheckAnnotator(mServices, mLogger, mReqPeas, mSymbolTable, mDurations);
	}
	

	@Override
	public List<ReqPeas> getReqPeas() {
		return mReqPeas;
	}

	@Override
	public IReqSymbolTable getSymboltable() {
		return mSymbolTable;
	}
	
	@Override
	public boolean hasErrors() {
		return mHasErrors;
	}

	@Override
	public Durations getDurations() {
		return mDurations;
	}

}
