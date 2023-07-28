package de.uni_freiburg.informatik.ultimate.pea2boogie.translator;

import java.util.ArrayList;
import java.util.List;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.pea.ComplementPEA;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.srparse.Durations;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.DeclarationPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType.ReqPeas;
import de.uni_freiburg.informatik.ultimate.pea2boogie.IReqSymbolTable;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.IReq2Pea;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.IReq2PeaAnnotator;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.ReqCheckAnnotator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
* This class constructs from a ReqPea containing one non-composite PEA two ReqPeas, 
* one that represents the totalised PEA and one that represents the complement PEA
* 
* The purpose of this class is to enable the complement check, a check to determine 
* whether or not two PEAs are complements of each other.
* 
* @author lena
*
*/

public class ComplementTransformerReq2Pea implements IReq2Pea {
	private final ILogger mLogger;
	private final List<DeclarationPattern> mInitPattern;
	private final List<ReqPeas> mReqPeas;
	private IReqSymbolTable mSymbolTable;
	private boolean mHasErrors;
	private final IUltimateServiceProvider mServices;
	private final Durations mDurations;


	public ComplementTransformerReq2Pea(final IUltimateServiceProvider services, final ILogger logger,
			final List<DeclarationPattern> init) {
		mServices = services;
		mLogger = logger;
		mInitPattern = init;
		mReqPeas = new ArrayList<>();
		mDurations = new Durations();
	}


	@Override
	public void transform(IReq2Pea req2pea) {
		final ReqSymboltableBuilder builder = new ReqSymboltableBuilder(mLogger);
		final List<ReqPeas> peas = req2pea.getReqPeas();
		if (peas.size() != 1) {
			mLogger.error("Number of PEAs must be exactly 1.");
		}
		final IReqSymbolTable symbolTable = req2pea.getSymboltable();
		mSymbolTable = symbolTable;

		for (final DeclarationPattern p : mInitPattern) {
			builder.addInitPattern(p);
			mDurations.addInitPattern(p);
		}
		ReqPeas reqPeas =  peas.get(0); 
		final PatternType<?> pattern = peas.get(0).getPattern();
		final List<Entry<CounterTrace, PhaseEventAutomata>> ct2pea = reqPeas.getCounterTrace2Pea();
		
		final List<Entry<CounterTrace, PhaseEventAutomata>> totalCt2pea = new ArrayList<>();
		final List<Entry<CounterTrace, PhaseEventAutomata>> complementCt2pea = new ArrayList<>();
		
		for (Entry<CounterTrace, PhaseEventAutomata> pea : ct2pea) {
			PhaseEventAutomata peaToComplement = pea.getValue();
			ComplementPEA complementPea= new ComplementPEA(peaToComplement);
			PhaseEventAutomata totalisedPea = complementPea.getTotalisedPEA();
			PhaseEventAutomata complementedPEA = complementPea.getComplementPEA();
			totalCt2pea.add(new Pair<>(pea.getKey(), totalisedPea));
			builder.addPea(pattern, totalisedPea);
			// The countertrace is wrong for the complemented Pea. I dont know how to negate a DC formula.
			builder.addPea(pattern, complementedPEA);
			complementCt2pea.add(new Pair<>(pea.getKey(), complementedPEA));
			
		}		
		mReqPeas.add(new ReqPeas(pattern, totalCt2pea));
		mReqPeas.add(new ReqPeas(pattern, complementCt2pea));
		mSymbolTable = builder.constructSymbolTable();
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
