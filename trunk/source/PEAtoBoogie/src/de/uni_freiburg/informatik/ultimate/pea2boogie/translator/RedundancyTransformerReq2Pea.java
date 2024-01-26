package de.uni_freiburg.informatik.ultimate.pea2boogie.translator;

import java.util.ArrayList;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.PEAComplement;
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

public class RedundancyTransformerReq2Pea implements IReq2Pea {

	private final ILogger mLogger;
	private final List<DeclarationPattern> mInitPattern;
	private final List<ReqPeas<CDD>> mReqPeas;
	private IReqSymbolTable mSymbolTable;
	private boolean mHasErrors;
	private final IUltimateServiceProvider mServices;
	private final Durations mDurations;

	public RedundancyTransformerReq2Pea(final IUltimateServiceProvider services, final ILogger logger,
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
		final IReqSymbolTable symbolTable = req2pea.getSymboltable();
		mSymbolTable = symbolTable;
		Set<String> constVars = mSymbolTable.getConstVars();
		String deltaIDString = mSymbolTable.getDeltaVarName();

		for (final DeclarationPattern p : mInitPattern) {
			builder.addInitPattern(p);
			mDurations.addInitPattern(p);
		}

		final List<ReqPeas<CDD>> peas = req2pea.getReqPeas();
		for (ReqPeas<CDD> reqPea : peas) {
			final PatternType<?> pattern = reqPea.getPattern();
			final List<Entry<CounterTrace, PhaseEventAutomata<CDD>>> ct2pea = reqPea.getCounterTrace2Pea();

			final List<Entry<CounterTrace, PhaseEventAutomata<CDD>>> totalCt2pea = new ArrayList<>();
			// final List<Entry<CounterTrace, PhaseEventAutomata<CDD>>> complementCt2pea = new ArrayList<>();

			for (Entry<CounterTrace, PhaseEventAutomata<CDD>> pea : ct2pea) {
				PhaseEventAutomata peaToComplement = pea.getValue();
				PEAComplement complementPea = new PEAComplement(peaToComplement, constVars);
				PhaseEventAutomata totalisedPea = complementPea.getTotalisedPEA();

				totalCt2pea.add(new Pair<>(pea.getKey(), totalisedPea));

			}
			mReqPeas.add(new ReqPeas(pattern, totalCt2pea));
		}
		mSymbolTable = builder.constructSymbolTable();
	}

	@Override
	public List<ReqPeas<CDD>> getReqPeas() {
		return mReqPeas;
	}

	@Override
	public IReqSymbolTable getSymboltable() {
		return mSymbolTable;
	}

	@Override
	public Durations getDurations() {
		return mDurations;
	}

	@Override
	public boolean hasErrors() {
		return mHasErrors;
	}

	@Override
	public IReq2PeaAnnotator getAnnotator() {
		return new ReqCheckAnnotator(mServices, mLogger, mReqPeas, mSymbolTable, mDurations);
	}

}