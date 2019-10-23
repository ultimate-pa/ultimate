package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import java.util.List;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.lib.mcr.MCR;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.IInterpolatingTraceCheck;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.TracePredicates;

public class IpAbStrategyModuleMCR<T extends IInterpolatingTraceCheck<LETTER>, LETTER extends IIcfgTransition<?>>
		implements IIpAbStrategyModule<LETTER> {

	private final IpTcStrategyModuleMCR<T, LETTER> mIpTcSmMCR;
	private IpAbStrategyModuleResult<LETTER> mResult;

	public IpAbStrategyModuleMCR(final IpTcStrategyModuleMCR<T, LETTER> ipTcSmMCR) {
		mIpTcSmMCR = ipTcSmMCR;
	}

	@Override
	public IpAbStrategyModuleResult<LETTER> buildInterpolantAutomaton(final List<QualifiedTracePredicates> perfectIpps,
			final List<QualifiedTracePredicates> imperfectIpps) throws AutomataOperationCanceledException {
		if (mResult == null) {
			final MCR<LETTER> mcr = mIpTcSmMCR.getOrConstruct();
			// TODO: Are these all predicates?
			final List<QualifiedTracePredicates> predicates = mcr.getTraceChecks().stream()
					.map(t -> new QualifiedTracePredicates(new TracePredicates(t), t.getClass(), t.isPerfectSequence()))
					.collect(Collectors.toList());
			mResult = new IpAbStrategyModuleResult<>(mcr.getAutomaton(), predicates);
		}
		return mResult;
	}
}
