package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import java.util.List;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.IInterpolatingTraceCheck;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

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
			final NestedWordAutomaton<LETTER, IPredicate> automaton = mIpTcSmMCR.getOrConstruct().getAutomaton();
			// TODO: What to use as interpolants? The interpolants (=states) used by automaton?
			mResult = new IpAbStrategyModuleResult<>(automaton, null);
		}
		return mResult;
	}
}
