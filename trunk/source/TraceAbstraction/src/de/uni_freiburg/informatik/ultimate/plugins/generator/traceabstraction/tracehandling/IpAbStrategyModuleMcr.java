package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import java.util.Collections;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.mcr.IInterpolantProvider;
import de.uni_freiburg.informatik.ultimate.lib.mcr.McrAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsAggregator;

/**
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class IpAbStrategyModuleMcr<LETTER extends IIcfgTransition<?>> implements IIpAbStrategyModule<LETTER> {
	private final McrAutomatonBuilder<LETTER> mAutomatonBuilder;
	private IpAbStrategyModuleResult<LETTER> mResult;
	private final List<LETTER> mTrace;
	private final IInterpolantProvider<LETTER> mInterpolantProvider;

	public IpAbStrategyModuleMcr(final List<LETTER> trace, final IPredicateUnifier predicateUnifier,
			final IEmptyStackStateFactory<IPredicate> emptyStackFactory, final IUltimateServiceProvider services,
			final ILogger logger, final Set<LETTER> alphabet, final IInterpolantProvider<LETTER> interpolantProvider) {
		mAutomatonBuilder = new McrAutomatonBuilder<>(trace, predicateUnifier, emptyStackFactory, logger,
				new VpAlphabet<>(alphabet), services);
		mTrace = trace;
		mInterpolantProvider = interpolantProvider;
	}

	@Override
	public IpAbStrategyModuleResult<LETTER> buildInterpolantAutomaton(final List<QualifiedTracePredicates> perfectIpps,
			final List<QualifiedTracePredicates> imperfectIpps) throws AutomataOperationCanceledException {
		if (mResult == null) {
			try {
				final QualifiedTracePredicates tracePredicate =
						perfectIpps.isEmpty() ? imperfectIpps.get(0) : perfectIpps.get(0);
				final NestedWordAutomaton<LETTER, IPredicate> ipAutomaton = mAutomatonBuilder
						.buildInterpolantAutomaton(mTrace, tracePredicate.getPredicates(), mInterpolantProvider);
				return new IpAbStrategyModuleResult<>(ipAutomaton, Collections.singletonList(tracePredicate));
			} catch (final AutomataLibraryException e) {
				throw new RuntimeException(e);
			}
		}
		return mResult;
	}

	@Override
	public void aggregateStatistics(final StatisticsAggregator statistics) {
		// McrAutomatonBuilder does not have statistics
	}
}
