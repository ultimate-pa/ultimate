package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown.RefinementStrategyExceptionBlacklist;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IIpTcStrategyModule;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.StrategyFactory;

public class CougarRefinementStrategy<L extends IIcfgTransition<?>> extends BasicRefinementStrategy<L> {

	public CougarRefinementStrategy(final StrategyFactory<L>.StrategyModuleFactory factory,
			final RefinementStrategyExceptionBlacklist exceptionBlacklist) {
		super(factory, createModules(factory), factory.createIpAbStrategyModuleStraightlineAll(), exceptionBlacklist);
	}

	@SuppressWarnings("unchecked")
	static <L extends IIcfgTransition<?>> IIpTcStrategyModule<?, L>[] createModules(
			final StrategyFactory<L>.StrategyModuleFactory factory) {

		final List<IIpTcStrategyModule<?, L>> rtr = new ArrayList<>();
		rtr.add(factory.createIpTcStrategyModuleZ3(InterpolationTechnique.FPandBPonlyIfFpWasNotPerfect));
		return rtr.toArray(new IIpTcStrategyModule[rtr.size()]);
	}

	private int getCexLength() {
		// TODO get somehow the length of the counterexample
		// assert super.getInterpolantAutomatonBuilder() instanceof IpAbStrategyModuleStraightlineAll;
		// return ((IpAbStrategyModuleStraightlineAll<?>)
		// super.getInterpolantAutomatonBuilder()).getCounterexample().length();
		return 0;
	}

	// We do not interpolate in this strategy
	@Override
	protected boolean needsMoreInterpolants(final List<QualifiedTracePredicates> perfectIpps,
			final List<QualifiedTracePredicates> imperfectIpps) {
		return false;
	}

	// TODO make mFactory accessible
	@Override
	public List<QualifiedTracePredicates> mergeInterpolants(final List<QualifiedTracePredicates> perfectIpps,
			final List<QualifiedTracePredicates> imperfectIpps) {
		final List<QualifiedTracePredicates> defaultIpps = new ArrayList<>();
		final IPredicate pre = null;// mFactory.getDefaultPredicateUnifier().getTruePredicate();
		final IPredicate post = null;// mFactory.getDefaultPredicateUnifier().getFalsePredicate();
		final List<IPredicate> trueSequence = new ArrayList<>();
		for (int i = 0; i < getCexLength(); i++) {
			trueSequence.add(post);
		}
		final TracePredicates trueTraceSequence = new TracePredicates(pre, post, trueSequence);
		final QualifiedTracePredicates naive = new QualifiedTracePredicates(trueTraceSequence, this.getClass(), false);
		defaultIpps.addLast(naive);

		return defaultIpps;
	}

	@Override
	public String getName() {
		return "COUGAR";
		// TODO return RefinementStrategy.COUGAR.toString();
	}

}
