package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.strategy;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown.RefinementStrategyExceptionBlacklist;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IIpTcStrategyModule;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.StrategyFactory;

public class SmtInterpolSleepSetPORRefinementStrategy<L extends IIcfgTransition<?>> extends BasicRefinementStrategy<L> {

	@SuppressWarnings("unchecked")
	public SmtInterpolSleepSetPORRefinementStrategy(final StrategyFactory<L>.StrategyModuleFactory factory,
			final RefinementStrategyExceptionBlacklist exceptionBlacklist) {
		super(factory,
				new IIpTcStrategyModule[] {
						factory.createIpTcStrategyModuleSmtInterpolCraigSleepSetPOR(
								InterpolationTechnique.Craig_NestedInterpolation)/*,
						factory.createIpTcStrategyModuleSmtInterpolSpWp(InterpolationTechnique.ForwardPredicates)*/ },
				factory.createIpAbStrategyModuleStraightlineAll(), exceptionBlacklist);
	}

	@Override
	public String getName() {
		return RefinementStrategy.SMTINTERPOL.toString();
	}
}