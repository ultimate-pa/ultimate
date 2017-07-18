package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.interactive;

import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarAbsIntRunner;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PathProgramCache;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interactive.InteractiveCegar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.IRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.RefinementStrategyFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TaCheckAndRefinementPreferences;

public class InteractiveRefinementStrategyFactory<LETTER extends IIcfgTransition<?>>
		extends RefinementStrategyFactory<LETTER> {

	private final InteractiveCegar mInteractive;

	public InteractiveRefinementStrategyFactory(final ILogger logger, final IUltimateServiceProvider services,
			final IToolchainStorage storage, final InteractiveCegar interactive,
			final TAPreferences taPrefsForInterpolantConsolidation, final TaCheckAndRefinementPreferences<LETTER> prefs,
			final CegarAbsIntRunner<LETTER> absIntRunner, final IIcfg<?> initialIcfg,
			final PredicateFactory predicateFactory, final PathProgramCache<LETTER> pathProgramCache) {
		super(logger, services, storage, taPrefsForInterpolantConsolidation, prefs, absIntRunner, initialIcfg,
				predicateFactory, pathProgramCache);
		mInteractive = interactive;
		assert mInteractive != null;
		assert mInteractive.isInteractiveMode();
	}

	@Override
	public IRefinementStrategy<LETTER> createStrategy(final RefinementStrategy strategy,
			final IRun<LETTER, IPredicate, ?> counterexample, final IAutomaton<LETTER, IPredicate> abstraction,
			final int iteration, final CegarLoopStatisticsGenerator benchmark) {
		final PredicateUnifier predicateUnifier = getNewPredicateUnifier();

		final Function<RefinementStrategy, IRefinementStrategy<LETTER>> fallBack =
				s -> super.createStrategy(s, counterexample, abstraction, iteration, benchmark);

		return new ParrotRefinementStrategy<LETTER>(mLogger, mPrefs, mServices, mInitialIcfg.getCfgSmtToolkit(),
				mPredicateFactory, predicateUnifier, mAssertionOrderModulation, counterexample, abstraction,
				mPrefsConsolidation, iteration, benchmark) {
			@Override
			protected InteractiveCegar getInteractive() {
				// instead of passing the interactive interface via
				// constructor, it is necessary to have a getter
				// because .next() is called in the constructor of the
				// superclass.
				return mInteractive;
			}

			@Override
			protected IRefinementStrategy<LETTER> createFallbackStrategy(final RefinementStrategy strategy) {
				return fallBack.apply(strategy);
			}
		};
	}
}
