package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import java.util.List;
import java.util.NoSuchElementException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.mcr.MCR;
import de.uni_freiburg.informatik.ultimate.lib.mcr.MCR.ITraceCheckFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheck;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown.RefinementStrategyExceptionBlacklist;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAbstractionUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.IInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.HoareTripleChecks;

/**
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class McrRefinementStrategy<LETTER extends IIcfgTransition<?>> extends BaseRefinementStrategy<LETTER>
		implements ITraceCheckFactory<LETTER> {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final TaCheckAndRefinementPreferences<LETTER> mPrefs;
	private final IRun<LETTER, IPredicate, ?> mCounterexample;
	private final IPredicate mPrecondition;
	private final PredicateFactory mPredicateFactory;
	private final IPredicateUnifier mPredicateUnifier;

	// TODO Christian 2016-11-11: Matthias wants to get rid of this
	private final TAPreferences mTaPrefsForInterpolantConsolidation;

	private MCR<LETTER> mMCR;
	private IInterpolantGenerator<LETTER> mInterpolantGenerator;
	private final RefinementEngineStatisticsGenerator mRefinementEngineStatisticsGenerator;
	private final ManagedScript mManagedScript;
	private final TaskIdentifier mTaskIdentifier;
	// private final McrRefinementStrategy<LETTER>.TraceCheckSupplier mTraceCheckSupplier;

	/**
	 * @param prefs
	 *            Preferences. pending contexts
	 * @param managedScript
	 *            managed script
	 * @param services
	 *            Ultimate services
	 * @param predicateUnifier
	 *            predicate unifier
	 * @param counterexample
	 *            counterexample trace
	 * @param logger
	 *            logger
	 * @param abstraction
	 *            abstraction
	 * @param taPrefsForInterpolantConsolidation
	 *            temporary argument, should be removed
	 * @param cegarLoopBenchmarks
	 *            benchmark
	 */
	public McrRefinementStrategy(final ILogger logger, final TaCheckAndRefinementPreferences<LETTER> prefs,
			final ManagedScript managedScript, final IUltimateServiceProvider services,
			final PredicateFactory predicateFactory, final IPredicateUnifier predicateUnifier,
			final IRun<LETTER, IPredicate, ?> counterexample, final IPredicate precondition,
			final IAutomaton<LETTER, IPredicate> abstraction, final TAPreferences taPrefsForInterpolantConsolidation,
			final TaskIdentifier taskIdentifier, final IEmptyStackStateFactory<IPredicate> emptyStackFactory) {
		super(logger, emptyStackFactory);
		mServices = services;
		mLogger = logger;
		mPrefs = prefs;
		mCounterexample = counterexample;
		mPrecondition = precondition;
		mPredicateFactory = predicateFactory;
		mPredicateUnifier = predicateUnifier;
		mTaPrefsForInterpolantConsolidation = taPrefsForInterpolantConsolidation;
		mManagedScript = managedScript;
		mTaskIdentifier = taskIdentifier;
		mRefinementEngineStatisticsGenerator = new RefinementEngineStatisticsGenerator();
	}

	@Override
	public boolean hasNextTraceCheck() {
		return false;
	}

	@Override
	public void nextTraceCheck() {
		throw new NoSuchElementException("This strategy has only one element.");
	}

	@Override
	public ITraceCheck getTraceCheck() {
		return constructMCR();
	}

	private MCR<LETTER> constructMCR() {
		if (mMCR == null) {
			final IHoareTripleChecker htc = TraceAbstractionUtils.constructEfficientHoareTripleCheckerWithCaching(
					mServices, HoareTripleChecks.MONOLITHIC, mPrefs.getCfgSmtToolkit(), mPredicateUnifier);
			mMCR = new MCR<>(mLogger, mPrefs, mPredicateUnifier, htc, mCounterexample.getWord().asList(), this);
			mRefinementEngineStatisticsGenerator.addTraceCheckStatistics(mMCR);
		}
		return mMCR;
	}

	@Override
	public boolean hasNextInterpolantGenerator(final List<TracePredicates> perfectIpps,
			final List<TracePredicates> imperfectIpps) {
		return false;
	}

	@Override
	public void nextInterpolantGenerator() {
		throw new NoSuchElementException("This strategy has only one element.");
	}

	@Override
	public IInterpolantGenerator<LETTER> getInterpolantGenerator() {
		if (mInterpolantGenerator == null) {
			mInterpolantGenerator = RefinementStrategyUtils.constructInterpolantGenerator(mServices, mLogger, mPrefs,
					mTaPrefsForInterpolantConsolidation, getTraceCheck(), mPredicateFactory, mPredicateUnifier,
					mCounterexample, mPrecondition, mRefinementEngineStatisticsGenerator);
		}
		return mInterpolantGenerator;
	}

	@Override
	public IInterpolantAutomatonBuilder<LETTER, IPredicate> getInterpolantAutomatonBuilder(
			final List<TracePredicates> perfectIpps, final List<TracePredicates> imperfectIpps) {
		return new IInterpolantAutomatonBuilder<LETTER, IPredicate>() {
			@Override
			public NestedWordAutomaton<LETTER, IPredicate> getResult() {
				// TODO: What to do with perfectIpps and imperfectIpps?
				return constructMCR().getAutomaton();
			}
		};
	}

	@Override
	public IPredicateUnifier getPredicateUnifier() {
		return mPredicateUnifier;
	}

	@Override
	public RefinementStrategyExceptionBlacklist getExceptionBlacklist() {
		return mPrefs.getExceptionBlacklist();
	}

	@Override
	public RefinementEngineStatisticsGenerator getRefinementEngineStatistics() {
		return mRefinementEngineStatisticsGenerator;
	}

	@Override
	public ITraceCheck getTraceCheck(final List<LETTER> trace) {
		// TODO: How to get an IRun from a trace? Construct a dummy-run?
		final IRun<LETTER, IPredicate, ?> counterexample = null;
		final TraceCheckConstructor<LETTER> tcConstructor =
				new TraceCheckConstructor<>(mPrefs, mManagedScript, mServices, mPredicateFactory, mPredicateUnifier,
						counterexample, mPrecondition, mPrefs.getInterpolationTechnique(), mTaskIdentifier);
		return tcConstructor.get();
	}
}
