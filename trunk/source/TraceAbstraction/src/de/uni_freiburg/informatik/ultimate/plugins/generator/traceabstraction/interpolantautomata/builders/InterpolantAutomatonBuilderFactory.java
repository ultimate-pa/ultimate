/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarAbsIntRunner;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.HoareTripleChecks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolantConsolidation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckSpWp;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TracePredicates;

/**
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class InterpolantAutomatonBuilderFactory<LETTER extends IIcfgTransition<?>> {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final CfgSmtToolkit mCsToolkit;
	private final PredicateFactoryForInterpolantAutomata mPredicateFactory;
	private final IIcfg<?> mIcfg;
	private final CegarAbsIntRunner<LETTER> mAbsIntRunner;
	private final CegarLoopStatisticsGenerator mBenchmark;

	private final HoareTripleChecks mHoareTripleChecks;
	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;
	private final InterpolationTechnique mInterpolationTechnique;
	private final InterpolantAutomaton mInterpolantAutomatonStyle;

	private final IBuilderFunction<LETTER> mBuilderFunction;

	public InterpolantAutomatonBuilderFactory(final IUltimateServiceProvider services, final CfgSmtToolkit csToolkit,
			final PredicateFactoryForInterpolantAutomata predFac, final IIcfg<?> icfg,
			final CegarAbsIntRunner<LETTER> abstractInterpretationRunner, final TAPreferences taPrefs,
			final InterpolationTechnique interpolation,
			final InterpolantAutomaton interpolantAutomatonConstructionProcedure,
			final CegarLoopStatisticsGenerator benchmark) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mCsToolkit = csToolkit;
		mPredicateFactory = predFac;
		mIcfg = icfg;
		mAbsIntRunner = abstractInterpretationRunner;
		mBenchmark = benchmark;

		// settings
		// interpolation settings is different because of settings fallback
		mInterpolationTechnique = interpolation;
		mInterpolantAutomatonStyle = interpolantAutomatonConstructionProcedure;
		mHoareTripleChecks = taPrefs.getHoareTripleChecks();
		mSimplificationTechnique = taPrefs.getSimplificationTechnique();
		mXnfConversionTechnique = taPrefs.getXnfConversionTechnique();

		mBuilderFunction = determineBuilder(abstractInterpretationRunner, mInterpolantAutomatonStyle);
	}

	private IBuilderFunction<LETTER> determineBuilder(final CegarAbsIntRunner<LETTER> abstractInterpretationRunner,
			final InterpolantAutomaton interpolAutomatonStyle) {
		final IBuilderFunction<LETTER> basicBuilder = determineBuilder(interpolAutomatonStyle);
		if (abstractInterpretationRunner.isDisabled()) {
			return basicBuilder;
		}

		return (abstraction, interpolGenerator, counterexample,
				ipp) -> abstractInterpretationRunner.hasShownInfeasibility()
						? createBuilderAbstractInterpretation(abstraction, interpolGenerator.getPredicateUnifier(),
								counterexample)
						: basicBuilder.create(abstraction, interpolGenerator, counterexample, ipp);
	}

	private IBuilderFunction<LETTER> determineBuilder(final InterpolantAutomaton interpolAutomatonStyle) {
		switch (interpolAutomatonStyle) {
		case CANONICAL:
			return this::createBuilderCanonical;
		case SINGLETRACE:
			return this::createBuilderSingleTrace;
		case TOTALINTERPOLATION2:
			return this::createBuilderTotalInterpolation2;
		case TWOTRACK:
			return this::createBuilderTwoTrack;
		case TOTALINTERPOLATION:
		default:
			throw new IllegalArgumentException("Setting " + interpolAutomatonStyle + " is unsupported");
		}
	}

	public NestedWordAutomaton<LETTER, IPredicate> getResult(final IAutomaton<LETTER, IPredicate> abstraction,
			final IInterpolantGenerator interpolGenerator, final IRun<LETTER, IPredicate, ?> counterexample,
			final List<TracePredicates> ipps) throws AutomataOperationCanceledException {
		return createBuilder(abstraction, interpolGenerator, counterexample, ipps).getResult();
	}

	public IInterpolantAutomatonBuilder<LETTER, IPredicate> createBuilder(
			final IAutomaton<LETTER, IPredicate> abstraction, final IInterpolantGenerator interpolGenerator,
			final IRun<LETTER, IPredicate, ?> counterexample, final List<TracePredicates> ipps)
			throws AutomataOperationCanceledException {
		mBenchmark.start(CegarLoopStatisticsDefinitions.BasicInterpolantAutomatonTime.toString());
		try {
			final IInterpolantAutomatonBuilder<LETTER, IPredicate> builder =
					mBuilderFunction.create(abstraction, interpolGenerator, counterexample, ipps);
			return builder;
		} finally {
			mBenchmark.stop(CegarLoopStatisticsDefinitions.BasicInterpolantAutomatonTime.toString());
		}
	}

	private IInterpolantAutomatonBuilder<LETTER, IPredicate> createBuilderAbstractInterpretation(
			final IAutomaton<LETTER, IPredicate> abstraction, final IPredicateUnifier predicateUnifier,
			final IRun<LETTER, IPredicate, ?> counterexample) {
		return mAbsIntRunner.createInterpolantAutomatonBuilder(predicateUnifier,
				(INestedWordAutomaton<LETTER, IPredicate>) abstraction, counterexample);
	}

	private IInterpolantAutomatonBuilder<LETTER, IPredicate> createBuilderCanonical(
			final IAutomaton<LETTER, IPredicate> abstraction, final IInterpolantGenerator interpolGenerator,
			final IRun<LETTER, IPredicate, ?> counterexample, final List<TracePredicates> ipps) {
		if (ipps.isEmpty()) {
			throw new IllegalArgumentException("Need at least one sequence of interpolants.");
		}
		// use the first sequence of interpolants
		final TracePredicates ipp = ipps.get(0);

		@SuppressWarnings("unchecked")
		final CanonicalInterpolantAutomatonBuilder<? extends Object, LETTER> iab =
				new CanonicalInterpolantAutomatonBuilder<>(mServices, ipp, counterexample.getStateSequence(),
						new VpAlphabet<>(abstraction), mCsToolkit, mPredicateFactory, mLogger,
						interpolGenerator.getPredicateUnifier(), (NestedWord<LETTER>) interpolGenerator.getTrace());
		iab.analyze();
		mLogger.info("Interpolants " + iab.getResult().getStates());
		final BackwardCoveringInformation bci = TraceCheckUtils.computeCoverageCapability(mServices, ipp,
				TraceCheckUtils.getSequenceOfProgramPoints(NestedWord.nestedWord(counterexample.getWord())), mLogger,
				interpolGenerator.getPredicateUnifier());
		mBenchmark.addBackwardCoveringInformation(bci);
		return iab;
	}

	private IInterpolantAutomatonBuilder<LETTER, IPredicate> createBuilderSingleTrace(
			final IAutomaton<LETTER, IPredicate> abstraction, final IInterpolantGenerator interpolGenerator,
			final IRun<LETTER, IPredicate, ?> counterexample, final List<TracePredicates> ipps) {
		final StraightLineInterpolantAutomatonBuilder<LETTER> iab = new StraightLineInterpolantAutomatonBuilder<>(
				mServices, new VpAlphabet<>(abstraction), interpolGenerator, mPredicateFactory,
				StraightLineInterpolantAutomatonBuilder.InitialAndAcceptingStateMode.ONLY_FIRST_INITIAL_LAST_ACCEPTING);
		return iab;
	}

	private IInterpolantAutomatonBuilder<LETTER, IPredicate> createBuilderTotalInterpolation2(
			final IAutomaton<LETTER, IPredicate> abstraction, final IInterpolantGenerator interpolGenerator,
			final IRun<LETTER, IPredicate, ?> counterexample, final List<TracePredicates> ipps)
			throws AutomataOperationCanceledException {
		final INestedWordAutomaton<LETTER, IPredicate> castedAbstraction =
				(INestedWordAutomaton<LETTER, IPredicate>) abstraction;
		@SuppressWarnings("unchecked")
		final NestedRun<LETTER, IPredicate> castedCex = (NestedRun<LETTER, IPredicate>) counterexample;
		final TotalInterpolationAutomatonBuilder<LETTER> iab = new TotalInterpolationAutomatonBuilder<>(
				castedAbstraction, castedCex.getStateSequence(), interpolGenerator, mCsToolkit, mPredicateFactory,
				mCsToolkit.getModifiableGlobalsTable(), mInterpolationTechnique, mServices, mHoareTripleChecks,
				mSimplificationTechnique, mXnfConversionTechnique, mIcfg.getCfgSmtToolkit().getSymbolTable());
		mBenchmark.addTotalInterpolationData(iab.getTotalInterpolationBenchmark());
		return iab;
	}

	private IInterpolantAutomatonBuilder<LETTER, IPredicate> createBuilderTwoTrack(
			final IAutomaton<LETTER, IPredicate> abstraction, final IInterpolantGenerator interpolGenerator,
			final IRun<LETTER, IPredicate, ?> counterexample, final List<TracePredicates> ipps)
			throws AutomataOperationCanceledException {
		if (!(interpolGenerator instanceof TraceCheckSpWp)
				&& !(interpolGenerator instanceof InterpolantConsolidation)) {
			throw new AssertionError("TWOTRACK only for traceCheckSpWp or InterpolantConsolidation");
		}
		final List<IPredicate> predicatesA;
		final List<IPredicate> predicatesB;
		boolean build2TrackAutomaton = false;
		if (interpolGenerator instanceof TraceCheckSpWp) {
			final TraceCheckSpWp traceCheck = (TraceCheckSpWp) interpolGenerator;
			predicatesA = traceCheck.getForwardPredicates();
			predicatesB = traceCheck.getBackwardPredicates();
			build2TrackAutomaton = true;
		} else if (!((InterpolantConsolidation<?>) interpolGenerator).consolidationSuccessful()) {
			// if consolidation wasn't successful, then build a 2-Track-Automaton
			final InterpolantConsolidation<?> ic = (InterpolantConsolidation<?>) interpolGenerator;
			predicatesA = ic.getInterpolantsOfType_I();
			predicatesB = ic.getInterpolantsOfType_II();
			build2TrackAutomaton = true;
		} else {
			predicatesA = null;
			predicatesB = null;
		}
		if (build2TrackAutomaton) {
			final TwoTrackInterpolantAutomatonBuilder<LETTER> ttiab = new TwoTrackInterpolantAutomatonBuilder<>(
					mServices, counterexample, mCsToolkit, predicatesA, predicatesB,
					interpolGenerator.getPrecondition(), interpolGenerator.getPostcondition(), abstraction);
			return ttiab;
		}
		// Case of Canonical_Automaton, i.e. if the consolidation was successful
		// FIXME: The case TWOTRACK from the switch is not nice. Should be refactored!
		return createBuilderCanonical(abstraction, interpolGenerator, counterexample, ipps);
	}

	@FunctionalInterface
	private interface IBuilderFunction<LETTER> {
		IInterpolantAutomatonBuilder<LETTER, IPredicate> create(final IAutomaton<LETTER, IPredicate> abstraction,
				final IInterpolantGenerator interpolGenerator, final IRun<LETTER, IPredicate, ?> counterexample,
				final List<TracePredicates> ipps) throws AutomataOperationCanceledException;
	}
}
