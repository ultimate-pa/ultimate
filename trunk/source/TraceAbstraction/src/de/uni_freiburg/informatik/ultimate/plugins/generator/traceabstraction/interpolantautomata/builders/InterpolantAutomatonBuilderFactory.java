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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.interpolant.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.interpolant.TracePredicates;
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
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckUtils;

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
	private final boolean mCollectInterpolantStatistics;

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
		mCollectInterpolantStatistics = taPrefs.collectInterpolantStatistics();

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
		case STRAIGHT_LINE:
			return this::createBuilderStraightLine;
		case CANONICAL:
			return this::createBuilderCanonical;
		case TOTALINTERPOLATION2:
			return this::createBuilderTotalInterpolation2;
		case TOTALINTERPOLATION:
		default:
			throw new IllegalArgumentException("Setting " + interpolAutomatonStyle + " is unsupported");
		}
	}

	public NestedWordAutomaton<LETTER, IPredicate> getResult(final IAutomaton<LETTER, IPredicate> abstraction,
			final IInterpolantGenerator<LETTER> interpolGenerator, final IRun<LETTER, IPredicate, ?> counterexample,
			final List<TracePredicates> ipps) throws AutomataOperationCanceledException {
		return createBuilder(abstraction, interpolGenerator, counterexample, ipps).getResult();
	}

	public IInterpolantAutomatonBuilder<LETTER, IPredicate> createBuilder(
			final IAutomaton<LETTER, IPredicate> abstraction, final IInterpolantGenerator<LETTER> interpolGenerator,
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

	private IInterpolantAutomatonBuilder<LETTER, IPredicate> createBuilderStraightLine(
			final IAutomaton<LETTER, IPredicate> abstraction, final IInterpolantGenerator<LETTER> interpolGenerator,
			final IRun<LETTER, IPredicate, ?> counterexample, final List<TracePredicates> ipps) {
		final StraightLineInterpolantAutomatonBuilder<LETTER> iab = new StraightLineInterpolantAutomatonBuilder<>(mServices,
				counterexample.getWord(), NestedWordAutomataUtils.getVpAlphabet(abstraction), ipps, mPredicateFactory,
				StraightLineInterpolantAutomatonBuilder.InitialAndAcceptingStateMode.ONLY_FIRST_INITIAL_ONLY_FALSE_ACCEPTING);
		return iab;
	}

	private IInterpolantAutomatonBuilder<LETTER, IPredicate> createBuilderAbstractInterpretation(
			final IAutomaton<LETTER, IPredicate> abstraction, final IPredicateUnifier predicateUnifier,
			final IRun<LETTER, IPredicate, ?> counterexample) {
		return mAbsIntRunner.createInterpolantAutomatonBuilder(predicateUnifier,
				(INestedWordAutomaton<LETTER, IPredicate>) abstraction, counterexample, mPredicateFactory);
	}

	private IInterpolantAutomatonBuilder<LETTER, IPredicate> createBuilderCanonical(
			final IAutomaton<LETTER, IPredicate> abstraction, final IInterpolantGenerator<LETTER> interpolGenerator,
			final IRun<LETTER, IPredicate, ?> counterexample, final List<TracePredicates> ipps) {
		if (ipps.isEmpty()) {
			throw new IllegalArgumentException("Need at least one sequence of interpolants.");
		}
		// use the first sequence of interpolants
		final TracePredicates ipp = ipps.get(0);
		if (ipps.size() > 1) {
			mLogger.warn("Throwing away all your interpolant sequences but the first");
		}

		final CanonicalInterpolantAutomatonBuilder<? extends Object, LETTER> iab =
				new CanonicalInterpolantAutomatonBuilder<>(mServices, ipp, counterexample.getStateSequence(),
						NestedWordAutomataUtils.getVpAlphabet(abstraction), mCsToolkit, mPredicateFactory, mLogger,
						interpolGenerator.getPredicateUnifier(),
						TraceCheckUtils.toNestedWord(interpolGenerator.getTrace()));
		iab.analyze();
		mLogger.info("Interpolants " + iab.getResult().getStates());
		final BackwardCoveringInformation bci = TraceCheckUtils.computeCoverageCapability(mServices, ipp,
				TraceCheckUtils.getSequenceOfProgramPoints(NestedWord.nestedWord(counterexample.getWord())), mLogger,
				interpolGenerator.getPredicateUnifier());
		mBenchmark.addBackwardCoveringInformation(bci);
		return iab;
	}

	private IInterpolantAutomatonBuilder<LETTER, IPredicate> createBuilderTotalInterpolation2(
			final IAutomaton<LETTER, IPredicate> abstraction, final IInterpolantGenerator<LETTER> interpolGenerator,
			final IRun<LETTER, IPredicate, ?> counterexample, final List<TracePredicates> ipps)
			throws AutomataOperationCanceledException {
		final INestedWordAutomaton<LETTER, IPredicate> castedAbstraction =
				(INestedWordAutomaton<LETTER, IPredicate>) abstraction;
		@SuppressWarnings("unchecked")
		final NestedRun<LETTER, IPredicate> castedCex = (NestedRun<LETTER, IPredicate>) counterexample;
		final TotalInterpolationAutomatonBuilder<LETTER> iab = new TotalInterpolationAutomatonBuilder<>(
				castedAbstraction, castedCex, interpolGenerator, mCsToolkit, mPredicateFactory,
				mCsToolkit.getModifiableGlobalsTable(), mInterpolationTechnique, mServices, mHoareTripleChecks,
				mSimplificationTechnique, mXnfConversionTechnique, mIcfg.getCfgSmtToolkit().getSymbolTable(),
				mCollectInterpolantStatistics);
		mBenchmark.addTotalInterpolationData(iab.getTotalInterpolationBenchmark());
		return iab;
	}

	@FunctionalInterface
	private interface IBuilderFunction<LETTER extends IAction> {
		IInterpolantAutomatonBuilder<LETTER, IPredicate> create(final IAutomaton<LETTER, IPredicate> abstraction,
				final IInterpolantGenerator<LETTER> interpolGenerator, final IRun<LETTER, IPredicate, ?> counterexample,
				final List<TracePredicates> ipps) throws AutomataOperationCanceledException;
	}
}
