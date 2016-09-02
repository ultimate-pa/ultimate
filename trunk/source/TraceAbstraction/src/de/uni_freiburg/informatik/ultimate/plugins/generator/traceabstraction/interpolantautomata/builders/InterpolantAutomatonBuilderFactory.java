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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.InCaReAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplicationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractInterpretationRunner;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.HoareTripleChecks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.InterpolantConsolidation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerSpWp;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerUtils;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class InterpolantAutomatonBuilderFactory {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final SmtManager mSmtManager;
	private final PredicateFactoryForInterpolantAutomata mPredicateFactory;
	private final RootNode mRootNode;
	private final AbstractInterpretationRunner mAbsIntRunner;
	private final CegarLoopStatisticsGenerator mBenchmark;

	private final HoareTripleChecks mHoareTripleChecks;
	private final SimplicationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;
	private final InterpolationTechnique mInterpolationTechnique;
	private final InterpolantAutomaton mInterpolantAutomatonStyle;

	private final IBuilderFunction mBuilderFunction;

	public InterpolantAutomatonBuilderFactory(final IUltimateServiceProvider services, final SmtManager smtManager,
			final PredicateFactoryForInterpolantAutomata predFac, final RootNode rootNode,
			final AbstractInterpretationRunner abstractInterpretationRunner, final TAPreferences taPrefs,
			final InterpolationTechnique interpolation,
			final InterpolantAutomaton interpolantAutomatonConstructionProcedure,
			final CegarLoopStatisticsGenerator benchmark) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mSmtManager = smtManager;
		mPredicateFactory = predFac;
		mRootNode = rootNode;
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

	private IBuilderFunction determineBuilder(final AbstractInterpretationRunner abstractInterpretationRunner,
			final InterpolantAutomaton interpolAutomatonStyle) {
		final IBuilderFunction basicBuilder = determineBuilder(interpolAutomatonStyle);
		if (abstractInterpretationRunner.isDisabled()) {
			return basicBuilder;
		}

		return (abstraction, interpolGenerator, counterexample) -> abstractInterpretationRunner.hasShownInfeasibility()
				? createBuilderAbstractInterpretation(abstraction, interpolGenerator, counterexample)
				: basicBuilder.create(abstraction, interpolGenerator, counterexample);
	}

	private IBuilderFunction determineBuilder(final InterpolantAutomaton interpolAutomatonStyle) {
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

	public NestedWordAutomaton<CodeBlock, IPredicate> getResult(final IAutomaton<CodeBlock, IPredicate> abstraction,
			final IInterpolantGenerator interpolGenerator, final IRun<CodeBlock, IPredicate> counterexample)
			throws AutomataOperationCanceledException {
		return createBuilder(abstraction, interpolGenerator, counterexample).getResult();
	}

	public IInterpolantAutomatonBuilder<CodeBlock, IPredicate> createBuilder(
			final IAutomaton<CodeBlock, IPredicate> abstraction, final IInterpolantGenerator interpolGenerator,
			final IRun<CodeBlock, IPredicate> counterexample) throws AutomataOperationCanceledException {
		mBenchmark.start(CegarLoopStatisticsDefinitions.BasicInterpolantAutomatonTime.toString());
		final IInterpolantAutomatonBuilder<CodeBlock, IPredicate> builder =
				mBuilderFunction.create(abstraction, interpolGenerator, counterexample);
		mBenchmark.stop(CegarLoopStatisticsDefinitions.BasicInterpolantAutomatonTime.toString());
		return builder;
	}

	private IInterpolantAutomatonBuilder<CodeBlock, IPredicate> createBuilderAbstractInterpretation(
			final IAutomaton<CodeBlock, IPredicate> abstraction, final IInterpolantGenerator interpolGenerator,
			final IRun<CodeBlock, IPredicate> counterexample) {
		return mAbsIntRunner.createInterpolantAutomatonBuilder(interpolGenerator,
				(INestedWordAutomaton<CodeBlock, IPredicate>) abstraction, counterexample);
	}

	private IInterpolantAutomatonBuilder<CodeBlock, IPredicate> createBuilderCanonical(
			final IAutomaton<CodeBlock, IPredicate> abstraction, final IInterpolantGenerator interpolGenerator,
			final IRun<CodeBlock, IPredicate> counterexample) {
		final List<ProgramPoint> programPoints = CoverageAnalysis.extractProgramPoints(counterexample);
		final CanonicalInterpolantAutomatonBuilder iab =
				new CanonicalInterpolantAutomatonBuilder(mServices, interpolGenerator, programPoints,
						new InCaReAlphabet<CodeBlock>(abstraction), mSmtManager, mPredicateFactory, mLogger);
		iab.analyze();
		mLogger.info("Interpolants " + iab.getResult().getStates());
		final BackwardCoveringInformation bci =
				TraceCheckerUtils.computeCoverageCapability(mServices, interpolGenerator, programPoints, mLogger);
		mBenchmark.addBackwardCoveringInformation(bci);
		return iab;
	}

	private IInterpolantAutomatonBuilder<CodeBlock, IPredicate> createBuilderSingleTrace(
			final IAutomaton<CodeBlock, IPredicate> abstraction, final IInterpolantGenerator interpolGenerator,
			final IRun<CodeBlock, IPredicate> counterexample) {
		final StraightLineInterpolantAutomatonBuilder iab = new StraightLineInterpolantAutomatonBuilder(mServices,
				new InCaReAlphabet<CodeBlock>(abstraction), interpolGenerator, mPredicateFactory);
		return iab;
	}

	private IInterpolantAutomatonBuilder<CodeBlock, IPredicate> createBuilderTotalInterpolation2(
			final IAutomaton<CodeBlock, IPredicate> abstraction, final IInterpolantGenerator interpolGenerator,
			final IRun<CodeBlock, IPredicate> counterexample) throws AutomataOperationCanceledException {
		final INestedWordAutomaton<CodeBlock, IPredicate> castedAbstraction =
				(INestedWordAutomaton<CodeBlock, IPredicate>) abstraction;
		final NestedRun<CodeBlock, IPredicate> castedCex = (NestedRun<CodeBlock, IPredicate>) counterexample;
		final TotalInterpolationAutomatonBuilder iab = new TotalInterpolationAutomatonBuilder(castedAbstraction,
				castedCex.getStateSequence(), interpolGenerator, mSmtManager, mPredicateFactory,
				mRootNode.getRootAnnot().getModGlobVarManager(), mInterpolationTechnique, mServices, mHoareTripleChecks,
				mSimplificationTechnique, mXnfConversionTechnique);
		mBenchmark.addTotalInterpolationData(iab.getTotalInterpolationBenchmark());
		return iab;
	}

	private IInterpolantAutomatonBuilder<CodeBlock, IPredicate> createBuilderTwoTrack(
			final IAutomaton<CodeBlock, IPredicate> abstraction, final IInterpolantGenerator interpolGenerator,
			final IRun<CodeBlock, IPredicate> counterexample) throws AutomataOperationCanceledException {
		if (!(interpolGenerator instanceof TraceCheckerSpWp)
				&& !(interpolGenerator instanceof InterpolantConsolidation)) {
			throw new AssertionError("TWOTRACK only for TraceCheckerSpWp or InterpolantConsolidation");
		}
		final List<IPredicate> predicatesA;
		final List<IPredicate> predicatesB;
		boolean build2TrackAutomaton = false;
		if (interpolGenerator instanceof TraceCheckerSpWp) {
			final TraceCheckerSpWp traceChecker = (TraceCheckerSpWp) interpolGenerator;
			predicatesA = traceChecker.getForwardPredicates();
			predicatesB = traceChecker.getBackwardPredicates();
			build2TrackAutomaton = true;
		} else if (!((InterpolantConsolidation) interpolGenerator).consolidationSuccessful()) {
			// if consolidation wasn't successful, then build a 2-Track-Automaton
			final InterpolantConsolidation ic = (InterpolantConsolidation) interpolGenerator;
			predicatesA = ic.getInterpolantsOfType_I();
			predicatesB = ic.getInterpolantsOfType_II();
			build2TrackAutomaton = true;
		} else {
			predicatesA = null;
			predicatesB = null;
		}
		if (build2TrackAutomaton) {
			final TwoTrackInterpolantAutomatonBuilder ttiab = new TwoTrackInterpolantAutomatonBuilder(mServices,
					counterexample, mSmtManager, predicatesA, predicatesB, interpolGenerator.getPrecondition(),
					interpolGenerator.getPostcondition(), abstraction);
			return ttiab;
		} else {
			// Case of Canonical_Automaton, i.e. if the consolidation was successful
			// FIXME: The case TWOTRACK from the switch is not nice. Should be refactored!
			return createBuilderCanonical(abstraction, interpolGenerator, counterexample);
		}
	}

	@FunctionalInterface
	private interface IBuilderFunction {
		IInterpolantAutomatonBuilder<CodeBlock, IPredicate> create(final IAutomaton<CodeBlock, IPredicate> abstraction,
				final IInterpolantGenerator interpolGenerator, final IRun<CodeBlock, IPredicate> counterexample)
				throws AutomataOperationCanceledException;
	}
}
