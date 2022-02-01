/*
 * Copyright (C) 2019 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2019 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.IIpAbStrategyModule.IpAbStrategyModuleResult;

/**
 * Checks a trace for feasibility and, if infeasible, constructs an interpolant automaton.
 *
 * This class is used in the {@link BasicCegarLoop}.
 *
 * @see IRefinementStrategy
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public final class TraceAbstractionRefinementEngine<L extends IIcfgTransition<?>>
		implements IRefinementEngine<L, NestedWordAutomaton<L, IPredicate>> {

	private final ILogger mLogger;
	private final IRefinementStrategy<L> mStrategy;
	private final AutomatonFreeRefinementEngine<L> mAutomatonFreeEngine;

	private NestedWordAutomaton<L, IPredicate> mInterpolantAutomaton;
	private List<QualifiedTracePredicates> mUsedTracePredicates;

	public TraceAbstractionRefinementEngine(final ILogger logger, final IRefinementStrategy<L> strategy) {
		mLogger = logger;
		mStrategy = strategy;
		mAutomatonFreeEngine = new AutomatonFreeRefinementEngine<>(logger, strategy);
		generateProof();
	}

	@Override
	public LBool getCounterexampleFeasibility() {
		return mAutomatonFreeEngine.getCounterexampleFeasibility();
	}

	@Override
	public NestedWordAutomaton<L, IPredicate> getInfeasibilityProof() {
		if (mInterpolantAutomaton == null) {
			throw new IllegalStateException(
					"There is no proof because counterexample was " + getCounterexampleFeasibility());
		}
		return mInterpolantAutomaton;
	}

	@Override
	public boolean somePerfectSequenceFound() {
		return mAutomatonFreeEngine.somePerfectSequenceFound();
	}

	@Override
	public boolean providesIcfgProgramExecution() {
		return mAutomatonFreeEngine.providesIcfgProgramExecution();
	}

	@Override
	public IProgramExecution<L, Term> getIcfgProgramExecution() {
		return mAutomatonFreeEngine.getIcfgProgramExecution();
	}

	@Override
	public List<QualifiedTracePredicates> getUsedTracePredicates() {
		return mUsedTracePredicates;
	}

	@Override
	public IHoareTripleChecker getHoareTripleChecker() {
		return mAutomatonFreeEngine.getHoareTripleChecker();
	}

	@Override
	public IPredicateUnifier getPredicateUnifier() {
		return mAutomatonFreeEngine.getPredicateUnifier();
	}

	@Override
	public RefinementEngineStatisticsGenerator getRefinementEngineStatistics() {
		return mAutomatonFreeEngine.getRefinementEngineStatistics();
	}

	private void generateProof() {
		final LBool cexResult = mAutomatonFreeEngine.getCounterexampleFeasibility();
		if (cexResult != LBool.UNSAT) {
			mInterpolantAutomaton = null;
			mUsedTracePredicates = null;
			return;
		}
		final Collection<QualifiedTracePredicates> ipps = mAutomatonFreeEngine.getInfeasibilityProof();
		final IIpAbStrategyModule<L> interpolantAutomatonBuilder = mStrategy.getInterpolantAutomatonBuilder();
		logModule("Using interpolant automaton builder", interpolantAutomatonBuilder);
		try {

			final List<QualifiedTracePredicates> perfectIpps =
					ipps.stream().filter(a -> a.isPerfect()).collect(Collectors.toList());
			final List<QualifiedTracePredicates> imperfectIpps =
					ipps.stream().filter(a -> !a.isPerfect()).collect(Collectors.toList());

			final IpAbStrategyModuleResult<L> result =
					interpolantAutomatonBuilder.buildInterpolantAutomaton(perfectIpps, imperfectIpps);
			mInterpolantAutomaton = result.getAutomaton();
			mUsedTracePredicates = result.getUsedTracePredicates();
		} catch (final AutomataOperationCanceledException e) {
			throw new ToolchainCanceledException(e,
					new RunningTaskInfo(interpolantAutomatonBuilder.getClass(), "computing interpolant automaton"));
		}
	}

	private void logModule(final String msg, final Object module) {
		mLogger.info("%s %s [%s]", msg, module.getClass().getSimpleName(), module.hashCode());
	}

}
