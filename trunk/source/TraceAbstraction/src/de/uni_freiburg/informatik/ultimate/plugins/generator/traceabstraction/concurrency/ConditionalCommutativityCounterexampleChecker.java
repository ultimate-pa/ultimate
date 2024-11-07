/*
 * Copyright (C) 2024 Marcel Ebbinghaus
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult.BasicRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.SleepSetStateFactoryForRefinement.SleepPredicate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.conditional.ConditionalCommutativityChecker;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.conditional.ConditionalCommutativityStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.IIpAbStrategyModule;
import de.uni_freiburg.informatik.ultimate.util.Lazy;

/**
 * Checks whether a counterexample has an equivalent trace of lower order (i.e. one which was already explored in a
 * previous iteration).
 *
 * @author Marcel Ebbinghaus
 *
 * @param <L>
 *            letter type
 */
public class ConditionalCommutativityCounterexampleChecker<L extends IAction> {
	private final IDfsOrder<L, IPredicate> mDfsOrder;
	private final ConditionalCommutativityChecker<L> mChecker;
	private final Function<IRun<L, IPredicate>, IIpAbStrategyModule<L>> mAutomatonBuilderFactory;
	private final ConditionalCommutativityStatisticsGenerator mStatistics;

	/**
	 * Creates a new instance. The instance may be used repeatedly throughout a CEGAR loop.
	 *
	 * @param services
	 *            Ultimate services
	 * @param dfsOrder
	 *            The order used for the emptiness check, which is a DFS
	 * @param conComChecker
	 *            Used to find and prove sufficient conditions for commutativity.
	 * @param automatonBuilderFactory
	 *            Used to construct interpolant automata from proofs of commutativity along a trace.
	 * @param statistics
	 *            collects statistics
	 */
	public ConditionalCommutativityCounterexampleChecker(final IUltimateServiceProvider services,
			final IDfsOrder<L, IPredicate> dfsOrder, final ConditionalCommutativityChecker<L> conComChecker,
			final Function<IRun<L, IPredicate>, IIpAbStrategyModule<L>> automatonBuilderFactory,
			final ConditionalCommutativityStatisticsGenerator statistics) {
		mDfsOrder = dfsOrder;
		mChecker = conComChecker;
		mAutomatonBuilderFactory = automatonBuilderFactory;
		mStatistics = statistics;
	}

	/**
	 * Checks for conditional commutativity along the given run (which represents the counterexample) and may provide an
	 * interpolant automaton which proves conditional commutativity and thus equivalence of a trace of lower order.
	 *
	 * @param run
	 *            the run representing the counterexample
	 * @param runPredicates
	 *            the predicates of the given run
	 * @return an interpolant automaton proving conditional commutativity or null otherwise
	 */
	public IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>>
			getCommutativityProof(final NestedRun<L, IPredicate> run) {
		for (int i = 0; i < run.getStateSequence().size() - 2; i++) {
			final IPredicate state = run.getStateSequence().get(i);
			final L letter1 = run.getWord().getSymbol(i);
			final L letter2 = run.getWord().getSymbol(i + 1);

			if (!isNonMinimalityPoint(state, letter1, letter2)) {
				continue;
			}

			final NestedRun<L, IPredicate> currentRun = run.getSubRun(0, i);
			final var refinementResult =
					mChecker.checkConditionalCommutativity(currentRun, state, letter1, letter2);

			if (refinementResult != null) {
				mStatistics.addCommutingCounterexample();
				return buildAutomaton(currentRun, refinementResult);
			}
		}
		return null;
	}

	private boolean isNonMinimalityPoint(final IPredicate state, final L currentLetter, final L nextLetter) {
		// TODO this is brittle, it will fail for many configurations
		final Set<L> sleepSet = ((SleepPredicate<L>) state).getSleepSet();
		return sleepSet.contains(nextLetter) || mDfsOrder.getOrder(state).compare(currentLetter, nextLetter) > 0;
	}

	private IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> buildAutomaton(
			final NestedRun<L, IPredicate> currentRun,
			final IRefinementEngineResult<L, Collection<QualifiedTracePredicates>> refinementResult) {
		// The code below is adapted from TraceAbstractionRefinementEngine.
		final var perfectIps = refinementResult.getInfeasibilityProof().stream().filter(qtp -> qtp.isPerfect())
				.collect(Collectors.toList());
		final var imperfectIps = refinementResult.getInfeasibilityProof().stream().filter(qtp -> !qtp.isPerfect())
				.collect(Collectors.toList());

		final var automatonBuilder = mAutomatonBuilderFactory.apply(currentRun);
		try {
			final var automatonResult = automatonBuilder.buildInterpolantAutomaton(perfectIps, imperfectIps);
			return new BasicRefinementEngineResult<>(LBool.UNSAT, automatonResult.getAutomaton(), null, false,
					automatonResult.getUsedTracePredicates(), new Lazy<>(refinementResult::getHoareTripleChecker),
					new Lazy<>(refinementResult::getPredicateUnifier));
		} catch (final AutomataOperationCanceledException e) {
			throw new ToolchainCanceledException(e,
					new RunningTaskInfo(automatonBuilder.getClass(), "computing interpolant automaton"));
		}
	}
}
