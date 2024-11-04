/*
 * Copyright (C) 2024 Marcel Ebbinghaus
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.conditional;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult.BasicRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.SleepSetStateFactoryForRefinement.SleepPredicate;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
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
	private final IUltimateServiceProvider mServices;
	private final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mAbstraction;
	private final IEmptyStackStateFactory<IPredicate> mEmptyStackStateFactory;
	private final ConditionalCommutativityChecker<L> mChecker;
	private final ConditionalCommutativityCheckerStatisticsUtils mStatisticsUtils;
	private final IDfsOrder<L, IPredicate> mDfsOrder;

	/**
	 * Constructor.
	 *
	 * @param services
	 *            Ultimate services
	 * @param criterion
	 *            An IConditionalCommutativityCriterion to decide when to check for conditional commutativity
	 * @param independenceRelation
	 *            The independence relation used for the reduction
	 * @param dfsOrder
	 *            The order used for the emptiness check, which is a DFS
	 * @param script
	 *            Script for conjunction handling
	 * @param generator
	 *            Generator for constructing commutativity conditions
	 * @param abstraction
	 *            Current abstraction
	 * @param emptyStackStateFactory
	 *            Factory
	 * @param traceChecker
	 *            An ITraceChecker responsible for checking whether a condition holds after the currentRun
	 * @param statisticsUtils
	 *            Statistics
	 */
	public ConditionalCommutativityCounterexampleChecker(final IUltimateServiceProvider services,
			final IDfsOrder<L, IPredicate> dfsOrder,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> abstraction,
			final IEmptyStackStateFactory<IPredicate> emptyStackStateFactory,
			final ConditionalCommutativityCheckerStatisticsUtils statisticsUtils,
			final ConditionalCommutativityChecker<L> conComChecker) {
		mServices = services;
		mDfsOrder = dfsOrder;
		mAbstraction = abstraction;
		mEmptyStackStateFactory = emptyStackStateFactory;
		mChecker = conComChecker;
		mStatisticsUtils = statisticsUtils;
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
	public BasicRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>>
			getInterpolants(final IRun<L, IPredicate> run, final List<IPredicate> runPredicates) {
		for (int i = 0; i < run.getStateSequence().size() - 2; i++) {
			final IPredicate state = run.getStateSequence().get(i);
			final L letter1 = run.getWord().getSymbol(i);
			final L letter2 = run.getWord().getSymbol(i + 1);

			// TODO this is brittle, it will fail for many configurations
			if (((SleepPredicate<L>) state).getSleepSet().contains(letter2)
					|| (mDfsOrder.getOrder(state).compare(letter1, letter2) > 0)) {

				final IPredicate runPredicate = runPredicates.get(i);
				final List<IPredicate> interpolantPredicates = new ArrayList<>();
				if (runPredicate != null && !SmtUtils.isTrueLiteral(runPredicate.getFormula())) {
					interpolantPredicates.add(runPredicate);
				}
				NestedRun<L, IPredicate> currentRun = (NestedRun<L, IPredicate>) run;
				if (i != run.getStateSequence().size() - 1) {
					currentRun = currentRun.getSubRun(0, i);
				}

				final var refinementResult = mChecker.checkConditionalCommutativity(currentRun, interpolantPredicates,
						state, letter1, letter2);

				if (refinementResult != null) {

					final var conComInterpolantProvider = ConditionalCommutativityInterpolantAutomatonProvider
							.fromRefinementResult(mServices, mAbstraction.getAlphabet(), mEmptyStackStateFactory,
									currentRun.getWord(), refinementResult);
					final NestedWordAutomaton<L, IPredicate> automaton =
							conComInterpolantProvider.getInterpolantAutomaton();

					mStatisticsUtils.addCommutingCounterexample();

					final BasicRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> refinementResultAut =
							new BasicRefinementEngineResult<>(LBool.UNSAT, automaton, null, false,
									refinementResult.getUsedTracePredicates(), new Lazy<>((IHoareTripleChecker) null),
									new Lazy<>(refinementResult.getPredicateUnifier()));
					return refinementResultAut;
				}
			}
		}
		return null;
	}

}
