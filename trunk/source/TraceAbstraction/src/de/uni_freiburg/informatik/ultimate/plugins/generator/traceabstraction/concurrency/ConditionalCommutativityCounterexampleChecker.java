/*
 * Copyright (C) 2024 Marcel Ebbinghaus
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
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

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.ISleepSetStateFactory;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult.BasicRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.ConditionalCommutativityChecker;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.IIpAbStrategyModule;
import de.uni_freiburg.informatik.ultimate.util.Lazy;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;
import de.uni_freiburg.informatik.ultimate.util.statistics.AbstractStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 * Checks whether a counterexample has an equivalent trace of lower order (i.e. one which was already explored in a
 * previous iteration).
 *
 * @author Marcel Ebbinghaus
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            letter type
 */
public class ConditionalCommutativityCounterexampleChecker<L extends IAction> {
	private final ILogger mLogger;
	private final IDfsOrder<L, IPredicate> mDfsOrder;
	private final ConditionalCommutativityChecker<L> mChecker;

	private final ISleepSetStateFactory<L, IPredicate, IPredicate> mSleepSetFactory;
	private final Function<Word<L>, IIpAbStrategyModule<L>> mAutomatonBuilderFactory;

	private final int mPathProgramThreshold;
	private final int mImperfectProofRetries;

	// We approximate path programs by looking at the set of control configurations.
	private final Map<Set<?>, Integer> mPreviouslySeenPathPrograms = new HashMap<>();

	private final Set<Triple<List<Object>, L, L>> mHopelessConditionChecks = new HashSet<>();
	private final Map<Triple<List<Object>, L, L>, Integer> mFailedConditionChecks = new HashMap<>();

	private final Statistics mStatistics;

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
	 * @param pathProgramThreshold
	 *            The threshold for repetition of the same path program at which to start commutativity condition
	 *            synthesis
	 * @param imperfectProofRetries
	 *            The number of retries for proving commutativity at the same point of non-minimality, if previous
	 *            attempts failed due to imperfect proofs.
	 */
	public ConditionalCommutativityCounterexampleChecker(final IUltimateServiceProvider services,
			final IDfsOrder<L, IPredicate> dfsOrder, final ConditionalCommutativityChecker<L> conComChecker,
			final ISleepSetStateFactory<L, IPredicate, IPredicate> sleepSetFactory,
			final Function<Word<L>, IIpAbStrategyModule<L>> automatonBuilderFactory, final int pathProgramThreshold,
			final int imperfectProofRetries) {
		mLogger = services.getLoggingService().getLogger(ConditionalCommutativityCounterexampleChecker.class);

		mDfsOrder = dfsOrder;
		mChecker = conComChecker;
		mSleepSetFactory = Objects.requireNonNull(sleepSetFactory);
		mAutomatonBuilderFactory = automatonBuilderFactory;
		mStatistics = new Statistics(conComChecker);

		mPathProgramThreshold = pathProgramThreshold;
		mImperfectProofRetries = imperfectProofRetries;
	}

	/**
	 * Checks for conditional commutativity along the given run (which represents the counterexample) and may provide an
	 * interpolant automaton which proves conditional commutativity and thus equivalence of a trace of lower order.
	 *
	 * @param run
	 *            the run representing the counterexample
	 * @param controlConfigurations
	 *            the control configurations along the given run
	 * @return an interpolant automaton proving conditional commutativity or null otherwise
	 */
	public IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>>
			getCommutativityProof(final NestedRun<L, IPredicate> run, final List<Object> controlConfigurations) {
		final Set<?> pathProgram = Set.copyOf(controlConfigurations);
		final int occurrence = mPreviouslySeenPathPrograms.getOrDefault(pathProgram, 0) + 1;
		mPreviouslySeenPathPrograms.put(pathProgram, occurrence);

		mLogger.info("Examining path program with hash %d, occurence #%d", pathProgram.hashCode(), occurrence);
		if (occurrence < mPathProgramThreshold) {
			mLogger.info("Commutativity condition synthesis is only active after more than %d occurrences. Skipping...",
					mPathProgramThreshold);
			return null;
		}
		mLogger.info("Trying to synthesize and prove commutativity condition.");

		for (int i = 0; i < run.getStateSequence().size() - 2; i++) {
			final IPredicate state = run.getStateSequence().get(i);
			final L letter1 = run.getWord().getSymbol(i);
			final L letter2 = run.getWord().getSymbol(i + 1);

			if (!isNonMinimalityPoint(state, letter1, letter2)) {
				continue;
			}

			final Word<L> currentTrace = run.getWord().getSubWord(0, i);
			final List<Object> currentConfigurations = controlConfigurations.subList(0, i + 1);

			// Check if we already cached this check as hopeless
			final var triple = new Triple<>(controlConfigurations, letter1, letter2);
			if (mHopelessConditionChecks.contains(triple)) {
				mLogger.info("Commutativity condition check at non-minimality point %d is hopeless, skipping.", i);
				continue;
			}

			mLogger.info("Performing commutativity condition check at non-minimality point %d", i);
			final var checkResult = mChecker.checkConditionalCommutativity(currentTrace, currentConfigurations, state,
					letter1, letter2);
			switch (checkResult.getType()) {
			case SUCCESS:
				mStatistics.reportSuccessfulCommutativityProof();
				mLogger.info(
						"Successfully proved commutativity at non-minimality point %d. Constructing proof automaton...",
						i);
				return buildAutomaton(currentTrace, checkResult.getRefinementResult());

			case UNKNOWN_CHECK:
			case CONDITION_NOT_SATISFIED:
				// Cache as hopeless and avoid any repeated checks.
				mLogger.info("Commutativity condition check yielded %s. Marking as hopeless.", checkResult.getType());
				mHopelessConditionChecks.add(triple);
				break;

			case ALREADY_INDEPENDENT:
				// By the definition of non-minimality points and the fact that we compute a minimal reduction, this
				// should be impossible.
				// TODO This can currently happen if letter2 is not enabled because letter1 is the fork that creates the
				// thread of letter2.
				// assert false : "Should never perform conditional commutativity check for independent letters";
				mLogger.warn("Statements were already independent.");
				break;

			case PROOF_IMPERFECT:
				final int repetition = mFailedConditionChecks.getOrDefault(triple, 0) + 1;
				mLogger.info("Commutativity condition check failed due to imperfect proof (attempt %d of %d).",
						repetition, mImperfectProofRetries + 1);
				if (repetition <= mImperfectProofRetries) {
					mFailedConditionChecks.put(triple, repetition);
				} else {
					mFailedConditionChecks.remove(triple);
					mHopelessConditionChecks.add(triple);
				}
				break;

			case NO_CONDITION_FOUND:
				// We do not cache this as hopeless because we assume the attempt to find a condition is comparatively
				// cheap, and since this result may occur quite often (e.g. for letters of the same thread), the memory
				// overhead would be large.
				mLogger.info("No commutativity condition found.");
				break;
			}
		}

		mLogger.warn("Failed to synthesize and prove commutativity condition.");
		return null;
	}

	public IStatisticsDataProvider getStatistics() {
		return mStatistics;
	}

	private boolean isNonMinimalityPoint(final IPredicate state, final L currentLetter, final L nextLetter) {
		final Set<L> sleepSet = mSleepSetFactory.getSleepSet(state);
		return sleepSet.contains(nextLetter) || mDfsOrder.getOrder(state).compare(currentLetter, nextLetter) > 0;
	}

	private IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> buildAutomaton(final Word<L> trace,
			final IRefinementEngineResult<L, Collection<QualifiedTracePredicates>> refinementResult) {
		// The code below is adapted from TraceAbstractionRefinementEngine.
		final var perfectIps = refinementResult.getInfeasibilityProof().stream()
				.filter(QualifiedTracePredicates::isPerfect).collect(Collectors.toList());
		final var imperfectIps = refinementResult.getInfeasibilityProof().stream().filter(qtp -> !qtp.isPerfect())
				.collect(Collectors.toList());

		final var automatonBuilder = mAutomatonBuilderFactory.apply(trace);
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

	private static class Statistics extends AbstractStatisticsDataProvider {
		private int mSuccessfulCommutativityProofs;

		public Statistics(final ConditionalCommutativityChecker<?> conComChecker) {
			declareCounter("SuccessfulCommutativityProofs", () -> mSuccessfulCommutativityProofs);
			forward("ConComChecker Statistics", conComChecker::getStatistics);
		}

		public void reportSuccessfulCommutativityProof() {
			mSuccessfulCommutativityProofs++;
		}
	}
}
