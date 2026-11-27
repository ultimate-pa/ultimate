/*
 * Copyright (C) 2026 Marcel Ebbinghaus
 * Copyright (C) 2026 University of Freiburg
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
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.afa.IndependenceLetter;
import de.uni_freiburg.informatik.ultimate.automata.afa.IndependenceLetter.IndependentPair;
import de.uni_freiburg.informatik.ultimate.automata.afa.IndependenceLetter.WrappedLetter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult.BasicRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.afa.AfaConditionalCommutativityChecker;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.IIpAbStrategyModule;
import de.uni_freiburg.informatik.ultimate.util.Lazy;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

public class AfaConditionalCommutativityCounterexampleChecker<L extends IAction, S1, S2> {
	private final ILogger mLogger;
	private final AfaConditionalCommutativityChecker<L> mChecker;
	private final Function<Word<L>, IIpAbStrategyModule<L>> mAutomatonBuilderFactory;
	private final INwaOutgoingLetterAndTransitionProvider<L, S2> mOrderAutomaton;
	private final IDfsOrder<L, S2> mOrder;

	// TODO: implement class similar to ConditionalCommutativityCounterexampleChecker but for AFAs

	public AfaConditionalCommutativityCounterexampleChecker(final IUltimateServiceProvider services,
			final AfaConditionalCommutativityChecker<L> checker, final IDfsOrder<L, S2> order,
			final INwaOutgoingLetterAndTransitionProvider<L, S2> orderAutomaton,
			final Function<Word<L>, IIpAbStrategyModule<L>> automatonBuilderFactory) {
		mLogger = services.getLoggingService().getLogger(AfaConditionalCommutativityCounterexampleChecker.class);
		mChecker = checker;
		mOrder = order;
		mOrderAutomaton = orderAutomaton;
		mAutomatonBuilderFactory = automatonBuilderFactory;
	}

	// TODO: what exactly do we have as an input here? A run? What kind of run? Do we need to implement a BddRun?
	// For now: just take the independence automaton and a word (or nestedrun if needed) and do a naive popr check, i.e.
	// consider all decompositions and check for each whether it actually is a popr using the independence automaton
	public IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> getCommutativityProof(
			final NestedRun<L, IPredicate> run,
			final INwaOutgoingLetterAndTransitionProvider<IndependenceLetter<L>, S1> independenceAutomaton,
			final List<?> controlConfigurations, final L templateLetter) {

		final NestedWord<L> trace = run.getWord();
		final List<L> traceLetters = trace.asList();
		final List<IPredicate> stateSequence = run.getStateSequence();
		final List<S2> orderStates = computeOrderStates(trace);

		for (int aIndex = 0; aIndex < trace.length() - 1; ++aIndex) {
			final L a = trace.getSymbol(aIndex);
			final L b = trace.getSymbol(aIndex + 1);

			// first, swap a and b
			final List<L> currentWord = new ArrayList<>(traceLetters);
			Collections.swap(currentWord, aIndex, aIndex + 1);

			// move b to the left.
			for (int cIndex = aIndex; cIndex >= 0; --cIndex) {
				final L c = trace.getSymbol(cIndex);

				if (cIndex < aIndex) {
					// check the next required swap in the current context
					if (!isIndependent(currentWord, independenceAutomaton, cIndex)) {
						// all further-left candidates require this swap as well
						break;
					}

					// swap before checking the next candidate
					Collections.swap(currentWord, cIndex, cIndex + 1);
				}

				final S2 orderState = orderStates.get(cIndex);

				if (mOrder.getOrder(orderState).compare(b, c) < 0) {
					// valid popr decomposition: check commutativity of a and b
					final var checkResult = mChecker.checkCommutativity(trace, aIndex, stateSequence.get(aIndex),
							controlConfigurations, templateLetter);

					// process result and build interpolant automaton if successful
					switch (checkResult.getType()) {
					case SUCCESS:
						mLogger.info("Successfully proved commutativity.Constructing proof automaton...");
						return buildAutomaton(trace, checkResult.getRefinementResult());
					case ALREADY_INDEPENDENT:
						mLogger.warn("Statements were already independent.");
						break;
					case PROOF_IMPERFECT:
						mLogger.info("Commutativity condition check failed due to imperfect proof");
						break;
					case UNKNOWN_CHECK:
					case FAILURE:
						mLogger.info("Commutativity condition check yielded %s.", checkResult.getType());
						break;
					}
					break;
				}
			}
		}
		mLogger.warn("Failed to prove commutativity.");
		return null;
	}

	private boolean isIndependent(final List<L> word,
			final INwaOutgoingLetterAndTransitionProvider<IndependenceLetter<L>, S1> automaton, final int index) {

		final Set<S1> currentStates = new HashSet<>();
		automaton.getInitialStates().forEach(currentStates::add);

		for (int i = 0; i < word.size(); ++i) {
			final IndependenceLetter<L> letter;

			if (i == index) {
				// this is the pair whose independence should be checked
				letter = new IndependentPair<>(word.get(i), word.get(i + 1));
			} else {
				letter = new WrappedLetter<>(word.get(i));
			}

			final Set<S1> successors = new HashSet<>();

			for (final S1 state : currentStates) {
				for (final var transition : automaton.internalSuccessors(state, letter)) {
					successors.add(transition.getSucc());
				}
			}

			if (successors.isEmpty()) {
				return false;
			}

			currentStates.clear();
			currentStates.addAll(successors);

			if (i == index) {
				++i;
			}
		}

		return currentStates.stream().anyMatch(automaton::isFinal);
	}

	private List<S2> computeOrderStates(final NestedWord<L> trace) {
		final S2 initialState =
				DataStructureUtils.getOneAndOnly(mOrderAutomaton.getInitialStates(), "initial order state");

		final List<S2> result = new ArrayList<>(trace.length() + 1);
		S2 currentState = initialState;
		result.add(currentState);

		for (int i = 0; i < trace.length(); i++) {
			currentState = getUniqueOrderSuccessor(currentState, trace.getSymbol(i));
			result.add(currentState);
		}
		return result;
	}

	// method to ensure that the order automaton is total and deterministic
	// should later be ensured by the order automaton instead
	private S2 getUniqueOrderSuccessor(final S2 state, final L letter) {
		final Iterator<OutgoingInternalTransition<L, S2>> iterator =
				mOrderAutomaton.internalSuccessors(state, letter).iterator();

		if (!iterator.hasNext()) {
			throw new IllegalArgumentException(
					"Order automaton is not total for state " + state + " and letter " + letter);
		}

		final S2 successor = iterator.next().getSucc();

		if (iterator.hasNext()) {
			throw new IllegalArgumentException(
					"Order automaton is not deterministic for state " + state + " and letter " + letter);
		}

		return successor;
	}

	private IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> buildAutomaton(final Word<L> trace,
			final IRefinementEngineResult<L, Collection<QualifiedTracePredicates>> refinementResult) {
		// The code below is copied from ConditionalCommutativityCounterexampleChecker to keep everything together for
		// now. We should definitely think about refactoring at some point.
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
}
