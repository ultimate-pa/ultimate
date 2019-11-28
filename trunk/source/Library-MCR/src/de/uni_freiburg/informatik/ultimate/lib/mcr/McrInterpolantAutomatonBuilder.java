package de.uni_freiburg.informatik.ultimate.lib.mcr;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.mcr.Mcr.IProofProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class McrInterpolantAutomatonBuilder<LETTER extends IIcfgTransition<?>> {
	private final NestedWordAutomaton<LETTER, IPredicate> mResult;
	private final IProofProvider<LETTER> mProofProvider;
	private final IPredicate mPrecondition;
	private final IPredicate mPostcondition;
	private final IPredicateUnifier mPredicateUnifier;
	private final ILogger mLogger;

	public McrInterpolantAutomatonBuilder(final AutomataLibraryServices services, final VpAlphabet<LETTER> vpAlphabet,
			final IEmptyStackStateFactory<IPredicate> emptyStateFactory, final IProofProvider<LETTER> proofProvider,
			final IPredicate precondition, final IPredicate postcondition, final IPredicateUnifier predicateUnifier,
			final ILogger logger) {
		mProofProvider = proofProvider;
		mPrecondition = precondition;
		mPostcondition = postcondition;
		mPredicateUnifier = predicateUnifier;
		mResult = new NestedWordAutomaton<>(services, vpAlphabet, emptyStateFactory);
		mResult.addState(true, false, precondition);
		mResult.addState(false, true, postcondition);
		mLogger = logger;
	}

	public NestedWordAutomaton<LETTER, IPredicate> getResult() {
		return mResult;
	}

	// TODO: Use DeterministicInterpolantAutomaton
	public List<IPredicate> getInterpolantsIfAccepted(final List<LETTER> trace) {
		final List<Map<IPredicate, IPredicate>> precedessorTrace = new ArrayList<>();
		final Map<IPredicate, IPredicate> initialPrecedessors = new HashMap<>();
		for (final IPredicate initial : mResult.getInitialStates()) {
			initialPrecedessors.put(initial, null);
		}
		precedessorTrace.add(initialPrecedessors);
		for (final LETTER action : trace) {
			final Map<IPredicate, IPredicate> newPrecedessors = new HashMap<>();
			for (final IPredicate state : precedessorTrace.get(precedessorTrace.size() - 1).keySet()) {
				for (final OutgoingInternalTransition<LETTER, IPredicate> outgoing : mResult.internalSuccessors(state,
						action)) {
					newPrecedessors.put(outgoing.getSucc(), state);
				}
			}
			precedessorTrace.add(newPrecedessors);
		}
		for (final IPredicate state : precedessorTrace.get(precedessorTrace.size() - 1).keySet()) {
			if (mResult.isFinal(state)) {
				final IPredicate[] stateSequence = new IPredicate[precedessorTrace.size()];
				IPredicate currentState = state;
				for (int i = precedessorTrace.size() - 1; i >= 0; i--) {
					stateSequence[i] = currentState;
					currentState = precedessorTrace.get(i).get(currentState);
				}
				return Arrays.asList(stateSequence);
			}
		}
		return null;
	}

	public <STATE> void update(final INestedWordAutomaton<LETTER, STATE> mcrAutomaton, final List<LETTER> initialTrace,
			final List<IPredicate> initialInterpolants) {
		final Map<STATE, IPredicate> stateMap = new HashMap<>();
		// Fill stateMap with the given interpolants
		final STATE initialState = mcrAutomaton.getInitialStates().iterator().next();
		final List<STATE> initialStates = new ArrayList<>();
		STATE currentState = initialState;
		initialStates.add(currentState);
		for (int i = 0; i < initialInterpolants.size(); i++) {
			currentState = getSuccessor(currentState, initialTrace.get(i), mcrAutomaton);
			initialStates.add(currentState);
		}
		coverStates(initialTrace, initialStates, initialInterpolants, mPrecondition, mPostcondition, stateMap,
				mcrAutomaton);
		final LinkedList<List<LETTER>> traceQueue = new LinkedList<>();
		final LinkedList<List<STATE>> stateQueue = new LinkedList<>();
		traceQueue.add(Collections.emptyList());
		stateQueue.add(Collections.singletonList(initialState));
		int count = 1;
		while (!traceQueue.isEmpty()) {
			final List<LETTER> trace = traceQueue.remove();
			final List<STATE> states = stateQueue.remove();
			final Iterable<OutgoingInternalTransition<LETTER, STATE>> nextStates =
					mcrAutomaton.internalSuccessors(states.get(states.size() - 1));
			for (final OutgoingInternalTransition<LETTER, STATE> outgoing : nextStates) {
				final STATE nextState = outgoing.getSucc();
				final boolean stateCovered = stateMap.containsKey(nextState);
				if (stateCovered && trace.isEmpty()) {
					// We already covered nextState, so we only need to explore its successors
					traceQueue.add(Collections.emptyList());
					stateQueue.add(Collections.singletonList(nextState));
				} else {
					final List<LETTER> newTrace = new ArrayList<>(trace.size() + 1);
					newTrace.addAll(trace);
					newTrace.add(outgoing.getLetter());
					final List<STATE> newStates = new ArrayList<>(states.size() + 1);
					newStates.addAll(states);
					newStates.add(nextState);
					if (stateCovered) {
						// We found a postcondition in the stateMap, so we can interpolate the trace
						count += visitTrace(newTrace, newStates, stateMap, mcrAutomaton);
					} else {
						traceQueue.add(newTrace);
						stateQueue.add(newStates);
					}
				}
			}
		}
		// TODO: Is this sound and necessary?
		addMissingTransitions(mcrAutomaton, stateMap);
		mLogger.info(mResult);
		mLogger.warn("MCR Automaton construction finsihed. Had to interpolate " + count + " traces.");
	}

	private <STATE> STATE getSuccessor(final STATE currentState, final LETTER action,
			final INestedWordAutomaton<LETTER, STATE> automaton) {
		for (final OutgoingInternalTransition<LETTER, STATE> outgoing : automaton.internalSuccessors(currentState,
				action)) {
			final STATE nextState = outgoing.getSucc();
			if (currentState != nextState) {
				return nextState;
			}
		}
		throw new IllegalStateException("No acyclic successor of + " + currentState + " under " + action);
	}

	private <STATE> void addMissingTransitions(final INestedWordAutomaton<LETTER, STATE> mcrAutomaton,
			final Map<STATE, IPredicate> stateMap) {
		for (final Entry<STATE, IPredicate> entry : stateMap.entrySet()) {
			final STATE oldState = entry.getKey();
			for (final OutgoingInternalTransition<LETTER, STATE> edge : mcrAutomaton.internalSuccessors(oldState)) {
				final STATE succ = edge.getSucc();
				if (succ == oldState) {
					// Ignore self-loops
					continue;
				}
				mResult.addInternalTransition(entry.getValue(), edge.getLetter(), stateMap.get(succ));
			}
		}
	}

	private <STATE> int visitTrace(final List<LETTER> trace, final List<STATE> states,
			final Map<STATE, IPredicate> stateMap, final INestedWordAutomaton<LETTER, STATE> mcrAutomaton) {
		int numberOfInterpolations = 0;
		IPredicate precondition = null;
		int start = 0;
		boolean newTraceFound = false;
		for (int i = 0; i < states.size(); i++) {
			final IPredicate newCondition = stateMap.get(states.get(i));
			if (newCondition != null) {
				if (newTraceFound) {
					if (i - start < 2) {
						continue;
					}
					final List<LETTER> newTrace = trace.subList(start, i);
					final List<STATE> newStates = states.subList(start, i + 1);
					final List<IPredicate> interpolants = getInterpolants(newTrace, precondition, newCondition);
					coverStates(newTrace, newStates, interpolants, precondition, newCondition, stateMap, mcrAutomaton);
					numberOfInterpolations++;
					start = i;
					precondition = newCondition;
					newTraceFound = false;
				} else {
					precondition = newCondition;
					start = i;
				}
			} else {
				newTraceFound = true;
			}
		}
		return numberOfInterpolations;
	}

	private <STATE> void coverStates(final List<LETTER> trace, final List<STATE> states,
			final List<IPredicate> interpolants, final IPredicate precondition, final IPredicate postcondition,
			final Map<STATE, IPredicate> stateMap, final INestedWordAutomaton<LETTER, STATE> mcrAutomaton) {
		assert states.size() == interpolants.size() + 2 && trace.size() == interpolants.size() + 1;
		// Add the interpolants to the resulting automaton and to stateMap and add the transitions from trace
		IPredicate currentInterpolant = precondition;
		stateMap.put(states.get(0), precondition);
		for (int i = 0; i < interpolants.size(); i++) {
			final IPredicate nextInterpolant = mPredicateUnifier.getOrConstructPredicate(interpolants.get(i));
			if (!mResult.contains(nextInterpolant)) {
				mResult.addState(false, false, nextInterpolant);
			}
			mResult.addInternalTransition(currentInterpolant, trace.get(i), nextInterpolant);
			stateMap.put(states.get(i + 1), nextInterpolant);
			currentInterpolant = nextInterpolant;
		}
		stateMap.put(states.get(states.size() - 1), postcondition);
		mResult.addInternalTransition(currentInterpolant, trace.get(trace.size() - 1), postcondition);
		// Try to merge states if the have the same sucessors
		final Set<STATE> visited = new HashSet<>();
		final LinkedList<STATE> queue = new LinkedList<>();
		// We just need to check given states and their predecessors
		for (final STATE state : states) {
			queue.add(state);
			mcrAutomaton.internalPredecessors(state).forEach(x -> queue.add(x.getPred()));
		}
		while (!queue.isEmpty()) {
			final STATE state = queue.remove();
			if (!visited.add(state)) {
				continue;
			}
			final IPredicate predicate = stateMap.get(state);
			assert predicate != null;
			for (final OutgoingInternalTransition<LETTER, IPredicate> predicateEdge : mResult
					.internalSuccessors(predicate)) {
				for (final OutgoingInternalTransition<LETTER, STATE> edge : mcrAutomaton.internalSuccessors(state,
						predicateEdge.getLetter())) {
					final STATE succ = edge.getSucc();
					stateMap.put(succ, predicateEdge.getSucc());
					queue.add(succ);
				}
			}
		}
	}

	private List<IPredicate> getInterpolants(final List<LETTER> trace, final IPredicate precondition,
			final IPredicate postcondition) {
		final Pair<LBool, QualifiedTracePredicates> result =
				mProofProvider.getProof(trace, precondition, postcondition);
		if (result.getFirst() != LBool.UNSAT) {
			// We found a feasible trace, somehow remove it from the automaton
			// TODO: For now just throw an exception
			throw new IllegalStateException("We found a feasible trace in the automaton.");
		}
		final List<IPredicate> predicates = result.getSecond().getPredicates();
		return predicates;
	}

	@Override
	public String toString() {
		return mResult.toString();
	}
}
