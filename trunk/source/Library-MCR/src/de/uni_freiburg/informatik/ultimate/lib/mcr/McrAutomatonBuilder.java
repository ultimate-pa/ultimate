package de.uni_freiburg.informatik.ultimate.lib.mcr;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IntersectNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.StringFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Class to construct automata based on the MCR relation.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class McrAutomatonBuilder<LETTER extends IIcfgTransition<?>> {
	private final List<LETTER> mOriginalTrace;
	private final IPredicateUnifier mPredicateUnifier;
	private final ILogger mLogger;
	private final AutomataLibraryServices mServices;
	private final IEmptyStackStateFactory<IPredicate> mEmptyStackFactory;
	private final VpAlphabet<LETTER> mAlphabet;
	private final VpAlphabet<Integer> mIntAlphabet;

	private List<INestedWordAutomaton<Integer, String>> mThreadAutomata;

	private final HashRelation<IProgramVar, Integer> mVariables2Writes;
	private final Map<LETTER, List<Integer>> mActions2Indices;
	private final Map<String, List<Integer>> mThreads2SortedActions;

	public McrAutomatonBuilder(final List<LETTER> trace, final IPredicateUnifier predicateUnifier,
			final IEmptyStackStateFactory<IPredicate> emptyStackFactory, final ILogger logger,
			final VpAlphabet<LETTER> alphabet, final IUltimateServiceProvider services) {
		mOriginalTrace = trace;
		mLogger = logger;
		mPredicateUnifier = predicateUnifier;
		mServices = new AutomataLibraryServices(services);
		mEmptyStackFactory = emptyStackFactory;
		mAlphabet = alphabet;
		mIntAlphabet = new VpAlphabet<>(IntStream.range(0, trace.size()).boxed().collect(Collectors.toSet()));
		mVariables2Writes = new HashRelation<>();
		mThreads2SortedActions = new HashMap<>();
		mActions2Indices = new HashMap<>();
		preprocess();
	}

	private void preprocess() {
		for (int i = 0; i < mOriginalTrace.size(); i++) {
			final LETTER action = mOriginalTrace.get(i);
			addValue(mActions2Indices, action, i);
			for (final IProgramVar var : action.getTransformula().getAssignedVars()) {
				mVariables2Writes.addPair(var, i);
			}
			final String currentThread = action.getPrecedingProcedure();
			addValue(mThreads2SortedActions, currentThread, i);
			final String nextThread = action.getSucceedingProcedure();
			if (currentThread != nextThread) {
				addValue(mThreads2SortedActions, nextThread, i);
			}
		}
	}

	private static <K, V> void addValue(final Map<K, List<V>> map, final K key, final V value) {
		List<V> values = map.get(key);
		if (values == null) {
			values = new ArrayList<>();
			map.put(key, values);
		}
		values.add(value);
	}

	private static String getState(final int i) {
		return "q" + i;
	}

	private List<INestedWordAutomaton<Integer, String>> getThreadAutomata() {
		if (mThreadAutomata == null) {
			mThreadAutomata = new ArrayList<>();
			final StringFactory factory = new StringFactory();
			// Construct automata for the MHB relation
			for (final List<Integer> threadActions : mThreads2SortedActions.values()) {
				final NestedWordAutomaton<Integer, String> nwa =
						new NestedWordAutomaton<>(mServices, mIntAlphabet, factory);
				final Set<Integer> threadActionSet = new HashSet<>(threadActions);
				for (int i = 0; i <= threadActions.size(); i++) {
					nwa.addState(i == 0, i == threadActions.size(), getState(i));
					if (i > 0) {
						nwa.addInternalTransition(getState(i - 1), threadActions.get(i - 1), getState(i));
					}
					for (int other = 0; other < mOriginalTrace.size(); other++) {
						if (!threadActionSet.contains(other)) {
							nwa.addInternalTransition(getState(i), other, getState(i));
						}
					}
				}
				mThreadAutomata.add(nwa);
			}
		}
		return mThreadAutomata;
	}

	public NestedWordAutomaton<LETTER, IPredicate> buildMhbAutomaton(final PredicateFactory predicateFactory)
			throws AutomataLibraryException {
		final INestedWordAutomaton<Integer, String> automaton = intersectNwa(getThreadAutomata());
		final Term trueTerm = mPredicateUnifier.getTruePredicate().getFormula();
		final Map<String, IPredicate> stateMap = automaton.getStates().stream()
				.collect(Collectors.toMap(x -> x, x -> predicateFactory.newSPredicate(null, trueTerm)));
		return transformAutomaton(automaton, stateMap::get, mEmptyStackFactory);
	}

	private <STATE> NestedWordAutomaton<LETTER, STATE> transformAutomaton(
			final INestedWordAutomaton<Integer, String> automaton, final Function<String, STATE> stateFunction,
			final IEmptyStackStateFactory<STATE> emptyStateFactory) {
		final NestedWordAutomaton<LETTER, STATE> result =
				new NestedWordAutomaton<>(mServices, mAlphabet, emptyStateFactory);
		final Set<STATE> initialStates =
				automaton.getInitialStates().stream().map(stateFunction).collect(Collectors.toSet());
		for (final String state : automaton.getFinalStates()) {
			final STATE stateT = stateFunction.apply(state);
			if (stateT != null) {
				result.addState(initialStates.contains(stateT), true, stateT);
			}
		}
		final ArrayDeque<String> dequeue = new ArrayDeque<>(automaton.getFinalStates());
		final Set<String> visited = new HashSet<>();
		while (!dequeue.isEmpty()) {
			final String state = dequeue.pop();
			final STATE stateT = stateFunction.apply(state);
			if (!visited.add(state) || stateT == null) {
				continue;
			}
			for (final IncomingInternalTransition<Integer, String> edge : automaton.internalPredecessors(state)) {
				final String pred = edge.getPred();
				final STATE predT = stateFunction.apply(pred);
				if (predT == null) {
					continue;
				}
				if (!result.contains(predT)) {
					result.addState(initialStates.contains(predT), false, predT);
				}
				result.addInternalTransition(predT, mOriginalTrace.get(edge.getLetter()), stateT);
				dequeue.add(pred);
			}
		}
		return result;

	}

	private List<Integer> getIntTrace(final List<LETTER> trace) {
		final List<Integer> intTrace = new ArrayList<>(trace.size());
		final Map<LETTER, Integer> counts = new HashMap<>();
		for (final LETTER action : trace) {
			final int count = counts.getOrDefault(action, 0);
			intTrace.add(mActions2Indices.get(action).get(count));
			counts.put(action, count + 1);
		}
		return intTrace;
	}

	private INestedWordAutomaton<Integer, String> buildMcrAutomaton(final List<Integer> intTrace)
			throws AutomataLibraryException {
		mLogger.info("Constructing automaton for MCR equivalence class.");
		// Determine all previous writes
		final List<Map<IProgramVar, Integer>> previousWrite = new ArrayList<>(intTrace.size());
		final Map<IProgramVar, Integer> lastWrittenBy = new HashMap<>();
		for (final int index : intTrace) {
			final Map<IProgramVar, Integer> previousWrites = new HashMap<>();
			final TransFormula transformula = mOriginalTrace.get(index).getTransformula();
			for (final IProgramVar read : transformula.getInVars().keySet()) {
				previousWrites.put(read, lastWrittenBy.get(read));
			}
			previousWrite.add(previousWrites);
			for (final IProgramVar written : transformula.getAssignedVars()) {
				lastWrittenBy.put(written, index);
			}
		}
		// Add all thread automata
		final List<INestedWordAutomaton<Integer, String>> automata = new ArrayList<>(getThreadAutomata());
		// Construct automata for each read to be preceded by the same write
		final StringFactory factory = new StringFactory();
		for (int j = 0; j < mOriginalTrace.size(); j++) {
			final int read = intTrace.get(j);
			final Map<IProgramVar, Integer> previousWrites = previousWrite.get(j);
			for (final Entry<IProgramVar, Integer> entry : previousWrites.entrySet()) {
				final Integer write = entry.getValue();
				final IProgramVar var = entry.getKey();
				final NestedWordAutomaton<Integer, String> nwa =
						new NestedWordAutomaton<>(mServices, mIntAlphabet, factory);
				final Set<Integer> writesOnVar = mVariables2Writes.getImage(var);
				nwa.addState(write == null, false, getState(1));
				nwa.addState(false, true, getState(2));
				nwa.addInternalTransition(getState(1), read, getState(2));
				if (write != null) {
					nwa.addState(true, false, getState(0));
					nwa.addInternalTransition(getState(0), write, getState(1));
				}
				for (int i = 0; i < mOriginalTrace.size(); i++) {
					if (i == read || write != null && i == write) {
						continue;
					}
					if (write != null) {
						nwa.addInternalTransition(getState(0), i, getState(0));
					}
					if (!writesOnVar.contains(i)) {
						nwa.addInternalTransition(getState(1), i, getState(1));
					}
					nwa.addInternalTransition(getState(2), i, getState(2));
				}
				automata.add(nwa);
			}
		}
		return intersectNwa(automata);
	}

	private INestedWordAutomaton<Integer, String> intersectNwa(
			final Collection<INestedWordAutomaton<Integer, String>> automata) throws AutomataLibraryException {
		mLogger.info("Started intersection.");
		final INestedWordAutomaton<Integer, String> result =
				new NestedWordAutomatonReachableStates<>(mServices, intersect(automata));
		mLogger.info("Finished intersection with " + result.sizeInformation());
		return result;
	}

	private static INwaOutgoingLetterAndTransitionProvider<Integer, String> intersect(
			final Collection<INestedWordAutomaton<Integer, String>> automata) throws AutomataLibraryException {
		final StringFactory factory = new StringFactory();
		INwaOutgoingLetterAndTransitionProvider<Integer, String> result = null;
		for (final INestedWordAutomaton<Integer, String> a : automata) {
			if (result == null) {
				result = a;
			} else {
				result = new IntersectNwa<>(result, a, factory, false);
			}
		}
		return result;
	}

	public NestedWordAutomaton<LETTER, IPredicate> buildInterpolantAutomaton(final List<LETTER> trace,
			final List<IPredicate> interpolants, final IInterpolantProvider<LETTER> ipProvider)
			throws AutomataLibraryException {
		final List<Integer> intTrace = getIntTrace(trace);
		assert isInterleaving(intTrace) : "Can only create an automaton for interleavings";
		final INestedWordAutomaton<Integer, String> automaton = buildMcrAutomaton(intTrace);
		mLogger.info("Constructing interpolant automaton by labelling MCR automaton with interpolants from "
				+ ipProvider.getClass().getSimpleName());
		final IPredicate truePred = mPredicateUnifier.getTruePredicate();
		final IPredicate falsePred = mPredicateUnifier.getFalsePredicate();
		final Map<String, IPredicate> states2Predicates = new HashMap<>();
		// Fill states2Predicates with the given interpolants
		String currentState = automaton.getInitialStates().iterator().next();
		states2Predicates.put(currentState, truePred);
		for (int i = 0; i < trace.size(); i++) {
			final Iterator<OutgoingInternalTransition<Integer, String>> succStates =
					automaton.internalSuccessors(currentState, intTrace.get(i)).iterator();
			if (!succStates.hasNext()) {
				throw new IllegalStateException("Trace is not present in the MCR automaton");
			}
			currentState = succStates.next().getSucc();
			states2Predicates.put(currentState, i < interpolants.size() ? interpolants.get(i) : falsePred);
		}
		// Get interpolants for the whole automaton and use them in the resulting automaton
		ipProvider.addInterpolants(transformAutomaton(automaton, x -> x, new StringFactory()), states2Predicates);
		final NestedWordAutomaton<LETTER, IPredicate> result =
				transformAutomaton(automaton, states2Predicates::get, mEmptyStackFactory);
		final Set<IPredicate> mcrIps = new HashSet<>(result.getStates());
		mcrIps.remove(truePred);
		mcrIps.remove(falsePred);
		mcrIps.removeAll(interpolants);
		mLogger.info("Construction finished. MCR generated " + mcrIps.size() + " new interpolants: " + mcrIps);
		return result;
	}

	private boolean isInterleaving(final List<Integer> intTrace) throws AutomataLibraryException {
		final Word<Integer> word = new Word<>(intTrace.toArray(new Integer[intTrace.size()]));
		return new Accepts<>(mServices, intersect(getThreadAutomata()), NestedWord.nestedWord(word)).getResult();
	}
}
