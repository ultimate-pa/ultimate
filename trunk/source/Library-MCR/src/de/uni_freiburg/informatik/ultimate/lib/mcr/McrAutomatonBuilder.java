package de.uni_freiburg.informatik.ultimate.lib.mcr;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.Stack;
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
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
	private final AutomataLibraryServices mAutomataServices;
	private final IEmptyStackStateFactory<IPredicate> mEmptyStackFactory;
	private final IHoareTripleChecker mHtc;
	private final VpAlphabet<LETTER> mAlphabet;
	private final VpAlphabet<Integer> mIntAlphabet;

	private List<INestedWordAutomaton<Integer, String>> mThreadAutomata;

	private final HashRelation<IProgramVar, Integer> mVariables2Writes;
	private final Map<LETTER, List<Integer>> mActions2Indices;
	private final Map<String, List<Integer>> mThreads2SortedActions;

	public McrAutomatonBuilder(final List<LETTER> trace, final IPredicateUnifier predicateUnifier,
			final IEmptyStackStateFactory<IPredicate> emptyStackFactory, final ILogger logger,
			final VpAlphabet<LETTER> alphabet, final IUltimateServiceProvider services, final IHoareTripleChecker htc) {
		mOriginalTrace = trace;
		mLogger = logger;
		mPredicateUnifier = predicateUnifier;
		mAutomataServices = new AutomataLibraryServices(services);
		mEmptyStackFactory = emptyStackFactory;
		mHtc = htc;
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
			List<Integer> currentIndices = mActions2Indices.get(action);
			if (currentIndices == null) {
				currentIndices = new ArrayList<>();
				mActions2Indices.put(action, currentIndices);
			}
			currentIndices.add(i);
			for (final IProgramVar var : action.getTransformula().getAssignedVars()) {
				mVariables2Writes.addPair(var, i);
			}
			final String currentThread = action.getPrecedingProcedure();
			List<Integer> threadActions = mThreads2SortedActions.get(currentThread);
			if (threadActions == null) {
				threadActions = new ArrayList<>();
				mThreads2SortedActions.put(currentThread, threadActions);
			}
			threadActions.add(i);
			final String nextThread = action.getSucceedingProcedure();
			if (currentThread != nextThread) {
				threadActions = mThreads2SortedActions.get(nextThread);
				if (threadActions == null) {
					threadActions = new ArrayList<>();
					mThreads2SortedActions.put(nextThread, threadActions);
				}
				threadActions.add(i);
			}
		}
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
						new NestedWordAutomaton<>(mAutomataServices, mIntAlphabet, factory);
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
		final NestedWordAutomaton<LETTER, IPredicate> result =
				new NestedWordAutomaton<>(mAutomataServices, mAlphabet, mEmptyStackFactory);
		final INestedWordAutomaton<Integer, String> intAutomaton = intersectNwa(getThreadAutomata());
		final Set<String> initialStates = intAutomaton.getInitialStates();
		final Set<String> finalStates = new HashSet<>(intAutomaton.getFinalStates());
		final LinkedList<String> queue = new LinkedList<>(finalStates);
		final Map<String, IPredicate> states2Predicates = new HashMap<>();
		final Term trueTerm = mPredicateUnifier.getTruePredicate().getFormula();
		for (final String state : intAutomaton.getStates()) {
			final IPredicate predicate = predicateFactory.newSPredicate(null, trueTerm);
			states2Predicates.put(state, predicate);
			result.addState(initialStates.contains(state), finalStates.contains(state), predicate);
		}
		final Set<String> visited = new HashSet<>();
		while (!queue.isEmpty()) {
			final String state = queue.remove();
			if (!visited.add(state)) {
				continue;
			}
			for (final IncomingInternalTransition<Integer, String> edge : intAutomaton.internalPredecessors(state)) {
				final LETTER letter = mOriginalTrace.get(edge.getLetter());
				result.addInternalTransition(states2Predicates.get(edge.getPred()), letter,
						states2Predicates.get(state));
				queue.add(edge.getPred());
			}
		}
		return result;
	}

	private boolean isInterleaving(final List<Integer> intTrace) throws AutomataLibraryException {
		final INwaOutgoingLetterAndTransitionProvider<Integer, String> mhbAutomaton = intersect(getThreadAutomata());
		final Word<Integer> word = new Word<>(intTrace.toArray(new Integer[intTrace.size()]));
		return new Accepts<>(mAutomataServices, mhbAutomaton, NestedWord.nestedWord(word)).getResult();
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
						new NestedWordAutomaton<>(mAutomataServices, mIntAlphabet, factory);
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
				new NestedWordAutomatonReachableStates<>(mAutomataServices, intersect(automata));
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
			final Collection<QualifiedTracePredicates> tracePredicates,
			final IInterpolantProvider<LETTER> interpolantProvider) throws AutomataLibraryException {
		final List<Integer> intTrace = getIntTrace(trace);
		assert isInterleaving(intTrace) : "Can only create an automaton for interleavings";
		final INestedWordAutomaton<Integer, String> automaton = buildMcrAutomaton(intTrace);
		mLogger.info("Constructing interpolant automaton by labelling MCR automaton.");
		final NestedWordAutomaton<LETTER, IPredicate> result =
				new NestedWordAutomaton<>(mAutomataServices, mAlphabet, mEmptyStackFactory);
		final IPredicate truePred = mPredicateUnifier.getTruePredicate();
		final IPredicate falsePred = mPredicateUnifier.getFalsePredicate();
		result.addState(true, false, truePred);
		result.addState(false, true, falsePred);
		final Set<IPredicate> initIps = new HashSet<>();
		initIps.add(truePred);
		initIps.add(falsePred);
		for (final QualifiedTracePredicates tp : tracePredicates) {
			final List<IPredicate> interpolants = tp.getPredicates();
			initIps.addAll(interpolants);
			final Map<String, IPredicate> stateMap = new HashMap<>();
			// Fill stateMap and automaton with the given interpolants
			String currentState = automaton.getInitialStates().iterator().next();
			IPredicate currentPredicate = truePred;
			stateMap.put(currentState, currentPredicate);
			for (int i = 0; i < trace.size(); i++) {
				final int index = intTrace.get(i);
				final Iterator<OutgoingInternalTransition<Integer, String>> succStates =
						automaton.internalSuccessors(currentState, index).iterator();
				if (!succStates.hasNext()) {
					throw new IllegalStateException("Trace is not present in the MCR automaton");
				}
				currentState = succStates.next().getSucc();
				final IPredicate nextPredicate = i == interpolants.size() ? falsePred
						: mPredicateUnifier.getOrConstructPredicate(interpolants.get(i));
				addTransition(result, currentPredicate, mOriginalTrace.get(index), nextPredicate);
				currentPredicate = nextPredicate;
				stateMap.put(currentState, currentPredicate);
			}
			// Find all paths containing states without interpolants and get some
			final Stack<List<LETTER>> traceStack = new Stack<>();
			final Stack<List<String>> stateStack = new Stack<>();
			traceStack.push(Collections.emptyList());
			stateStack.push(Collections.singletonList(automaton.getInitialStates().iterator().next()));
			while (!traceStack.empty()) {
				final List<LETTER> currentTrace = traceStack.pop();
				final List<String> currentStates = stateStack.pop();
				final String lastState = currentStates.get(currentStates.size() - 1);
				for (final OutgoingInternalTransition<Integer, String> outgoing : automaton
						.internalSuccessors(lastState)) {
					final LETTER action = mOriginalTrace.get(outgoing.getLetter());
					final String nextState = outgoing.getSucc();
					final IPredicate nextPredicate = stateMap.get(nextState);
					final List<LETTER> newTrace = DataStructureUtils.concat(currentTrace, action);
					if (nextPredicate != null) {
						if (!currentTrace.isEmpty()) {
							final String prevState = currentStates.get(0);
							final IPredicate precondition = stateMap.get(prevState);
							// TODO: Maybe use this later?
							// final int start = Math.max(visitedStates.indexOf(prevState) - 1, 0);
							// final int end = Math.floorMod(visitedStates.indexOf(nextState) - 1, interpolants.size());
							// final Set<TermVariable> vars = interpolants.subList(start, end + 1).stream()
							// .flatMap(x -> x.getVars().stream().map(IProgramVar::getTermVariable))
							// .collect(Collectors.toSet());
							// TODO: Optimization: Try to reuse previous interpolants
							final IPredicate[] ips =
									interpolantProvider.getInterpolants(precondition, newTrace, nextPredicate);
							IPredicate lastIp = precondition;
							for (int i = 0; i < ips.length; i++) {
								final IPredicate ip = ips[i];
								stateMap.put(currentStates.get(i + 1), ip);
								addTransition(result, lastIp, currentTrace.get(i), ip);
								lastIp = ip;
							}
						}
						// TODO: This is only a workaround!
						final IPredicate lastPredicate = stateMap.get(lastState);
						if (!currentTrace.isEmpty() || checkHoareTriple(lastPredicate, action, nextPredicate)) {
							addTransition(result, lastPredicate, action, nextPredicate);
						}
						stateMap.put(nextState, nextPredicate);
						traceStack.push(Collections.emptyList());
						stateStack.push(Collections.singletonList(nextState));
					} else {
						traceStack.push(newTrace);
						stateStack.push(DataStructureUtils.concat(currentStates, nextState));
					}
				}
			}
		}
		final Set<IPredicate> mcrIps = DataStructureUtils.difference(result.getStates(), initIps);
		mLogger.info("Construction finished. MCR generated " + mcrIps.size() + " new interpolants: " + mcrIps);
		return result;
	}

	private void addTransition(final NestedWordAutomaton<LETTER, IPredicate> automaton, final IPredicate pred,
			final LETTER action, final IPredicate succ) {
		assert checkHoareTriple(pred, action, succ) : "Invalid hoare triple {" + pred + "} " + action + " {" + succ
				+ "}";
		if (!automaton.contains(succ)) {
			automaton.addState(false, false, succ);
		}
		automaton.addInternalTransition(pred, action, succ);
	}

	private boolean checkHoareTriple(final IPredicate precondition, final LETTER action,
			final IPredicate postcondition) {
		return mHtc.checkInternal(precondition, (IInternalAction) action, postcondition) != Validity.INVALID;
	}
}
