package de.uni_freiburg.informatik.ultimate.lib.mcr;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.TermDomainOperationProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class McrAutomatonBuilder<LETTER extends IIcfgTransition<?>> {
	private final List<LETTER> mOriginalTrace;
	private final IPredicateUnifier mPredicateUnifier;
	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final AutomataLibraryServices mAutomataServices;
	private final ManagedScript mManagedScript;
	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;
	private final IEmptyStackStateFactory<IPredicate> mEmptyStackFactory;
	private final VpAlphabet<LETTER> mAlphabet;

	private List<INestedWordAutomaton<Integer, String>> mThreadAutomata;

	private final HashRelation<IProgramVar, Integer> mVariables2Writes;
	private final Map<LETTER, List<Integer>> mActions2Indices;
	private final Map<String, List<Integer>> mThreads2SortedActions;

	public McrAutomatonBuilder(final List<LETTER> trace, final IPredicateUnifier predicateUnifier,
			final IEmptyStackStateFactory<IPredicate> emptyStackFactory, final ILogger logger,
			final VpAlphabet<LETTER> alphabet, final IUltimateServiceProvider services,
			final ManagedScript managedScript, final XnfConversionTechnique xnfConversionTechnique,
			final SimplificationTechnique simplificationTechnique) {
		mOriginalTrace = trace;
		mLogger = logger;
		mPredicateUnifier = predicateUnifier;
		mServices = services;
		mAutomataServices = new AutomataLibraryServices(mServices);
		mManagedScript = managedScript;
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
		mEmptyStackFactory = emptyStackFactory;
		mAlphabet = alphabet;
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
			final Set<Integer> range = IntStream.range(0, mOriginalTrace.size()).boxed().collect(Collectors.toSet());
			final VpAlphabet<Integer> alphabet = new VpAlphabet<>(range);
			final StringFactory factory = new StringFactory();
			// Construct automata for the MHB relation
			for (final List<Integer> threadActions : mThreads2SortedActions.values()) {
				final Set<Integer> otherActions = new HashSet<>(range);
				final NestedWordAutomaton<Integer, String> nwa =
						new NestedWordAutomaton<>(mAutomataServices, alphabet, factory);
				otherActions.removeAll(threadActions);
				nwa.addState(true, false, getState(0));
				for (final Integer otherAction : otherActions) {
					nwa.addInternalTransition(getState(0), otherAction, getState(0));
				}
				for (int i = 0; i < threadActions.size(); i++) {
					nwa.addState(false, i + 1 == threadActions.size(), getState(i + 1));
					nwa.addInternalTransition(getState(i), threadActions.get(i), getState(i + 1));
					for (final Integer otherAction : otherActions) {
						nwa.addInternalTransition(getState(i + 1), otherAction, getState(i + 1));
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
		final Term trueTerm = mManagedScript.getScript().term("true");
		for (final String state : intAutomaton.getStates()) {
			// final IPredicate predicate = predicateFactory.newDebugPredicate(state);
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
		for (int i = 0; i < intTrace.size(); i++) {
			final Map<IProgramVar, Integer> previousWrites = new HashMap<>();
			final TransFormula transformula = mOriginalTrace.get(intTrace.get(i)).getTransformula();
			for (final IProgramVar read : transformula.getInVars().keySet()) {
				previousWrites.put(read, lastWrittenBy.get(read));
			}
			previousWrite.add(previousWrites);
			for (final IProgramVar written : transformula.getAssignedVars()) {
				lastWrittenBy.put(written, intTrace.get(i));
			}
		}
		final VpAlphabet<Integer> alphabet =
				new VpAlphabet<>(IntStream.range(0, mOriginalTrace.size()).boxed().collect(Collectors.toSet()));
		// Add all thread automata
		final List<INestedWordAutomaton<Integer, String>> automata = new ArrayList<>(getThreadAutomata());
		// Construct automata for each read to be preceded by the same write
		final StringFactory factory = new StringFactory();
		for (int read = 0; read < mOriginalTrace.size(); read++) {
			final Map<IProgramVar, Integer> previousWrites = previousWrite.get(read);
			if (previousWrites == null) {
				continue;
			}
			for (final Entry<IProgramVar, Integer> entry : previousWrites.entrySet()) {
				final Integer write = entry.getValue();
				final IProgramVar var = entry.getKey();
				final NestedWordAutomaton<Integer, String> nwa =
						new NestedWordAutomaton<>(mAutomataServices, alphabet, factory);
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
			final Collection<QualifiedTracePredicates> tracePredicates) throws AutomataLibraryException {
		final List<Integer> intTrace = getIntTrace(trace);
		assert isInterleaving(intTrace) : "Can only create an automaton for interleavings";
		final INestedWordAutomaton<Integer, String> automaton = buildMcrAutomaton(intTrace);
		mLogger.info("Constructing interpolant automaton by labelling MCR automaton.");
		final NestedWordAutomaton<LETTER, IPredicate> result =
				new NestedWordAutomaton<>(mAutomataServices, mAlphabet, mEmptyStackFactory);
		final PredicateTransformer<Term, IPredicate, TransFormula> predicateTransformer =
				new PredicateTransformer<>(mManagedScript, new TermDomainOperationProvider(mServices, mManagedScript));
		int wpCalls = 0;
		result.addState(true, false, mPredicateUnifier.getTruePredicate());
		result.addState(false, true, mPredicateUnifier.getFalsePredicate());
		for (final QualifiedTracePredicates tp : tracePredicates) {
			final List<IPredicate> interpolants = tp.getPredicates();
			final Map<String, IPredicate> stateMap = new HashMap<>();
			// Fill stateMap and automaton with the given interpolants
			final LinkedList<String> queue = new LinkedList<>();
			String currentState = automaton.getInitialStates().iterator().next();
			IPredicate currentPredicate = mPredicateUnifier.getTruePredicate();
			stateMap.put(currentState, currentPredicate);
			queue.add(currentState);
			for (int i = 0; i < trace.size(); i++) {
				final int index = intTrace.get(i);
				final Iterator<OutgoingInternalTransition<Integer, String>> succStates =
						automaton.internalSuccessors(currentState, index).iterator();
				if (!succStates.hasNext()) {
					throw new IllegalStateException("Trace is not present in the MCR automaton");
				}
				currentState = succStates.next().getSucc();
				// TODO: Check interpolants.get(i) for "useless" (not future-live) variables and quantifiy them away
				// (using exists) and show a warning
				final IPredicate nextPredicate = i == interpolants.size() ? mPredicateUnifier.getFalsePredicate()
						: mPredicateUnifier.getOrConstructPredicate(interpolants.get(i));
				if (!result.contains(nextPredicate)) {
					result.addState(false, false, nextPredicate);
				}
				result.addInternalTransition(currentPredicate, mOriginalTrace.get(index), nextPredicate);
				queue.add(currentState);
				currentPredicate = nextPredicate;
				stateMap.put(currentState, currentPredicate);
			}
			while (!queue.isEmpty()) {
				final String state = queue.remove();
				final IPredicate predicate = stateMap.get(state);
				if (predicate == null) {
					throw new IllegalStateException("Trying to visit an uncovered state.");
				}
				for (final IncomingInternalTransition<Integer, String> edge : automaton.internalPredecessors(state)) {
					final String predecessor = edge.getPred();
					IPredicate predPredicate = stateMap.get(predecessor);
					final LETTER action = mOriginalTrace.get(edge.getLetter());
					// If the predecessor is already labeled, we can continue
					if (predPredicate == null) {
						queue.add(predecessor);
						final Iterator<IncomingInternalTransition<LETTER, IPredicate>> predicateEdges =
								result.internalPredecessors(predicate, action).iterator();
						// If there is a predecessor present in the result automaton, we can just use it
						if (predicateEdges.hasNext()) {
							predPredicate = predicateEdges.next().getPred();
						} else {
							// Otherwise calculate wp and add it as a state if necessary
							wpCalls++;
							final Term wp =
									predicateTransformer.weakestPrecondition(predicate, action.getTransformula());
							final Term wpEliminated = PartialQuantifierElimination.tryToEliminate(mServices, mLogger,
									mManagedScript, wp, mSimplificationTechnique, mXnfConversionTechnique);
							predPredicate = mPredicateUnifier.getOrConstructPredicate(wpEliminated);
							if (!result.contains(predPredicate)) {
								result.addState(false, false, predPredicate);
							}
						}
						stateMap.put(predecessor, predPredicate);
					}
					// Add the corresponding transition
					result.addInternalTransition(predPredicate, action, predicate);
				}
			}
		}
		mLogger.info("Construction finished. Needed to calculate wp " + wpCalls + " times.");
		return result;
	}
}
