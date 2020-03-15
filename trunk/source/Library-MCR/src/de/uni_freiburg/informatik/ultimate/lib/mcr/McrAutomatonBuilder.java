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
import java.util.Set;
import java.util.Map.Entry;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IntersectNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.TermDomainOperationProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class McrAutomatonBuilder<LETTER extends IIcfgTransition<?>> {
	private final List<LETTER> mTrace;
	private final IPredicateUnifier mPredicateUnifier;
	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final AutomataLibraryServices mAutomataServices;
	private final ManagedScript mManagedScript;
	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;
	private final IEmptyStackStateFactory<IPredicate> mEmptyStackFactory;
	private final VpAlphabet<LETTER> mAlphabet;

	private final HashRelation<IProgramVar, Integer> mVariables2Writes;
	private final List<Map<IProgramVar, Integer>> mPreviousWrite;
	private final Map<String, List<Integer>> mThreads2SortedActions;

	private Collection<INestedWordAutomaton<Integer, String>> mThreadAutomata;

	public McrAutomatonBuilder(final List<LETTER> trace, final IPredicateUnifier predicateUnifier,
			final IEmptyStackStateFactory<IPredicate> emptyStackFactory, final ILogger logger,
			final Set<LETTER> alphabet, final IUltimateServiceProvider services, final ManagedScript managedScript,
			final XnfConversionTechnique xnfConversionTechnique,
			final SimplificationTechnique simplificationTechnique) {
		mTrace = trace;
		mLogger = logger;
		mPredicateUnifier = predicateUnifier;
		mServices = services;
		mAutomataServices = new AutomataLibraryServices(mServices);
		mManagedScript = managedScript;
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
		mEmptyStackFactory = emptyStackFactory;
		mAlphabet = new VpAlphabet<>(alphabet);
		mVariables2Writes = new HashRelation<>();
		mPreviousWrite = new ArrayList<>(trace.size());
		mThreads2SortedActions = new HashMap<>();
		preprocess();
	}

	private void preprocess() {
		final Map<IProgramVar, Integer> lastWrittenBy = new HashMap<>();
		for (int i = 0; i < mTrace.size(); i++) {
			final LETTER action = mTrace.get(i);
			final TransFormula transformula = action.getTransformula();
			final Set<IProgramVar> writtenVars = transformula.getAssignedVars();
			for (final IProgramVar var : writtenVars) {
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
			final Map<IProgramVar, Integer> previousWrites = new HashMap<>();
			for (final IProgramVar read : transformula.getInVars().keySet()) {
				previousWrites.put(read, lastWrittenBy.get(read));
			}
			mPreviousWrite.add(previousWrites);
			for (final IProgramVar written : writtenVars) {
				lastWrittenBy.put(written, i);
			}
		}
	}

	private static String getState(final int i) {
		return "q" + i;
	}

	private Collection<INestedWordAutomaton<Integer, String>> getThreadAutomata() {
		if (mThreadAutomata == null) {
			mThreadAutomata = new ArrayList<>();
			final Set<Integer> range = IntStream.range(0, mTrace.size()).boxed().collect(Collectors.toSet());
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

	public INestedWordAutomaton<Integer, String> buildMhbAutomaton() throws AutomataLibraryException {
		return intersect(getThreadAutomata(), new StringFactory(), mAutomataServices, mLogger);
	}

	public INestedWordAutomaton<Integer, String> buildMcrAutomaton() throws AutomataLibraryException {
		mLogger.info("Constructing automaton for MCR equivalence class.");
		final VpAlphabet<Integer> alphabet =
				new VpAlphabet<>(IntStream.range(0, mTrace.size()).boxed().collect(Collectors.toSet()));
		final List<INestedWordAutomaton<Integer, String>> automata = new ArrayList<>();
		automata.addAll(getThreadAutomata());
		final StringFactory factory = new StringFactory();
		// Construct automata for each read to be preceded by the same write
		for (int read = 0; read < mTrace.size(); read++) {
			final Map<IProgramVar, Integer> previousWrites = mPreviousWrite.get(read);
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
				for (int i = 0; i < mTrace.size(); i++) {
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
		return intersect(automata, factory, mAutomataServices, mLogger);
	}

	private static <LETTER, STATE> INestedWordAutomaton<LETTER, STATE> intersect(
			final Collection<INestedWordAutomaton<LETTER, STATE>> automata,
			final IIntersectionStateFactory<STATE> stateFactory, final AutomataLibraryServices services,
			final ILogger logger) throws AutomataLibraryException {
		logger.info("Started intersection.");
		INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> intersection = null;
		for (final INestedWordAutomaton<LETTER, STATE> a : automata) {
			if (intersection == null) {
				intersection = a;
			} else {
				intersection = new IntersectNwa<>(intersection, a, stateFactory, false);
			}
		}
		final INestedWordAutomaton<LETTER, STATE> result =
				new NestedWordAutomatonReachableStates<>(services, intersection);
		logger.info("Finished intersection with " + result.sizeInformation());
		return result;
	}

	public <STATE> NestedWordAutomaton<LETTER, IPredicate> buildInterpolantAutomaton(
			final List<INestedWordAutomaton<Integer, STATE>> automata,
			final List<QualifiedTracePredicates> tracePredicates) {
		assert automata.size() == tracePredicates.size();
		mLogger.info("Constructing interpolant automaton by labelling MCR automaton.");
		final NestedWordAutomaton<LETTER, IPredicate> result =
				new NestedWordAutomaton<>(mAutomataServices, mAlphabet, mEmptyStackFactory);
		final PredicateTransformer<Term, IPredicate, TransFormula> predicateTransformer =
				new PredicateTransformer<>(mManagedScript, new TermDomainOperationProvider(mServices, mManagedScript));
		int wpCalls = 0;
		result.addState(true, false, mPredicateUnifier.getTruePredicate());
		result.addState(false, true, mPredicateUnifier.getFalsePredicate());
		for (int j = 0; j < automata.size(); j++) {
			final INestedWordAutomaton<Integer, STATE> automaton = automata.get(j);
			final List<IPredicate> interpolants = tracePredicates.get(j).getPredicates();
			final Map<STATE, IPredicate> stateMap = new HashMap<>();
			// Fill stateMap and automaton with the given interpolants
			final LinkedList<STATE> queue = new LinkedList<>();
			STATE currentState = automaton.getInitialStates().iterator().next();
			IPredicate currentPredicate = mPredicateUnifier.getTruePredicate();
			stateMap.put(currentState, currentPredicate);
			queue.add(currentState);
			for (int i = 0; i < mTrace.size(); i++) {
				final Iterator<OutgoingInternalTransition<Integer, STATE>> succStates =
						automaton.internalSuccessors(currentState, i).iterator();
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
				result.addInternalTransition(currentPredicate, mTrace.get(i), nextPredicate);
				queue.add(currentState);
				currentPredicate = nextPredicate;
				stateMap.put(currentState, currentPredicate);
			}
			while (!queue.isEmpty()) {
				final STATE state = queue.remove();
				final IPredicate predicate = stateMap.get(state);
				if (predicate == null) {
					throw new IllegalStateException("Trying to visit an uncovered state.");
				}
				for (final IncomingInternalTransition<Integer, STATE> edge : automaton.internalPredecessors(state)) {
					final STATE predecessor = edge.getPred();
					IPredicate predPredicate = stateMap.get(predecessor);
					final LETTER action = mTrace.get(edge.getLetter());
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

	public <STATE> NestedWordAutomaton<LETTER, IPredicate> buildInterpolantAutomaton(
			final INestedWordAutomaton<Integer, STATE> automaton,
			final List<QualifiedTracePredicates> tracePredicates) {
		return buildInterpolantAutomaton(Collections.nCopies(tracePredicates.size(), automaton), tracePredicates);
	}
}
