package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.Map.Entry;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Intersect;
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.TermDomainOperationProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class IpAbStrategyModulMcr<LETTER extends IIcfgTransition<?>> implements IIpAbStrategyModule<LETTER> {
	private final List<LETTER> mTrace;
	private final IPredicateUnifier mPredicateUnifier;
	private final ILogger mLogger;
	private final AutomataLibraryServices mServices;
	private final ManagedScript mManagedScript;
	private final IEmptyStackStateFactory<IPredicate> mEmptyStackFactory;
	private final VpAlphabet<LETTER> mAlphabet;
	private final PredicateTransformer<Term, IPredicate, TransFormula> mPredicateTransformer;

	private final List<Set<IProgramVar>> mWrites2Variables;
	private final HashRelation<IProgramVar, Integer> mVariables2Writes;
	private final List<Map<IProgramVar, Integer>> mPreviousWrite;
	private final Map<String, List<Integer>> mThreads2SortedActions;
	private final List<Set<String>> mActions2Threads;

	private IpAbStrategyModuleResult<LETTER> mResult;

	public IpAbStrategyModulMcr(final List<LETTER> trace, final IPredicateUnifier predicateUnifier,
			final IEmptyStackStateFactory<IPredicate> emptyStackFactory, final ILogger logger,
			final ITraceCheckPreferences prefs, final Set<LETTER> alphabet) {
		mTrace = trace;
		mLogger = logger;
		mPredicateUnifier = predicateUnifier;
		final IUltimateServiceProvider services = prefs.getUltimateServices();
		mServices = new AutomataLibraryServices(services);
		mManagedScript = prefs.getCfgSmtToolkit().getManagedScript();
		mEmptyStackFactory = emptyStackFactory;
		mAlphabet = new VpAlphabet<>(alphabet);
		mPredicateTransformer =
				new PredicateTransformer<>(mManagedScript, new TermDomainOperationProvider(services, mManagedScript));
		mWrites2Variables = new ArrayList<>(trace.size());
		mVariables2Writes = new HashRelation<>();
		mPreviousWrite = new ArrayList<>(trace.size());
		mThreads2SortedActions = new HashMap<>();
		mActions2Threads = new ArrayList<>(trace.size());
		preprocess();
	}

	private void preprocess() {
		final Map<IProgramVar, Integer> lastWrittenBy = new HashMap<>();
		for (int i = 0; i < mTrace.size(); i++) {
			final LETTER action = mTrace.get(i);
			final TransFormula transformula = action.getTransformula();
			final Set<IProgramVar> writtenVars = transformula.getAssignedVars();
			mWrites2Variables.add(writtenVars);
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
			mActions2Threads.add(new HashSet<>(Arrays.asList(currentThread, nextThread)));
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

	private INestedWordAutomaton<Integer, ?> constructMcrAutomaton() throws AutomataLibraryException {
		mLogger.info("Constructing automaton for MCR equivalence class.");
		final Set<Integer> range = IntStream.range(0, mTrace.size()).boxed().collect(Collectors.toSet());
		final VpAlphabet<Integer> alphabet = new VpAlphabet<>(range);
		final List<INestedWordAutomaton<Integer, String>> automata = new ArrayList<>();
		final StringFactory factory = new StringFactory();
		// Construct automata for the MHB relation
		for (final List<Integer> threadActions : mThreads2SortedActions.values()) {
			final Set<Integer> otherActions = new HashSet<>(range);
			final NestedWordAutomaton<Integer, String> nwa = new NestedWordAutomaton<>(mServices, alphabet, factory);
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
			automata.add(nwa);
		}
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
						new NestedWordAutomaton<>(mServices, alphabet, factory);
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
		final INestedWordAutomaton<Integer, String> result = intersect(automata, factory, mServices);
		mLogger.info("Construction finished.");
		return result;
	}

	private static <LETTER, STATE> INestedWordAutomaton<LETTER, STATE> intersect(
			final Collection<INestedWordAutomaton<LETTER, STATE>> automata,
			final IIntersectionStateFactory<STATE> stateFactory, final AutomataLibraryServices services)
			throws AutomataLibraryException {
		INestedWordAutomaton<LETTER, STATE> result = null;
		for (final INestedWordAutomaton<LETTER, STATE> a : automata) {
			if (result == null) {
				result = a;
			} else {
				result = new Intersect<>(services, stateFactory, result, a).getResult();
			}
		}
		return result;
	}

	private static String getState(final int i) {
		return "q" + i;
	}

	private <STATE> NestedWordAutomaton<LETTER, IPredicate> constructInterpolantAutomaton(
			final List<IPredicate> interpolants, final INestedWordAutomaton<Integer, STATE> mcrAutomaton)
			throws AutomataLibraryException {
		mLogger.info("Constructing interpolant automaton by labelling MCR automaton.");
		final Map<STATE, IPredicate> stateMap = new HashMap<>();
		final NestedWordAutomaton<LETTER, IPredicate> result =
				new NestedWordAutomaton<>(mServices, mAlphabet, mEmptyStackFactory);
		IPredicate currentPredicate = mPredicateUnifier.getTruePredicate();
		result.addState(true, false, currentPredicate);
		result.addState(false, true, mPredicateUnifier.getFalsePredicate());
		// Fill stateMap and automaton with the given interpolants
		final LinkedList<STATE> queue = new LinkedList<>();
		STATE currentState = mcrAutomaton.getInitialStates().iterator().next();
		stateMap.put(currentState, currentPredicate);
		queue.add(currentState);
		for (int i = 0; i < mTrace.size(); i++) {
			final Iterator<OutgoingInternalTransition<Integer, STATE>> succStates =
					mcrAutomaton.internalSuccessors(currentState, i).iterator();
			if (!succStates.hasNext()) {
				throw new IllegalStateException("Trace is not present in the MCR automaton");
			}
			currentState = succStates.next().getSucc();
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
		int preCalls = 0;
		while (!queue.isEmpty()) {
			final STATE state = queue.remove();
			final IPredicate predicate = stateMap.get(state);
			if (predicate == null) {
				throw new IllegalStateException("Trying to visit an uncovered state.");
			}
			for (final IncomingInternalTransition<Integer, STATE> edge : mcrAutomaton.internalPredecessors(state)) {
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
						// Otherwise calculate pre and add it as a state if necessary
						preCalls++;
						final Term pre = mPredicateTransformer.pre(predicate, action.getTransformula());
						predPredicate = mPredicateUnifier.getOrConstructPredicate(pre);
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
		mLogger.info("Construction finished. Needed to calculate pre " + preCalls + " times.");
		return result;
	}

	@Override
	public IpAbStrategyModuleResult<LETTER> buildInterpolantAutomaton(final List<QualifiedTracePredicates> perfectIpps,
			final List<QualifiedTracePredicates> imperfectIpps) throws AutomataOperationCanceledException {
		if (mResult == null) {
			try {
				final INestedWordAutomaton<Integer, ?> mcrAutomaton = constructMcrAutomaton();
				final QualifiedTracePredicates qtp = perfectIpps.isEmpty() ? imperfectIpps.get(0) : perfectIpps.get(0);
				return new IpAbStrategyModuleResult<>(constructInterpolantAutomaton(qtp.getPredicates(), mcrAutomaton),
						Collections.singletonList(qtp));
			} catch (final AutomataLibraryException e) {
				throw new RuntimeException(e);
			}
		}
		return mResult;
	}
}
