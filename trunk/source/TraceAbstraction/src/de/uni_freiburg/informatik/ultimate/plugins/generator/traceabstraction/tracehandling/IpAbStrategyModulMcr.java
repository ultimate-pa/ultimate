package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Intersect;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveDeadEnds;
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

	private final HashRelation<LETTER, IProgramVar> mReads2Variables;
	private final HashRelation<LETTER, IProgramVar> mWrites2Variables;
	private final HashRelation<IProgramVar, LETTER> mVariables2Writes;
	private final Map<LETTER, Map<IProgramVar, LETTER>> mPreviousWrite;
	private final Map<String, List<LETTER>> mThreads2SortedActions;
	private final HashRelation<LETTER, String> mActions2Threads;

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
		mReads2Variables = new HashRelation<>();
		mWrites2Variables = new HashRelation<>();
		mVariables2Writes = new HashRelation<>();
		mPreviousWrite = new HashMap<>();
		mThreads2SortedActions = new HashMap<>();
		mActions2Threads = new HashRelation<>();
		preprocess();
	}

	// TODO: Use indices of actions in trace as unique keys
	private void preprocess() {
		final Map<IProgramVar, LETTER> lastWrittenBy = new HashMap<>();
		for (final LETTER action : mTrace) {
			final TransFormula transformula = action.getTransformula();
			mReads2Variables.addAllPairs(action, transformula.getInVars().keySet());
			for (final IProgramVar var : transformula.getAssignedVars()) {
				mVariables2Writes.addPair(var, action);
				mWrites2Variables.addPair(action, var);
			}
			final String currentThread = action.getPrecedingProcedure();
			mActions2Threads.addPair(action, currentThread);
			List<LETTER> threadActions = mThreads2SortedActions.get(currentThread);
			if (threadActions == null) {
				threadActions = new ArrayList<>();
				mThreads2SortedActions.put(currentThread, threadActions);
			}
			threadActions.add(action);
			final String nextThread = action.getSucceedingProcedure();
			if (currentThread != nextThread) {
				mActions2Threads.addPair(action, nextThread);
				threadActions = mThreads2SortedActions.get(nextThread);
				if (threadActions == null) {
					threadActions = new ArrayList<>();
					mThreads2SortedActions.put(nextThread, threadActions);
				}
				threadActions.add(action);
			}
			final Set<IProgramVar> reads = mReads2Variables.getImage(action);
			if (!reads.isEmpty()) {
				final Map<IProgramVar, LETTER> previousWrites = new HashMap<>();
				for (final IProgramVar read : reads) {
					previousWrites.put(read, lastWrittenBy.get(read));
				}
				mPreviousWrite.put(action, previousWrites);
			}
			for (final IProgramVar written : mWrites2Variables.getImage(action)) {
				lastWrittenBy.put(written, action);
			}
		}
	}

	private INestedWordAutomaton<LETTER, String> constructMcrAutomaton(final List<IPredicate> interpolants)
			throws AutomataLibraryException {
		final List<INestedWordAutomaton<LETTER, String>> automata = new ArrayList<>();
		final StringFactory factory = new StringFactory();
		// Construct automata for the MHB relation
		for (final List<LETTER> threadActions : mThreads2SortedActions.values()) {
			final Set<LETTER> otherActions = new HashSet<>(mTrace);
			final NestedWordAutomaton<LETTER, String> nwa = new NestedWordAutomaton<>(mServices, mAlphabet, factory);
			otherActions.removeAll(threadActions);
			final String initial = getState(0);
			nwa.addState(true, false, initial);
			for (final LETTER otherAction : otherActions) {
				nwa.addInternalTransition(initial, otherAction, initial);
			}
			for (int i = 0; i < threadActions.size(); i++) {
				final String currentState = getState(i);
				final String nextState = getState(i + 1);
				nwa.addState(false, i + 1 == threadActions.size(), nextState);
				nwa.addInternalTransition(currentState, threadActions.get(i), nextState);
				for (final LETTER otherAction : otherActions) {
					nwa.addInternalTransition(nextState, otherAction, nextState);
				}
			}
			automata.add(nwa);
		}
		// Construct automata for each read to be preceded by the specific (or a "similar") write
		for (final LETTER read : mTrace) {
			final Map<IProgramVar, LETTER> previousWrites = mPreviousWrite.get(read);
			if (previousWrites == null) {
				continue;
			}
			for (final Entry<IProgramVar, LETTER> entry : previousWrites.entrySet()) {
				final LETTER write = entry.getValue();
				final IProgramVar var = entry.getKey();
				final NestedWordAutomaton<LETTER, String> nwa =
						new NestedWordAutomaton<>(mServices, mAlphabet, factory);
				final Set<LETTER> writesOnVar = mVariables2Writes.getImage(var);
				nwa.addState(true, false, getState(0));
				nwa.addState(false, true, getState(2));
				if (write == null) {
					nwa.addInternalTransition(getState(0), read, getState(2));
					for (final LETTER action : mTrace) {
						if (!writesOnVar.contains(action)) {
							nwa.addInternalTransition(getState(0), action, getState(0));
						}
						nwa.addInternalTransition(getState(2), action, getState(2));
					}
				} else {
					nwa.addState(false, false, getState(1));
					// Add q0 -w-> q1
					nwa.addInternalTransition(getState(0), write, getState(1));
					// Add q1 -r-> q2
					nwa.addInternalTransition(getState(1), read, getState(2));
					// Add the self-loops
					for (final LETTER action : mTrace) {
						nwa.addInternalTransition(getState(0), action, getState(0));
						nwa.addInternalTransition(getState(2), action, getState(2));
						if (!writesOnVar.contains(action)) {
							nwa.addInternalTransition(getState(1), action, getState(1));
						}
					}
				}
				automata.add(nwa);
			}
		}
		return intersect(automata, factory);
	}

	private <STATE> INestedWordAutomaton<LETTER, STATE> intersect(
			final Collection<INestedWordAutomaton<LETTER, STATE>> automata,
			final IIntersectionStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		if (automata.isEmpty()) {
			return new NestedWordAutomaton<>(mServices, mAlphabet, stateFactory);
		}
		INestedWordAutomaton<LETTER, STATE> result = null;
		for (final INestedWordAutomaton<LETTER, STATE> a : automata) {
			if (result == null) {
				result = a;
			} else {
				final Intersect<LETTER, STATE> intersect = new Intersect<>(mServices, stateFactory, result, a);
				result = intersect.getResult();
			}
		}
		final INestedWordAutomaton<LETTER, STATE> simplified = new RemoveDeadEnds<>(mServices, result).getResult();
		mLogger.info(simplified);
		return simplified;
	}

	private static String getState(final int i) {
		return "q" + i;
	}

	private NestedWordAutomaton<LETTER, IPredicate> constructInterpolantAutomaton(final List<IPredicate> interpolants)
			throws AutomataLibraryException {
		final INestedWordAutomaton<LETTER, String> mcrAutomaton = constructMcrAutomaton(interpolants);
		final Map<String, IPredicate> stateMap = new HashMap<>();
		// Fill stateMap with the given interpolants
		final LinkedList<String> queue = new LinkedList<>();
		String currentState = mcrAutomaton.getInitialStates().iterator().next();
		stateMap.put(currentState, mPredicateUnifier.getTruePredicate());
		queue.add(currentState);
		for (int i = 0; i < interpolants.size(); i++) {
			final LETTER action = mTrace.get(i);
			currentState = getSuccessor(currentState, action, mcrAutomaton);
			stateMap.put(currentState, mPredicateUnifier.getOrConstructPredicate(interpolants.get(i)));
			queue.add(currentState);
		}
		final String finalState = mcrAutomaton.getFinalStates().iterator().next();
		stateMap.put(finalState, mPredicateUnifier.getFalsePredicate());
		final Set<String> visited = new HashSet<>();
		while (!queue.isEmpty()) {
			final String state = queue.remove();
			final IPredicate predicate = stateMap.get(state);
			if (predicate == null || !visited.add(state)) {
				continue;
			}
			for (final IncomingInternalTransition<LETTER, String> edge : mcrAutomaton.internalPredecessors(state)) {
				final String predecessor = edge.getPred();
				queue.add(predecessor);
				if (stateMap.containsKey(predecessor)) {
					continue;
				}
				final Term pre = mPredicateTransformer.pre(predicate, edge.getLetter().getTransformula());
				// TODO: Try to cover more states as before?
				stateMap.put(predecessor, mPredicateUnifier.getOrConstructPredicate(pre));
			}
		}
		return createAutomatonFromMap(mcrAutomaton, stateMap);
	}

	private NestedWordAutomaton<LETTER, IPredicate> createAutomatonFromMap(
			final INestedWordAutomaton<LETTER, String> mcrAutomaton, final Map<String, IPredicate> stateMap) {
		final NestedWordAutomaton<LETTER, IPredicate> result =
				new NestedWordAutomaton<>(mServices, mAlphabet, mEmptyStackFactory);
		// Add all the new predicates as states
		result.addState(true, false, mPredicateUnifier.getTruePredicate());
		result.addState(false, true, mPredicateUnifier.getFalsePredicate());
		for (final IPredicate predicate : stateMap.values()) {
			if (!result.contains(predicate)) {
				result.addState(false, false, predicate);
			}
		}
		for (final Entry<String, IPredicate> entry : stateMap.entrySet()) {
			final String oldState = entry.getKey();
			for (final OutgoingInternalTransition<LETTER, String> edge : mcrAutomaton.internalSuccessors(oldState)) {
				final String succ = edge.getSucc();
				result.addInternalTransition(entry.getValue(), edge.getLetter(), stateMap.get(succ));
			}
		}
		mLogger.info(result);
		return result;
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

	@Override
	public IpAbStrategyModuleResult<LETTER> buildInterpolantAutomaton(final List<QualifiedTracePredicates> perfectIpps,
			final List<QualifiedTracePredicates> imperfectIpps) throws AutomataOperationCanceledException {
		if (mResult == null) {
			try {
				final QualifiedTracePredicates qtp = perfectIpps.isEmpty() ? imperfectIpps.get(0) : perfectIpps.get(0);
				return new IpAbStrategyModuleResult<>(constructInterpolantAutomaton(qtp.getPredicates()),
						Collections.singletonList(qtp));
			} catch (final AutomataLibraryException e) {
				throw new RuntimeException(e);
			}
		}
		return mResult;
	}
}
