package de.uni_freiburg.informatik.ultimate.lib.mcr;

import java.math.BigInteger;
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
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Intersect;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveDeadEnds;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.StringFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.IInterpolatingTraceCheck;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.InterpolantComputationStatus;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class Mcr<LETTER extends IIcfgTransition<?>> implements IInterpolatingTraceCheck<LETTER> {
	private final ILogger mLogger;
	private final IPredicateUnifier mPredicateUnifier;
	private final IUltimateServiceProvider mServices;
	private final ManagedScript mManagedScript;
	private final IEmptyStackStateFactory<IPredicate> mEmptyStackStateFactory;

	private final HashRelation<LETTER, IProgramVar> mReads2Variables;
	private final HashRelation<LETTER, IProgramVar> mWrites2Variables;
	private final HashRelation<IProgramVar, LETTER> mVariables2Writes;
	private final Map<LETTER, Map<IProgramVar, LETTER>> mPreviousWrite;
	private final Map<LETTER, Term> mActions2TermVars;
	private final Map<String, List<LETTER>> mThreads2SortedActions;
	private final HashRelation<LETTER, String> mActions2Threads;

	private final IProofProvider<LETTER> mProofProvider;
	private final AutomataLibraryServices mAutomataServices;
	private final VpAlphabet<LETTER> mAlphabet;
	private final McrTraceCheckResult<LETTER> mResult;
	private final IWriteRelation<LETTER> mWriteRelation;

	public Mcr(final ILogger logger, final ITraceCheckPreferences prefs, final IPredicateUnifier predicateUnifier,
			final IEmptyStackStateFactory<IPredicate> emptyStackStateFactory, final List<LETTER> trace,
			final Set<LETTER> alphabet, final IProofProvider<LETTER> proofProvider,
			final IWriteRelation<LETTER> writeRelation) throws AutomataLibraryException {
		mLogger = logger;
		mPredicateUnifier = predicateUnifier;
		mServices = prefs.getUltimateServices();
		mAutomataServices = new AutomataLibraryServices(mServices);
		mAlphabet = new VpAlphabet<>(alphabet);
		mManagedScript = prefs.getCfgSmtToolkit().getManagedScript();
		mEmptyStackStateFactory = emptyStackStateFactory;
		mProofProvider = proofProvider;
		mWriteRelation = writeRelation;
		mReads2Variables = new HashRelation<>();
		mWrites2Variables = new HashRelation<>();
		mVariables2Writes = new HashRelation<>();
		mPreviousWrite = new HashMap<>();
		mActions2TermVars = new HashMap<>();
		mThreads2SortedActions = new HashMap<>();
		mActions2Threads = new HashRelation<>();
		// Explore all the interleavings of trace
		mResult = exploreInterleavings(trace);
	}

	private McrTraceCheckResult<LETTER> exploreInterleavings(final List<LETTER> initialTrace)
			throws AutomataLibraryException {
		getReadsAndWrites(initialTrace);
		final LinkedList<List<LETTER>> queue = new LinkedList<>();
		final Set<List<LETTER>> visited = new HashSet<>();
		queue.add(initialTrace);
		final McrInterpolantAutomatonBuilder<LETTER> automatonBuilder =
				new McrInterpolantAutomatonBuilder<>(mAutomataServices, mAlphabet, mEmptyStackStateFactory,
						mProofProvider, getPrecondition(), getPostcondition(), mPredicateUnifier, mLogger);
		IPredicate[] initialInterpolants = null;
		while (!queue.isEmpty()) {
			final List<LETTER> trace = queue.remove();
			if (!visited.add(trace)) {
				continue;
			}
			preprocess(trace);
			List<IPredicate> interpolants = automatonBuilder.getInterpolantsIfAccepted(trace);
			if (interpolants == null) {
				final Pair<LBool, QualifiedTracePredicates> proof =
						mProofProvider.getProof(trace, getPrecondition(), getPostcondition());
				final LBool feasibility = proof.getFirst();
				if (feasibility != LBool.UNSAT) {
					// We found a feasible error trace
					return new McrTraceCheckResult<>(trace, feasibility, automatonBuilder.getResult(), null);
				}
				interpolants = proof.getSecond().getPredicates();
				if (trace == initialTrace) {
					initialInterpolants = interpolants.toArray(new IPredicate[interpolants.size()]);
				}
				final INestedWordAutomaton<LETTER, ?> mcrAutomaton = getMcrAutomaton(trace, interpolants);
				automatonBuilder.update(mcrAutomaton, trace, interpolants);
			}
			// queue.addAll(generateSeedInterleavings(trace, interpolants));
		}
		// All traces are infeasible
		return new McrTraceCheckResult<>(initialTrace, LBool.UNSAT, automatonBuilder.getResult(), initialInterpolants);
	}

	private void getReadsAndWrites(final List<LETTER> trace) {
		for (final LETTER action : trace) {
			final TermVariable tv =
					mManagedScript.constructFreshTermVariable("order", SmtSortUtils.getIntSort(mManagedScript));
			final String varName = ProgramVarUtils.generateConstantIdentifierForAuxVar(tv);
			final Term constant = SmtUtils.buildNewConstant(mManagedScript.getScript(), varName, "Int");
			if (mActions2TermVars.put(action, constant) != null) {
				// For now throw an exception for duplicate actions
				// TODO: Fix this using the indices instead
				throw new IllegalArgumentException("For now MCR cannot handle duplicate actions");
			}
			final TransFormula transformula = action.getTransformula();
			mReads2Variables.addAllPairs(action, transformula.getInVars().keySet());
			for (final IProgramVar var : transformula.getAssignedVars()) {
				mVariables2Writes.addPair(var, action);
				mWrites2Variables.addPair(action, var);
			}
		}
	}

	private void preprocess(final List<LETTER> trace) {
		mPreviousWrite.clear();
		mThreads2SortedActions.clear();
		mActions2Threads.clear();
		final Map<IProgramVar, LETTER> lastWrittenBy = new HashMap<>();
		for (int i = 0; i < trace.size(); i++) {
			final LETTER action = trace.get(i);
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

	// TODO: Avoid duplicates by caching?
	private Collection<List<LETTER>> generateSeedInterleavings(final List<LETTER> trace,
			final List<IPredicate> interpolants) {
		final Script script = mManagedScript.getScript();
		final List<List<LETTER>> result = new ArrayList<>();
		final Term[] termVars = mActions2TermVars.values().toArray(new Term[trace.size()]);
		for (final LETTER read : trace) {
			final Set<IProgramVar> readVars = mReads2Variables.getImage(read);
			if (readVars.isEmpty()) {
				continue;
			}
			for (final IProgramVar var : readVars) {
				final Map<IProgramVar, LETTER> previousWrites = mPreviousWrite.get(read);
				final Set<LETTER> writesWithNull =
						DataStructureUtils.union(mVariables2Writes.getImage(var), Collections.singleton(null));
				for (final LETTER write : writesWithNull) {
					if (mWriteRelation.areRelated(write, previousWrites.get(var), var, trace, interpolants)) {
						continue;
					}
					script.push(1);
					// If the constraints are satisfiable, add a trace based on them
					final Term constraints = getConstraints(trace, read, write, interpolants, var);
					script.assertTerm(constraints);
					if (script.checkSat() == LBool.SAT) {
						result.add(constructTraceFromModel(trace, script.getValue(termVars)));
					}
					script.pop(1);
				}
			}
		}
		return result;
	}

	/**
	 * Encode a new trace in a formula, that is equivalent to trace, except that write happens right before read.
	 */
	private Term getConstraints(final List<LETTER> trace, final LETTER read, final LETTER write,
			final List<IPredicate> interpolants, final IProgramVar var) {
		final Script script = mManagedScript.getScript();
		final List<Term> conjuncts = new ArrayList<>();
		// Add the MHB-constraints
		for (final List<LETTER> threadActions : mThreads2SortedActions.values()) {
			final Iterator<LETTER> iterator = threadActions.iterator();
			LETTER currentAction = iterator.next();
			while (iterator.hasNext()) {
				final LETTER nextAction = iterator.next();
				conjuncts.add(
						SmtUtils.less(script, mActions2TermVars.get(currentAction), mActions2TermVars.get(nextAction)));
				currentAction = nextAction;
			}
		}
		conjuncts.addAll(getRwConstraints(read, trace, interpolants));
		conjuncts.addAll(getRwConstraints(write, trace, interpolants));
		conjuncts.addAll(getValueConstraints(read, write, trace, interpolants));
		return SmtUtils.and(script, conjuncts);
	}

	private Collection<Term> getRwConstraints(final LETTER action, final List<LETTER> trace,
			final List<IPredicate> interpolants) {
		final List<Term> result = new ArrayList<>();
		for (final String thread : mActions2Threads.getImage(action)) {
			for (final LETTER otherAction : mThreads2SortedActions.get(thread)) {
				final Map<IProgramVar, LETTER> previousWrites = mPreviousWrite.get(otherAction);
				for (final IProgramVar var : mReads2Variables.getImage(otherAction)) {
					result.addAll(getValueConstraints(otherAction, previousWrites.get(var), trace, interpolants));
				}
				// We only need to constraint all actions up to action, so we are done here
				if (otherAction == action) {
					break;
				}
			}
		}
		return result;
	}

	private Collection<Term> getValueConstraints(final LETTER read, final LETTER writeToBeRead,
			final List<LETTER> trace, final List<IPredicate> interpolants) {
		final Script script = mManagedScript.getScript();
		final List<Term> result = new ArrayList<>();
		final Term readVar = mActions2TermVars.get(read);
		for (final IProgramVar var : mReads2Variables.getImage(read)) {
			final List<Term> disjuncts = new ArrayList<>();
			final Set<LETTER> writesWithNull =
					DataStructureUtils.union(mVariables2Writes.getImage(var), Collections.singleton(null));
			for (final LETTER write : writesWithNull) {
				if (!mWriteRelation.areRelated(write, writeToBeRead, var, trace, interpolants)) {
					continue;
				}
				final List<Term> conjuncts = new ArrayList<>();
				// TODO: This can lead to infinite recursion, catch this error and better cache the results
				conjuncts.addAll(getRwConstraints(write, trace, interpolants));
				Term writeVar = null;
				if (write != null) {
					writeVar = mActions2TermVars.get(write);
					conjuncts.add(SmtUtils.less(script, writeVar, readVar));
				}
				for (final LETTER otherWrite : mVariables2Writes.getImage(var)) {
					if (mWriteRelation.areRelated(otherWrite, writeToBeRead, var, trace, interpolants)) {
						continue;
					}
					final Term otherWriteVar = mActions2TermVars.get(otherWrite);
					final Term afterRead = SmtUtils.less(script, readVar, otherWriteVar);
					if (write != null) {
						final Term beforeWrite = SmtUtils.less(script, otherWriteVar, writeVar);
						conjuncts.add(SmtUtils.or(script, beforeWrite, afterRead));
					} else {
						conjuncts.add(afterRead);
					}
				}
				disjuncts.add(SmtUtils.and(script, conjuncts));
			}
			result.add(SmtUtils.or(mManagedScript.getScript(), disjuncts));
		}
		return result;
	}

	private List<LETTER> constructTraceFromModel(final List<LETTER> originalTrace, final Map<Term, Term> valueMap) {
		// TODO: For repeating actions sort IntStream.range(0, originalTrace.size()).boxed() instead
		return originalTrace.stream().sorted((a1, a2) -> getIntValue(valueMap, a1).compareTo(getIntValue(valueMap, a2)))
				.collect(Collectors.toList());
	}

	private BigInteger getIntValue(final Map<Term, Term> valueMap, final LETTER action) {
		final Term term = valueMap.get(mActions2TermVars.get(action));
		assert term instanceof ConstantTerm;
		final Object value = ((ConstantTerm) term).getValue();
		if (value instanceof BigInteger) {
			return (BigInteger) value;
		}
		assert value instanceof Rational;
		final Rational rational = (Rational) value;
		assert rational.denominator().equals(BigInteger.ONE);
		return rational.numerator();
	}

	private INestedWordAutomaton<LETTER, ?> getMcrAutomaton(final List<LETTER> trace,
			final List<IPredicate> interpolants) throws AutomataLibraryException {
		final List<INestedWordAutomaton<LETTER, String>> automata = new ArrayList<>();
		final StringFactory factory = new StringFactory();
		// Construct automata for the MHB relation
		for (final List<LETTER> threadActions : mThreads2SortedActions.values()) {
			final Set<LETTER> otherActions = new HashSet<>(trace);
			final NestedWordAutomaton<LETTER, String> nwa =
					new NestedWordAutomaton<>(mAutomataServices, mAlphabet, factory);
			otherActions.removeAll(threadActions);
			final List<String> states =
					IntStream.rangeClosed(0, threadActions.size()).mapToObj(x -> "q" + x).collect(Collectors.toList());
			final String initial = states.get(0);
			nwa.addState(true, false, initial);
			for (final LETTER otherAction : otherActions) {
				nwa.addInternalTransition(initial, otherAction, initial);
			}
			for (int i = 0; i < threadActions.size(); i++) {
				final String currentState = states.get(i);
				final String nextState = states.get(i + 1);
				nwa.addState(false, i + 1 == threadActions.size(), nextState);
				nwa.addInternalTransition(currentState, threadActions.get(i), nextState);
				for (final LETTER otherAction : otherActions) {
					nwa.addInternalTransition(nextState, otherAction, nextState);
				}
			}
			automata.add(nwa);
		}
		// Construct automata for each read to be preceded by the specific (or a "similar") write
		for (final LETTER read : trace) {
			final Map<IProgramVar, LETTER> previousWrites = mPreviousWrite.get(read);
			if (previousWrites == null) {
				continue;
			}
			for (final Entry<IProgramVar, LETTER> entry : previousWrites.entrySet()) {
				final LETTER write = entry.getValue();
				final IProgramVar var = entry.getKey();
				final NestedWordAutomaton<LETTER, String> nwa =
						new NestedWordAutomaton<>(mAutomataServices, mAlphabet, factory);
				final Set<LETTER> writesOnVar = mVariables2Writes.getImage(var);
				final String initial = "q0";
				final String postWrite = "q1";
				final String postRead = "q2";
				nwa.addState(true, false, initial);
				nwa.addState(false, true, postRead);
				if (write == null) {
					nwa.addInternalTransition(initial, read, postRead);
					for (final LETTER action : trace) {
						if (!writesOnVar.contains(action)) {
							nwa.addInternalTransition(initial, action, initial);
						}
						nwa.addInternalTransition(postRead, action, postRead);
					}
				} else {
					nwa.addState(false, false, postWrite);
					// Add q0 -w-> q1 for all related writes w
					writesOnVar.stream().filter(x -> mWriteRelation.areRelated(x, write, var, trace, interpolants))
							.forEach(x -> nwa.addInternalTransition(initial, x, postWrite));
					// Add q1 -r-> q2
					nwa.addInternalTransition(postWrite, read, postRead);
					// Add the self-loops
					for (final LETTER action : trace) {
						nwa.addInternalTransition(initial, action, initial);
						nwa.addInternalTransition(postRead, action, postRead);
						if (!writesOnVar.contains(action)) {
							nwa.addInternalTransition(postWrite, action, postWrite);
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
			return new NestedWordAutomaton<>(mAutomataServices, mAlphabet, stateFactory);
		}
		INestedWordAutomaton<LETTER, STATE> result = null;
		for (final INestedWordAutomaton<LETTER, STATE> a : automata) {
			if (result == null) {
				result = a;
			} else {
				final Intersect<LETTER, STATE> intersect = new Intersect<>(mAutomataServices, stateFactory, result, a);
				result = intersect.getResult();
			}
		}
		final INestedWordAutomaton<LETTER, STATE> simplified =
				new RemoveDeadEnds<>(mAutomataServices, result).getResult();
		mLogger.info(simplified);
		return simplified;
	}

	public NestedWordAutomaton<LETTER, IPredicate> getAutomaton() {
		return mResult.getAutomaton();
	}

	@Override
	public List<LETTER> getTrace() {
		return mResult.getTrace();
	}

	@Override
	public IPredicate[] getInterpolants() {
		return mResult.getInterpolants();
	}

	@Override
	public IPredicateUnifier getPredicateUnifier() {
		return mPredicateUnifier;
	}

	@Override
	public boolean isPerfectSequence() {
		// TODO: Adapt later; for now, automata are created by MCR so it does not really matter
		return false;
	}

	@Override
	public InterpolantComputationStatus getInterpolantComputationStatus() {
		// TODO: Only a workaround, use from RefinementEngine
		return new InterpolantComputationStatus();
	}

	@Override
	public LBool isCorrect() {
		return mResult.isCorrect();
	}

	@Override
	public IPredicate getPrecondition() {
		return mPredicateUnifier.getTruePredicate();
	}

	@Override
	public IPredicate getPostcondition() {
		return mPredicateUnifier.getFalsePredicate();
	}

	@Override
	public Map<Integer, IPredicate> getPendingContexts() {
		return Collections.emptyMap();
	}

	@Override
	public boolean providesRcfgProgramExecution() {
		return isCorrect() != LBool.SAT;
	}

	@Override
	public IProgramExecution<IIcfgTransition<IcfgLocation>, Term> getRcfgProgramExecution() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public TraceCheckReasonUnknown getTraceCheckReasonUnknown() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean wasTracecheckFinishedNormally() {
		// TODO Auto-generated method stub
		return true;
	}

	public interface IProofProvider<LETTER extends IIcfgTransition<?>> {
		Pair<LBool, QualifiedTracePredicates> getProof(List<LETTER> trace, IPredicate precondition,
				IPredicate postcondition);
	}

	public interface IWriteRelation<LETTER extends IIcfgTransition<?>> {
		/**
		 * Returns true iff write1 and write2 are related writes on var int the trace, given these interpolants. To be a
		 * useful relation, write1 must be at least as strong as writ2 on the given var.
		 */
		boolean areRelated(LETTER write1, LETTER write2, IProgramVar var, List<LETTER> trace,
				List<IPredicate> interpolants);
	}
}
