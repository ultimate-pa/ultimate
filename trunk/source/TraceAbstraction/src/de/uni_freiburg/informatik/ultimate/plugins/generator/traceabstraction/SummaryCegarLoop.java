package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Difference;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovabilityReason;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.SPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.TermDomainOperationProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.SubtaskIterationIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.AutomatonFreeRefinementEngine;
import de.uni_freiburg.informatik.ultimate.lib.proofs.floydhoare.NwaHoareProofProducer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.Counterexample;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.ProgramUtilities.AssureStatement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.ProgramUtilities.PrePostDummyTransition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine.ITARefinementStrategy;

/**
 * Summary Based Cegar Loop
 *
 * @param <L>
 */
public class SummaryCegarLoop<L extends IIcfgTransition<?>> extends NwaCegarLoop<L> {

	protected PredicateTransformer<Term, IPredicate, TransFormula> mPredicateTransformer;
	protected PredicateFactoryRefinement mPredicateFactoryRefinement;

	protected ProgramUtilities<L> mProgramUtilities;

	protected ContractMode mContractMode;
	protected Map<String, Collection<FunctionContract>> mContractCache;

	/**
	 * Constructs a new SummaryCegarLoop with the given contract mode.
	 *
	 * @see ContractMode
	 *
	 * @param name
	 * @param initialAbstraction
	 * @param rootNode
	 * @param csToolkit
	 * @param predicateFactory
	 * @param taPrefs
	 * @param errorLocs
	 * @param proofProducer
	 * @param services
	 * @param transitionClazz
	 * @param stateFactoryForRefinement
	 * @param contractMode
	 */
	public SummaryCegarLoop(final DebugIdentifier name, final INestedWordAutomaton<L, IPredicate> initialAbstraction,
			final IIcfg<?> rootNode, final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory,
			final TAPreferences taPrefs, final Set<? extends IcfgLocation> errorLocs,
			final NwaHoareProofProducer<L> proofProducer, final IUltimateServiceProvider services,
			final Class<L> transitionClazz, final PredicateFactoryRefinement stateFactoryForRefinement,
			final ContractMode contractMode) {
		super(name, initialAbstraction, rootNode, csToolkit, predicateFactory, taPrefs, errorLocs, proofProducer,
				services, transitionClazz, stateFactoryForRefinement);

		mContractMode = contractMode;

		mPredicateTransformer = new PredicateTransformer<>(mCsToolkit.getManagedScript(),
				new TermDomainOperationProvider(mServices, mCsToolkit.getManagedScript()));

		mPredicateFactoryRefinement = new PredicateFactoryRefinement(services, mCsToolkit.getManagedScript(),
				mPredicateFactory, true, new AnySet<>());

		mProgramUtilities = new ProgramUtilities<>(mIcfg, mServices, mPredicateFactory, mPredicateTransformer,
				mStateFactoryForRefinement, mErrorLocs, mCsToolkit, mPref);

		mContractCache = new HashMap<>();
		for (final String function : mProgramUtilities.getFunctionsWithImplementation()) {
			mContractCache.put(function, new ArrayList<>());
		}
	}

	/**
	 * Constructs a new SummaryCegarLoop with the global contract mode.
	 *
	 * @see ContractMode
	 *
	 * @param name
	 * @param initialAbstraction
	 * @param rootNode
	 * @param csToolkit
	 * @param predicateFactory
	 * @param taPrefs
	 * @param errorLocs
	 * @param proofProducer
	 * @param services
	 * @param transitionClazz
	 * @param stateFactoryForRefinement
	 */
	public SummaryCegarLoop(final DebugIdentifier name, final INestedWordAutomaton<L, IPredicate> initialAbstraction,
			final IIcfg<?> rootNode, final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory,
			final TAPreferences taPrefs, final Set<? extends IcfgLocation> errorLocs,
			final NwaHoareProofProducer<L> proofProducer, final IUltimateServiceProvider services,
			final Class<L> transitionClazz, final PredicateFactoryRefinement stateFactoryForRefinement) {
		this(name, initialAbstraction, rootNode, csToolkit, predicateFactory, taPrefs, errorLocs, proofProducer,
				services, transitionClazz, stateFactoryForRefinement, ContractMode.GLOBAL);
	}

	@Override
	public CegarLoopResult<L> runCegar() {
		Map<String, SafenessResult<L>> results;
		try {
			results = runSafenessChecks();
		} catch (final AutomataOperationCanceledException e) {
			throw new RuntimeException("Canceled");
		}

		mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.OverallTime.toString()); // TODO override finish?

		return buildCegarLoopResult(results);
	}

	/**
	 * Builds the {@link CegarLoopResult} object.
	 *
	 * @param results
	 *            the results of the analyzed functions from the cegar loops
	 * @return a {@link CegarLoopResult} object
	 */
	protected CegarLoopResult<L> buildCegarLoopResult(final Map<String, SafenessResult<L>> results) {
		final Map<IcfgLocation, CegarLoopLocalResult<L>> localResults = new HashMap<>();
		final Set<IcfgLocation> errorNodes = mIcfg.getProcedureErrorNodes().values().stream().flatMap(Set::stream)
				.collect(Collectors.toUnmodifiableSet());

		boolean allSafe = true;
		for (final SafenessResult<L> result : results.values()) {
			if (!result.isSafe()) {

				final IcfgLocation violatedErrorNode =
						((SPredicate) result.getNestedCounterexample().getStateSequence().getLast()).getProgramPoint();

				allSafe = false;
				for (final IcfgLocation errorNode : errorNodes) {
					if (errorNode.equals(violatedErrorNode)) {
						final IRun<L, ?> nestedCounterexample = result.getNestedCounterexample();
						final IRun<L, ?> nestedCounterexampleClean =
								removeDummyLocFromCounterexample(nestedCounterexample);

						final IRun<L, ?> nestedCounterexampleRelation =
								computeNestingRelation(nestedCounterexampleClean);

						final var locations = getControlConfigurationsFromCounterexample(nestedCounterexampleRelation);
						final var cEx = new Counterexample<>(nestedCounterexampleRelation.getWord(), locations);

						final ITARefinementStrategy<L> strategy = mStrategyFactory.constructStrategy(getServices(), cEx,
								mAbstraction, new SubtaskIterationIdentifier(mTaskIdentifier, getIteration()),
								mPredicateFactoryInterpolantAutomata, getPreconditionProvider(),
								getPostconditionProvider());

						final var programExecution = new AutomatonFreeRefinementEngine<>(mServices, mLogger, strategy)
								.getResult().getIcfgProgramExecution();

						localResults.put(errorNode,
								new CegarLoopLocalResult<>(Result.UNSAFE, programExecution, null, null));

					} else {
						final List<UnprovabilityReason> reasons = new ArrayList<>();
						reasons.add(new UnprovabilityReason("Not checked"));
						localResults.put(errorNode, new CegarLoopLocalResult<>(Result.UNKNOWN, null, reasons, null));
					}
				}
				break;
			}
		}

		if (allSafe) {
			for (final IcfgLocation errorNode : errorNodes) {
				localResults.put(errorNode, new CegarLoopLocalResult<>(Result.SAFE, null, null, null));
			}
		}

		return new CegarLoopResult<>(localResults, mCegarLoopBenchmark, mIcfg, null);
	}

	/**
	 * Removes the dummy location from the counterexample trace.
	 *
	 * @param counterexample
	 * @return cleaned counterexample
	 */
	protected IRun<L, ?> removeDummyLocFromCounterexample(final IRun<L, ?> counterexample) {
		if (counterexample.getWord().getSymbol(0) instanceof PrePostDummyTransition) {
			final List<L> letters = counterexample.getWord().asList().subList(1, counterexample.getWord().length());
			final List<?> states = counterexample.getStateSequence().subList(1, counterexample.getLength());

			final Word<L> word = new Word<>(letters.toArray(new IIcfgTransition[0]));
			final NestedWord<L> nestedWord = NestedWord.nestedWord(word);

			return new NestedRun<>(nestedWord, states);
		}

		return counterexample;
	}

	/**
	 * Builds a counterexample with valid nesting relation.
	 *
	 * @param counterexample
	 * @return counterexample with valid nesting relation
	 */
	protected IRun<L, ?> computeNestingRelation(final IRun<L, ?> counterexample) {
		final List<L> letters = counterexample.getWord().asList();
		final List<?> states = counterexample.getStateSequence();

		final int[] nestingRelation = new int[letters.size()];

		final Stack<Integer> callStack = new Stack<>();

		for (int i = 0; i < letters.size(); i++) {
			final L letter = letters.get(i);
			if (letter instanceof Call) {
				callStack.push(i);
			} else if (letter instanceof Return) {
				final int callIndex = callStack.pop();
				nestingRelation[callIndex] = i;
				nestingRelation[i] = callIndex;

			} else {
				nestingRelation[i] = NestedWord.INTERNAL_POSITION;
			}

		}

		while (!callStack.isEmpty()) {
			final int callIndex = callStack.pop();
			nestingRelation[callIndex] = NestedWord.PLUS_INFINITY;
		}

		@SuppressWarnings("unchecked")
		final L[] wordArray = (L[]) letters.toArray(new IIcfgTransition[0]);
		final NestedWord<L> nestedWord = new NestedWord<>(wordArray, nestingRelation);

		return new NestedRun<>(nestedWord, states);
	}

	/**
	 * Runs the safeness checks for all functions to be analyzed.
	 *
	 * @return map with function names and their results
	 * @throws AutomataOperationCanceledException
	 */
	protected Map<String, SafenessResult<L>> runSafenessChecks() throws AutomataOperationCanceledException {
		final Map<String, SafenessResult<L>> results = new HashMap<>();
		for (final String function : mProgramUtilities.getFunctionsToCheck()) {
			final SafenessResult<L> result = runSafenessCheck(function);
			results.put(function, result);
		}

		return results;
	}

	/**
	 * Runs a safeness check on the automaton of the given function.
	 *
	 * @param function
	 * @return
	 * @throws AutomataOperationCanceledException
	 */
	protected SafenessResult<L> runSafenessCheck(final String function) throws AutomataOperationCanceledException {

		final Set<Term> terms = new HashSet<>();
		for (final IProgramNonOldVar globalVar : mCsToolkit.getModifiableGlobalsTable()
				.getModifiedBoogieVars(function)) {
			final Term globalEqualsOld = mCsToolkit.getManagedScript().getScript().term("=",
					globalVar.getTermVariable(), globalVar.getOldVar().getTermVariable());

			terms.add(globalEqualsOld);
		}

		final Term preFormula = SmtUtils.and(mCsToolkit.getManagedScript().getScript(), terms);
		final IPredicate prePred = mPredicateFactory.newPredicate(preFormula);

		final Term postViolatedFormula = mCsToolkit.getManagedScript().getScript().term("false");
		final IPredicate postViolatedPred = mPredicateFactory.newPredicate(postViolatedFormula);

		if (!mProgramUtilities.functionHasImplementation(function)) {
			return new SafenessResult<>(true, 0, null, null, mProgramUtilities.newContractMap(), null, null, null);
		}

		final INestedWordAutomaton<L, IPredicate> abstraction =
				mProgramUtilities.initializeFunctionAbstraction(function, prePred, postViolatedPred);

		final SafenessResult<L> result = checkAutomatonSafeness(abstraction, mProgramUtilities.newContractMap());
		System.out.println(result);
		return result;

	}

	/**
	 * Checks the safeness of a function given by a summary and a given pre- and postcondition.
	 *
	 * @param summary
	 * @param contracts
	 * @param preconditionPredicate
	 * @param postconditionViolatedPredicate
	 * @return
	 * @throws AutomataOperationCanceledException
	 */
	public SafenessResult<L> checkSafeness(final Summary summary,
			final Map<Summary, Collection<FunctionContract>> contracts, final IPredicate preconditionPredicate,
			final IPredicate postconditionViolatedPredicate) throws AutomataOperationCanceledException {
		if (mContractMode == ContractMode.CACHE) {
			final FunctionContract cachedContract = getCachedContract(summary.getCallStatement().getMethodName(),
					preconditionPredicate, postconditionViolatedPredicate);
			if (cachedContract != null) {
				return new SafenessResult<>(true, 0, null, cachedContract, contracts, null, null, null);
			}
		}

		final String functionName = summary.getCallStatement().getMethodName();
		final INestedWordAutomaton<L, IPredicate> functionAbstraction = mProgramUtilities
				.initializeFunctionAbstraction(functionName, preconditionPredicate, postconditionViolatedPredicate);

		final SafenessResult<L> result = checkAutomatonSafeness(functionAbstraction, contracts);
		if (result.isSafe()) {
			mContractCache.get(summary.getCallStatement().getMethodName()).add(result.getFunctionContract());

			System.out.println("Computed contract for Summary: " + summary);
			System.out.println(result.getFunctionContract());
			System.out.println("---");
		}

		return result;

	}

	/**
	 * Returns a cached contract, if there exists one that fulfils the given pre- and postcondition, else
	 * <code>null</code>.
	 *
	 * @param functionName
	 * @param preconditionPredicate
	 * @param postconditionViolatedPredicate
	 * @return a {@link FunctionContract}, or <code>null</code>
	 */
	protected FunctionContract getCachedContract(final String functionName, final IPredicate preconditionPredicate,
			final IPredicate postconditionViolatedPredicate) {
		final Collection<FunctionContract> cachedContracts = mContractCache.get(functionName);
		if (cachedContracts == null || cachedContracts.isEmpty()) {
			return null;
		}

		final Script script = mCsToolkit.getManagedScript().getScript();
		final Term precondition = preconditionPredicate.getFormula();
		final Term postcondition = SmtUtils.not(script, postconditionViolatedPredicate.getFormula());

		for (final FunctionContract contract : mContractCache.get(functionName)) {
			final LBool preconditionImplication =
					SmtUtils.checkImplication(precondition, contract.getPrecondition().getFormula(), script);
			if (preconditionImplication != LBool.UNSAT) {
				continue;
			}

			final Term restrictedContractPostcondition =
					SmtUtils.and(script, preconditionPredicate.getFormula(), contract.getPostcondition().getFormula());

			final LBool postconditionImplication =
					SmtUtils.checkImplication(restrictedContractPostcondition, postcondition, script);

			if (postconditionImplication == LBool.UNSAT) {
				return contract;
			}
		}

		return null;
	}

	/**
	 * Checks if a function automaton is safe, meaning all accepted traces of the automaton are infeasible.
	 *
	 * @param abstraction
	 * @param contracts
	 * @return a {@link SafenessResult}
	 * @throws AutomataOperationCanceledException
	 */
	public SafenessResult<L> checkAutomatonSafeness(final INestedWordAutomaton<L, IPredicate> abstraction,
			final Map<Summary, Collection<FunctionContract>> contracts) throws AutomataOperationCanceledException {

		final Map<Summary, Collection<FunctionContract>> functionContracts = new HashMap<>(contracts);
		INestedWordAutomaton<L, IPredicate> currentAbstraction = abstraction;

		for (int i = 0; i < 10000000; i++) {
			final IsEmpty<L, ?> emptynessCheck =
					new IsEmpty<>(new AutomataLibraryServices(getServices()), currentAbstraction, mSearchStrategy);
			if (emptynessCheck.getResult()) {
				final FunctionContract contract = extractContract(currentAbstraction);
				return new SafenessResult<>(true, i + 1, currentAbstraction, contract, functionContracts, null, null,
						null);
			}

			final IRun<L, ?> counterexample = emptynessCheck.getNestedRun();

			final FeasibilityResult result = checkFeasibility(counterexample, functionContracts);
			functionContracts.putAll(result.getContracts());

			final var locations = getControlConfigurationsFromCounterexample(counterexample);
			final var cEx = new Counterexample<>(counterexample.getWord(), locations);

			final boolean feasable = result.isFeasable();
			if (feasable) {
				return new SafenessResult<>(false, i + 1, currentAbstraction, null, functionContracts,
						result.getViolatingPrecondition(), cEx, result.getNestedCounterexample());
			}

			final ITARefinementStrategy<L> strategy = mStrategyFactory.constructStrategy(getServices(), cEx,
					currentAbstraction, new SubtaskIterationIdentifier(mTaskIdentifier, getIteration()),
					mPredicateFactoryInterpolantAutomata, getPreconditionProvider(), getPostconditionProvider());

			final TraceAbstractionRefinementEngine<L> refinementEngine =
					new TraceAbstractionRefinementEngine<>(mServices, mLogger, strategy);
			mRefinementResult = refinementEngine.getResult();

			final NestedWordAutomaton<L, IPredicate> interpolantAutomata = mRefinementResult.getInfeasibilityProof();

			final var enhancedAutomaton = enhanceInterpolantAutomaton(mPref.interpolantAutomatonEnhancement(),
					mRefinementResult.getPredicateUnifier(), getHoareTripleChecker(), interpolantAutomata);

			IOpWithDelayedDeadEndRemoval<L, IPredicate> diff;
			try {
				final PowersetDeterminizer<L, IPredicate> psd =
						new PowersetDeterminizer<>(enhancedAutomaton, true, mPredicateFactoryInterpolantAutomata);

				diff = new Difference<>(new AutomataLibraryServices(getServices()), mPredicateFactoryRefinement,
						currentAbstraction, enhancedAutomaton, psd, true);

				currentAbstraction = diff.getResult();
			} catch (final AutomataLibraryException e) {
				e.printStackTrace();
			}

		}

		throw new RuntimeException("Max iterations reached");
	}

	/**
	 * Extracts a contract from the final abstraction.
	 *
	 * @param finalAbstraction
	 * @return a {@link FunctionContract}
	 */
	protected FunctionContract extractContract(final INestedWordAutomaton<L, IPredicate> finalAbstraction) {
		// TODO top level automaton needs different locations to extract

		final Set<Term> preconditionTerms = new HashSet<>();
		final Set<Term> postconditionTerms = new HashSet<>();

		final String functionName =
				((ISLPredicate) finalAbstraction.getInitialStates().iterator().next()).getProgramPoint().getProcedure();

		for (final IPredicate s : finalAbstraction.getStates()) {
			final ISLPredicate state = (ISLPredicate) s;
			final IcfgLocation entryNode = mIcfg.getProcedureEntryNodes().get(state.getProgramPoint().getProcedure());
			final IcfgLocation exitNode = mIcfg.getProcedureExitNodes().get(state.getProgramPoint().getProcedure());

			if (state.getProgramPoint().equals(entryNode)) {
				preconditionTerms.add(state.getFormula());
			}
			if (state.getProgramPoint().equals(exitNode)) {
				postconditionTerms.add(state.getFormula());
			}
		}

		final Term pre = SmtUtils.and(mCsToolkit.getManagedScript().getScript(), preconditionTerms);
		final Term post = SmtUtils.or(mCsToolkit.getManagedScript().getScript(), postconditionTerms);

		final List<TermVariable> modifiedGlobalVars = mCsToolkit.getModifiableGlobalsTable()
				.getModifiedBoogieVars(functionName).stream().map(IProgramNonOldVar::getTermVariable).toList();
		final List<TermVariable> modifiedGlobalOldVars = mCsToolkit.getModifiableGlobalsTable()
				.getModifiedBoogieVars(functionName).stream().map(pv -> pv.getOldVar().getTermVariable()).toList();

		final List<TermVariable> params = mCsToolkit.getInParams().get(functionName).stream()
				.map(ILocalProgramVar::getTermVariable).collect(Collectors.toCollection(ArrayList::new));
		params.addAll(modifiedGlobalVars);

		final List<TermVariable> returnParams = mCsToolkit.getOutParams().get(functionName).stream()
				.map(ILocalProgramVar::getTermVariable).collect(Collectors.toCollection(ArrayList::new));
		returnParams.addAll(modifiedGlobalVars);
		returnParams.addAll(modifiedGlobalOldVars);

		final Map<TermVariable, TermVariable> oldToGlobalVar = new HashMap<>();
		for (final IProgramNonOldVar globalProgramVar : mCsToolkit.getModifiableGlobalsTable()
				.getModifiedBoogieVars(functionName)) {

			oldToGlobalVar.put(globalProgramVar.getOldVar().getTermVariable(), globalProgramVar.getTermVariable());
		}

		Term preSub;
		if (!oldToGlobalVar.isEmpty()) {
			preSub = Substitution.apply(mCsToolkit.getManagedScript(), oldToGlobalVar, pre);
		} else {
			preSub = pre;
		}

		final List<TermVariable> toQuantifyPre =
				Arrays.stream(pre.getFreeVars()).filter(tv -> !params.contains(tv)).toList();
		final List<TermVariable> toQuantifyPost = Arrays.stream(post.getFreeVars())
				.filter(tv -> !params.contains(tv) && !returnParams.contains(tv)).toList();

		final Term preQuantified = SmtUtils.quantifier(mCsToolkit.getManagedScript().getScript(),
				QuantifiedFormula.EXISTS, toQuantifyPre, preSub);
		final Term postQuantified = SmtUtils.quantifier(mCsToolkit.getManagedScript().getScript(),
				QuantifiedFormula.EXISTS, toQuantifyPost, post);

		final IPredicate precondition = mPredicateFactory.newPredicate(preQuantified);
		final IPredicate postcondition = mPredicateFactory.newPredicate(postQuantified);

		return new FunctionContract(precondition, postcondition);
	}

	/**
	 * Checks if a trace that may contain function summaries is feasible.
	 *
	 * If required, new contracts for the functions of the summaries are computed.
	 *
	 * @param counterexample
	 * @param contracts
	 * @return a {@link FeasibilityResult}
	 * @throws AutomataOperationCanceledException
	 */
	public FeasibilityResult checkFeasibility(final IRun<L, ?> counterexample,
			final Map<Summary, Collection<FunctionContract>> contracts) throws AutomataOperationCanceledException {
		final Script script = mCsToolkit.getManagedScript().getScript();

		final Word<L> trace = counterexample.getWord();
		final int n = trace.length();

		Map<Summary, Collection<FunctionContract>> functionContracts;
		switch (mContractMode) {
		case GLOBAL:
		case LOCAL:
			functionContracts = new HashMap<>(contracts);
			break;
		case CACHE:
			functionContracts = mProgramUtilities.newContractMap();
			break;
		default:
			throw new AssertionError("Unknown contract mode");

		}
		applyContracts(functionContracts);

		final Map<Summary, IRun<L, ?>> summaryRuns = new HashMap<>();

		final List<SPredicate> interpolatedPredicates = initPredicates(counterexample);

		int k = 0;
		while (k < n) {
			L symbol = trace.getSymbol(k);
			final SPredicate preconditionPredicate = interpolatedPredicates.get(k);
			final SPredicate postconditionPredicate = interpolatedPredicates.get(k + 1);
			final Term sp = mPredicateTransformer.strongestPostcondition(interpolatedPredicates.get(k),
					symbol.getTransformula());
			final SPredicate spPredicate =
					mPredicateFactory.newSPredicate(postconditionPredicate.getProgramPoint(), sp);

			boolean strenghtenBackwards = false;

			if (symbol instanceof AssureStatement) {
				final AssureStatement assure = (AssureStatement) symbol;
				final IPredicate preconditionTransitionedPredicate =
						mProgramUtilities.transformPrecondition(assure.getSummary(), preconditionPredicate);

				final Term falseTerm = script.term("false");
				final IPredicate falsePredicate = mPredicateFactory.newPredicate(falseTerm);

				final SafenessResult<L> result = checkSafeness(assure.getSummary(), functionContracts,
						preconditionTransitionedPredicate, falsePredicate);
				functionContracts = assignContractMap(functionContracts, result.getContracts());
				if (result.isSafe()) {
					final FunctionContract assureContract = result.getFunctionContract();
					functionContracts = assignContract(functionContracts, assure.getSummary(), assureContract);
					applyContracts(functionContracts);

					return new FeasibilityResult(false, functionContracts, script.term("false"),
							interpolatedPredicates);
				}

				summaryRuns.put(assure.getSummary(), result.getNestedCounterexample());

				applyContracts(functionContracts);

				final Term counterexampleState = result.getViolatingPrecondition();
				final Term negatedCounterexample = SmtUtils.not(script, counterexampleState);
				final BasicPredicate negatedCounterexamplePredicate =
						mPredicateFactory.newPredicate(negatedCounterexample);

				final Term negatedCounterexampleTransitioned =
						mProgramUtilities.callTransitionReverse(assure.getSummary(), negatedCounterexamplePredicate);

				final Term andTerm =
						SmtUtils.and(script, preconditionPredicate.getFormula(), negatedCounterexampleTransitioned);

				final SPredicate andPredicate =
						mPredicateFactory.newSPredicate(preconditionPredicate.getProgramPoint(), andTerm);
				interpolatedPredicates.set(k, andPredicate);

				strenghtenBackwards = true;
				k--;

			} else if (k + 1 == n) {
				final LBool isSat = SmtUtils.checkSatTerm(script, sp);
				switch (isSat) {
				case SAT:
					strenghtenBackwards = true;
					break;
				case UNSAT:
					return new FeasibilityResult(false, functionContracts, script.term("false"),
							interpolatedPredicates);
				default:
				case UNKNOWN:
					throw new RuntimeException("unknown sat");

				}
			} else if (symbol instanceof Summary && ((Summary) symbol).calledProcedureHasImplementation()) {
				final Summary summarySymbol = (Summary) symbol;

				final LBool implicationHolds =
						SmtUtils.checkImplication(sp, postconditionPredicate.getFormula(), script);
				switch (implicationHolds) {
				case SAT: // implication holds not
					final IPredicate preconditionTransitionedPredicate =
							mProgramUtilities.transformPrecondition(summarySymbol, preconditionPredicate);

					final List<TermVariable> returnParams = mProgramUtilities.getReturnParams(summarySymbol).stream()
							.map(IProgramVar::getTermVariable).toList();

					final Term quantifiedPostcondition = SmtUtils.quantifier(script, QuantifiedFormula.EXISTS,
							returnParams, postconditionPredicate.getFormula());

					final LBool contractedImplicationHolds =
							SmtUtils.checkImplication(sp, quantifiedPostcondition, script);

					switch (contractedImplicationHolds) {
					case UNSAT: // holds
						final IPredicate postconditionTransitionedPredicate = mProgramUtilities
								.transformPostcondition(summarySymbol, postconditionPredicate, preconditionPredicate);

						final IPredicate postconditionViolatedTransitionedPredicate =
								mPredicateFactory.not(postconditionTransitionedPredicate);

						final SafenessResult<L> result = checkSafeness(summarySymbol, functionContracts,
								preconditionTransitionedPredicate, postconditionViolatedTransitionedPredicate);

						functionContracts = assignContractMap(functionContracts, result.getContracts());
						if (result.isSafe()) {
							final FunctionContract contract = result.getFunctionContract();
							functionContracts = assignContract(functionContracts, summarySymbol, contract);
							applyContracts(functionContracts);
						} else {
							summaryRuns.put(summarySymbol, result.getNestedCounterexample());

							applyContracts(functionContracts);
							final Term counterexampleState = result.getViolatingPrecondition();
							final BasicPredicate counterexamplePredicate =
									mPredicateFactory.newPredicate(counterexampleState);

							final Term counterexampleTransitioned =
									mProgramUtilities.callTransitionReverse(summarySymbol, counterexamplePredicate);

							final Term negatedCounterexample = SmtUtils.not(script, counterexampleTransitioned);

							final Term andTerm =
									SmtUtils.and(script, preconditionPredicate.getFormula(), negatedCounterexample);

							final SPredicate andPredicate =
									mPredicateFactory.newSPredicate(preconditionPredicate.getProgramPoint(), andTerm);
							interpolatedPredicates.set(k, andPredicate);

							strenghtenBackwards = true;
							k--;
						}
						break;
					case SAT: // holds not
						final Term trueTerm = script.term("true");
						final IPredicate truePredicate = mPredicateFactory.newPredicate(trueTerm);

						final Term quantifiedPostconditionNegated = SmtUtils.not(script, quantifiedPostcondition);

						final Term endCheckPrecondition = SmtUtils.and(script, preconditionPredicate.getFormula(),
								quantifiedPostconditionNegated);
						final IPredicate endCheckPreconditionPredicate =
								mPredicateFactory.newPredicate(endCheckPrecondition);

						final IPredicate endCheckPreconditionTransitionedPredicate =
								mProgramUtilities.transformPrecondition(summarySymbol, endCheckPreconditionPredicate);

						final SafenessResult<L> reachableEndCheckResult = checkSafeness(summarySymbol,
								functionContracts, endCheckPreconditionTransitionedPredicate, truePredicate);

						functionContracts =
								assignContractMap(functionContracts, reachableEndCheckResult.getContracts());
						if (reachableEndCheckResult.isSafe()) {
							final FunctionContract contract = reachableEndCheckResult.getFunctionContract();
							functionContracts = assignContract(functionContracts, summarySymbol, contract);
							applyContracts(functionContracts);

							continue;
						}
						summaryRuns.put(summarySymbol, reachableEndCheckResult.getNestedCounterexample());

						applyContracts(functionContracts);

						final Term counterexampleState = reachableEndCheckResult.getViolatingPrecondition();

						final BasicPredicate counterexamplePredicate =
								mPredicateFactory.newPredicate(counterexampleState);

						final Term counterexampleTransitioned =
								mProgramUtilities.callTransitionReverse(summarySymbol, counterexamplePredicate);

						final Term implication =
								SmtUtils.implies(script, counterexampleTransitioned, quantifiedPostcondition);

						final Term andTerm = SmtUtils.and(script, preconditionPredicate.getFormula(), implication);

						final SPredicate andPredicate =
								mPredicateFactory.newSPredicate(preconditionPredicate.getProgramPoint(), andTerm);
						interpolatedPredicates.set(k, andPredicate);

						strenghtenBackwards = true;
						k--;

						break;
					default:
					case UNKNOWN:
						throw new RuntimeException("unknown sat");
					}
					break;
				case UNSAT: // implication holds
					interpolatedPredicates.set(k + 1, spPredicate);
					k++;
					continue;
				default:
				case UNKNOWN:
					throw new RuntimeException("unknown sat");

				}

			} else if (k + 1 != n) {
				interpolatedPredicates.set(k + 1, spPredicate);
				k++;
				continue;
			}

			if (strenghtenBackwards) {
				while (k >= 0) {
					symbol = trace.getSymbol(k);
					if (symbol instanceof Summary && ((Summary) symbol).calledProcedureHasImplementation()) {
						break;
					}
					final Term wp = mPredicateTransformer.weakestPrecondition(interpolatedPredicates.get(k + 1),
							symbol.getTransformula());
					final Term andTerm = SmtUtils.and(script, wp, interpolatedPredicates.get(k).getFormula());

					interpolatedPredicates.set(k,
							mPredicateFactory.newSPredicate(interpolatedPredicates.get(k).getProgramPoint(), andTerm));

					k--;
				}

				if (k < 0) {
					final Term notTerm = SmtUtils.not(script, interpolatedPredicates.get(0).getFormula());
					final IRun<L, ?> nestedCounterexample = extractNestedRun(counterexample, summaryRuns);
					return new FeasibilityResult(true, contracts, notTerm, interpolatedPredicates,
							nestedCounterexample);
				}

			}

		}

		throw new RuntimeException("Should not happen");
	}

	/**
	 * Inits the predicates of the trace. All predicates will be initialized to <code>true</code>, except the final one,
	 * which will be initialized to <code>false</code>.
	 *
	 * @param counterexample
	 * @return a {@link List} containing elements of type {@link SPredicate}
	 */
	protected List<SPredicate> initPredicates(final IRun<L, ?> counterexample) {
		final List<SPredicate> predicates = new ArrayList<>();

		final Script script = mCsToolkit.getManagedScript().getScript();

		final List<?> stateSequence = counterexample.getStateSequence();

		final Term termTrue = script.term("true");
		for (int i = 0; i < counterexample.getLength() - 1; i++) {
			final IcfgLocation location = ((ISLPredicate) stateSequence.get(i)).getProgramPoint();
			final SPredicate predicateTrue = mPredicateFactory.newSPredicate(location, termTrue);
			predicates.add(predicateTrue);
		}

		final Term termFalse = script.term("false");
		final SPredicate predicateFalse =
				mPredicateFactory.newSPredicate(((ISLPredicate) stateSequence.getLast()).getProgramPoint(), termFalse);
		predicates.add(predicateFalse);

		return predicates;
	}

	/**
	 * Extracts a nested run, meaning the summary statements are replaced by actual traces through the function.
	 *
	 * @param counterexample
	 * @param summaryRuns
	 * @return an {@link IRun} object
	 */
	@SuppressWarnings("unchecked")
	protected IRun<L, ?> extractNestedRun(final IRun<L, ?> counterexample, final Map<Summary, IRun<L, ?>> summaryRuns) {
		final List<L> letters = new ArrayList<>();
		final List<Object> states = new ArrayList<>();

		Outer: for (int i = 0; i < counterexample.getWord().length(); i++) {
			final Object state = counterexample.getStateSequence().get(i);
			states.add(state);

			final L st = counterexample.getSymbol(i);
			if (st instanceof Summary || st instanceof AssureStatement) {
				if (st instanceof Summary && !((Summary) st).calledProcedureHasImplementation()) {
					letters.add(st);
				}

				final Summary summary = st instanceof Summary ? (Summary) st : ((AssureStatement) st).getSummary();
				final IRun<L, ?> summaryRun = summaryRuns.get(summary);

				for (int j = 0; j < summaryRun.getWord().length(); j++) {
					final L nestedSt = summaryRun.getSymbol(j);
					if (j == 0 && nestedSt instanceof PrePostDummyTransition) {

						final Call call = mProgramUtilities.getCallSummariesInverse().get(summary);
						letters.add((L) call);
						continue;
					}
					final Object nestedState = summaryRun.getStateSequence().get(j);
					states.add(nestedState);

					if (j == summaryRun.getWord().length() - 1) {
						if (!(nestedSt instanceof PrePostDummyTransition)) {
							states.add(summaryRun.getStateSequence().get(j + 1));
							letters.add(nestedSt);
							break Outer;

						}
						final Return ret = mProgramUtilities.getReturnSummariesInverse().get(summary);
						letters.add((L) ret);
						break;
					}

					letters.add(nestedSt);
				}

			} else {
				letters.add(st);
			}

			if (i == counterexample.getWord().length() - 1) {
				states.add(counterexample.getStateSequence().get(i + 1));
			}
		}

		final Word<L> word = new Word<>(letters.toArray(new IIcfgTransition[0]));
		final NestedWord<L> nestedWord = NestedWord.nestedWord(word);

		return new NestedRun<>(nestedWord, states);
	}

	/**
	 * Assigns a contact to a contract map.
	 *
	 * @param oldContracts
	 * @param summary
	 * @param contract
	 * @return a new contract map including the given contract and the original entries
	 */
	protected Map<Summary, Collection<FunctionContract>> assignContract(
			final Map<Summary, Collection<FunctionContract>> oldContracts, final Summary summary,
			final FunctionContract contract) {

		final Map<Summary, Collection<FunctionContract>> newMap = new HashMap<>();
		for (final var entry : oldContracts.entrySet()) {
			final Summary entrySummary = entry.getKey();
			final Collection<FunctionContract> old = entry.getValue();
			final Collection<FunctionContract> newContracts = new HashSet<>(old);
			switch (mContractMode) {
			case GLOBAL:
				if (summary.getCallStatement().getMethodName()
						.equals(entrySummary.getCallStatement().getMethodName())) {
					newContracts.add(contract);
				}
				break;
			case LOCAL:
			case CACHE:
				if (summary.equals(entrySummary)) {
					newContracts.add(contract);
				}
				break;
			default:
				throw new AssertionError("Unknown contract mode");

			}

			newMap.put(entrySummary, newContracts);
		}

		return newMap;

	}

	/**
	 * Assigns a contract map to another contract map.
	 *
	 * @param oldContracts
	 * @param contracts
	 * @return a new contract map including the contracts from the given contract map and the original entries
	 */
	protected static Map<Summary, Collection<FunctionContract>> assignContractMap(
			final Map<Summary, Collection<FunctionContract>> oldContracts,
			final Map<Summary, Collection<FunctionContract>> contracts) {

		final Map<Summary, Collection<FunctionContract>> newMap = new HashMap<>();
		for (final var entry : oldContracts.entrySet()) {
			final Summary summary = entry.getKey();
			final Collection<FunctionContract> old = entry.getValue();

			final Collection<FunctionContract> newContracts = new HashSet<>(old);
			newContracts.addAll(contracts.get(summary));

			newMap.put(summary, newContracts);
		}

		return newMap;

	}

	/**
	 * Applies the given contract map to the corresponding summary statements by building respective trans formulas.
	 *
	 * @param contracts
	 */
	protected void applyContracts(final Map<Summary, Collection<FunctionContract>> contracts) {
		for (final var entry : contracts.entrySet()) {
			final Summary summary = entry.getKey();
			final Collection<FunctionContract> entryContracts = entry.getValue();

			final UnmodifiableTransFormula summaryTransFormula =
					FunctionContract.buildTransFormulaForContracts(summary, entryContracts, mProgramUtilities);
			summary.setTransitionFormula(summaryTransFormula);

			final AssureStatement assure = mProgramUtilities.getAssureStatement(summary);
			if (assure != null) {
				final UnmodifiableTransFormula assureTransFormula =
						FunctionContract.buildAssureTransFormula(summary, entryContracts, mProgramUtilities);
				assure.setTransformula(assureTransFormula);
			}
		}
	}

	/**
	 * The result of an automaton safeness check.
	 *
	 * @param <L>
	 */
	public static class SafenessResult<L> {
		final boolean mIsSafe;
		final int mRequiredIterations;
		final INestedWordAutomaton<L, IPredicate> mFunctionAbstraction;
		final FunctionContract mFunctionContract;
		final Map<Summary, Collection<FunctionContract>> mContracts;
		final Term mViolatingPrecondition;
		final Counterexample<L> mCounterexampleTrace;
		final IRun<L, ?> mNestedCounterexample;

		public SafenessResult(final boolean isSafe, final int requiredIterations,
				final INestedWordAutomaton<L, IPredicate> abstraction, final FunctionContract functionContract,
				final Map<Summary, Collection<FunctionContract>> contracts, final Term violatingPrecondition,
				final Counterexample<L> counterexampleTrace, final IRun<L, ?> nestedCounterexample) {
			mIsSafe = isSafe;
			mRequiredIterations = requiredIterations;
			mFunctionAbstraction = abstraction;
			mFunctionContract = functionContract;
			mContracts = contracts;
			mViolatingPrecondition = violatingPrecondition;
			mCounterexampleTrace = counterexampleTrace;
			mNestedCounterexample = nestedCounterexample;
		}

		public IRun<L, ?> getNestedCounterexample() {
			return mNestedCounterexample;
		}

		public boolean isSafe() {
			return mIsSafe;
		}

		public int getRequiredIterations() {
			return mRequiredIterations;
		}

		public INestedWordAutomaton<L, IPredicate> getAbstraction() {
			return mFunctionAbstraction;
		}

		public FunctionContract getFunctionContract() {
			return mFunctionContract;
		}

		public Map<Summary, Collection<FunctionContract>> getContracts() {
			return mContracts;
		}

		public Term getViolatingPrecondition() {
			return mViolatingPrecondition;
		}

		public Counterexample<L> getCounterexampleTrace() {
			return mCounterexampleTrace;
		}

		@Override
		public String toString() {
			return "CorrectnessResult [mIsCorrect=" + mIsSafe + ", mFunctionContract=" + mFunctionContract
					+ ", mCounterexampleState=" + mViolatingPrecondition + "]";
		}
	}

	/**
	 * The result of a feasibility check.
	 */
	public class FeasibilityResult {
		final boolean mIsFeasible;
		final Map<Summary, Collection<FunctionContract>> mContracts;
		final Term mViolatingPrecondition;
		final List<SPredicate> mPredicates;
		final IRun<L, ?> mNestedCounterexample;

		public FeasibilityResult(final boolean isFeasible, final Map<Summary, Collection<FunctionContract>> contracts,
				final Term violatingPrecondition, final List<SPredicate> interpolatedPredicates) {
			mIsFeasible = isFeasible;
			mContracts = contracts;
			mViolatingPrecondition = violatingPrecondition;
			mPredicates = interpolatedPredicates;
			mNestedCounterexample = null;
		}

		public FeasibilityResult(final boolean isFeasible, final Map<Summary, Collection<FunctionContract>> contracts,
				final Term violatingPrecondition, final List<SPredicate> interpolatedPredicates,
				final IRun<L, ?> nestedCounterexample) {
			mIsFeasible = isFeasible;
			mContracts = contracts;
			mViolatingPrecondition = violatingPrecondition;
			mPredicates = interpolatedPredicates;
			mNestedCounterexample = nestedCounterexample;
		}

		public Map<Summary, Collection<FunctionContract>> getContracts() {
			return mContracts;
		}

		public boolean isFeasable() {
			return mIsFeasible;
		}

		public Term getViolatingPrecondition() {
			return mViolatingPrecondition;
		}

		public List<SPredicate> getPredicates() {
			return mPredicates;
		}

		public IRun<L, ?> getNestedCounterexample() {
			return mNestedCounterexample;
		}

		@Override
		public String toString() {
			return "FeasabilityResult [mIsFeasable=" + mIsFeasible + ", mCounterexampleState=" + mViolatingPrecondition
					+ ", mPredicates=" + mPredicates + "]";
		}
	}

	/**
	 * The contract mode of the Summary Cegar Loop. Contract mode global means that function contracts are assigned to
	 * all summaries of the corresponding function. Local means that contracts are only applies to the summaries they
	 * were computed for. Cache means that contracts are reset at the start of each feasibility check, but a cache of
	 * computed contracts is maintained and checked before a new contract is computed.
	 *
	 */
	public enum ContractMode {
		GLOBAL, LOCAL, CACHE
	}

	public static class AnySet<L> extends HashSet<L> {

		private static final long serialVersionUID = -2475140788612700623L;

		@Override
		public boolean contains(final Object o) {
			return true;
		}

	}

}
