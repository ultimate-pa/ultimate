package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Difference;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovabilityReason;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.core.model.models.Payload;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
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
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.Counterexample;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine.ITARefinementStrategy;

public class SummaryCegarLoop<L extends IIcfgTransition<?>> extends NwaCegarLoop<L> {

	// protected BasicPredicateFactory mBasicPredicateFactory;
	protected PredicateTransformer<Term, IPredicate, TransFormula> mPredicateTransformer;
	protected PredicateFactoryRefinement mPredicateFactoryRefinement;

	protected ProgramExtractor<L> mProgramExtractor;

	public SummaryCegarLoop(final DebugIdentifier name, final INestedWordAutomaton<L, IPredicate> initialAbstraction,
			final IIcfg<?> rootNode, final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory,
			final TAPreferences taPrefs, final Set<? extends IcfgLocation> errorLocs,
			final NwaHoareProofProducer<L> proofProducer, final IUltimateServiceProvider services,
			final Class<L> transitionClazz, final PredicateFactoryRefinement stateFactoryForRefinement) {
		super(name, initialAbstraction, rootNode, csToolkit, predicateFactory, taPrefs, errorLocs, proofProducer,
				services, transitionClazz, stateFactoryForRefinement);

		mPredicateTransformer = new PredicateTransformer<>(mCsToolkit.getManagedScript(),
				new TermDomainOperationProvider(mServices, mCsToolkit.getManagedScript()));

		mPredicateFactoryRefinement = new PredicateFactoryRefinement(services, mCsToolkit.getManagedScript(),
				mPredicateFactory, true, new AnySet<>());

		mProgramExtractor = new ProgramExtractor<>(mIcfg, mServices, mPredicateFactory, mPredicateTransformer,
				mStateFactoryForRefinement, mErrorLocs, mCsToolkit, mPref);
	}

	@Override
	public CegarLoopResult<L> runCegar() {
		final Map<IcfgLocation, CegarLoopLocalResult<L>> localResults = new HashMap<>();
		final Set<IcfgLocation> errorNodes = mIcfg.getProcedureErrorNodes().values().stream().flatMap(Set::stream)
				.collect(Collectors.toUnmodifiableSet());

		try {
			boolean allSafe = true;
			final Map<String, CorrectnessResult<L>> results = runCorrectnessChecks();
			for (final CorrectnessResult<L> result : results.values()) {
				if (!result.isCorrect()) {
					// final Term state = result.getCounterexampleState();
					// SmtUtils.checkSatTerm(mCsToolkit.getManagedScript().getScript(), state);
					//
					// final List<Term> list = new ArrayList<>();
					// list.add(state);
					// final var r = SmtUtils.getValues(mCsToolkit.getManagedScript().getScript(), list);
					// System.out.println(r);

					allSafe = false;
					for (final IcfgLocation errorNode : errorNodes) {
						// @SuppressWarnings("unchecked")
						// final IProgramExecution<L, Term> programExecution =
						// new IcfgProgramExecution<>(new ArrayList<>(), new HashMap<>(), new Map[0], false, null);
						if (errorNode == result.getCounterexampleTrace().getControlConfigurations().getLast()) {

							final ITARefinementStrategy<L> strategy = mStrategyFactory.constructStrategy(getServices(),
									result.getCounterexampleTrace(), result.getAbstraction(),
									new SubtaskIterationIdentifier(mTaskIdentifier, getIteration()),
									mPredicateFactoryInterpolantAutomata, getPreconditionProvider(),
									getPostconditionProvider());

							final var programExecution =
									new AutomatonFreeRefinementEngine<>(mServices, mLogger, strategy).getResult()
											.getIcfgProgramExecution();
							// localResults.put(errorNode,
							// new CegarLoopLocalResult<>(Result.UNSAFE, programExecution, null, null));

							final List<UnprovabilityReason> reasons = new ArrayList<>();
							reasons.add(new UnprovabilityReason(
									"Actually unsafe but program execution needs to be build correctly"));
							localResults.put(errorNode,
									new CegarLoopLocalResult<>(Result.UNSAFE, programExecution, reasons, null));

						} else {
							final List<UnprovabilityReason> reasons = new ArrayList<>();
							reasons.add(new UnprovabilityReason("Not checked"));
							localResults.put(errorNode,
									new CegarLoopLocalResult<>(Result.UNKNOWN, null, reasons, null));
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
		} catch (final AutomataOperationCanceledException e) {
			e.printStackTrace();
			// TODO
		}

		if (mStrategyFactory != null && mStrategyFactory.getPathProgramCache() != null) {
			final List<Integer> sortedHistogram = mStrategyFactory.getPathProgramCache().computeSortedHistrogram();
			System.out.println(sortedHistogram);
		}

		mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.OverallTime.toString()); // TODO override finish?

		return new CegarLoopResult<>(localResults, mCegarLoopBenchmark, mIcfg, null);
	}

	protected void strenghtenFunctionContract(final String functionName, final IPredicate precondition,
			final IPredicate postcondition) {
		for (final Summary summary : mProgramExtractor.getFunctionSummaries(functionName)) {
			final Term implication = SmtUtils.implies(mCsToolkit.getManagedScript().getScript(),
					precondition.getFormula(), postcondition.getFormula());
			// final Term contract = SmtUtils.and(mCsToolkit.getManagedScript().getScript(),
			// summary.getTransformula().getFormula(), implication);

			final IPredicate predicate = mPredicateFactory.newPredicate(implication);
			final UnmodifiableTransFormula transFormula = buildContractTransFormula(summary, predicate);
			final UnmodifiableTransFormula mergedTransFormula =
					mergeTransFormulas(summary.getTransformula(), transFormula);

			summary.setTransitionFormula(mergedTransFormula);
		}
	}

	protected UnmodifiableTransFormula buildContractTransFormula(final Summary summary, final IPredicate contract) { // TODO
																														// another
																														// quantifier
																														// for
																														// implication
																														// needed?
		final Map<IProgramVar, TermVariable> inVars = new HashMap<>();
		final Map<IProgramVar, TermVariable> outVars = new HashMap<>();
		final Set<TermVariable> auxVars = new HashSet<>();

		final Map<IProgramVar, IProgramVar> callVarsMapping = mProgramExtractor.getCallVarMapping(summary.getSource());
		final Map<IProgramVar, IProgramVar> returnVarsMapping =
				mProgramExtractor.getReturnVarMapping(summary.getTarget());

		for (final IProgramVar var : contract.getVars()) {
			final TermVariable termVariable = var.getTermVariable();
			final IProgramVar mappedCallVar = callVarsMapping.get(var);
			final IProgramVar mappedReturnVar = returnVarsMapping.get(var);

			if (mappedReturnVar != null) {
				outVars.put(mappedReturnVar, termVariable);
			}
			if (mappedCallVar != null) {
				inVars.put(mappedCallVar, termVariable);
				outVars.putIfAbsent(mappedCallVar, termVariable);
			}
			if (mappedReturnVar == null && mappedCallVar == null) {
				auxVars.add(termVariable);
			}
		}

		final TransFormulaBuilder builder =
				new TransFormulaBuilder(inVars, outVars, true, null, true, null, auxVars.isEmpty());

		final Term quantifiedFormula = SmtUtils.quantifier(mCsToolkit.getManagedScript().getScript(),
				QuantifiedFormula.FORALL, auxVars, contract.getFormula());

		builder.setFormula(quantifiedFormula);

		if (!auxVars.isEmpty()) {
			// builder.addAuxVarsButRenameToFreshCopies(auxVars, mCsToolkit.getManagedScript());
		}

		builder.setInfeasibility(Infeasibility.UNPROVEABLE);

		return builder.finishConstruction(mCsToolkit.getManagedScript());
	}

	protected UnmodifiableTransFormula mergeTransFormulas(final UnmodifiableTransFormula transFormula1,
			final UnmodifiableTransFormula transFormula2) {
		final Map<IProgramVar, TermVariable> inVars = new HashMap<>();
		final Map<IProgramVar, TermVariable> outVars = new HashMap<>();
		final Set<TermVariable> auxVars = new HashSet<>();

		inVars.putAll(transFormula1.getInVars());
		inVars.putAll(transFormula2.getInVars());

		outVars.putAll(transFormula1.getOutVars());
		outVars.putAll(transFormula2.getOutVars());

		auxVars.addAll(transFormula1.getAuxVars());
		auxVars.addAll(transFormula2.getAuxVars());

		final TransFormulaBuilder builder =
				new TransFormulaBuilder(inVars, outVars, true, null, true, null, auxVars.isEmpty());

		final Term formula1 = transFormula1.getFormula();
		final Term formula2 = transFormula2.getFormula();
		final Term andFormula = SmtUtils.and(mCsToolkit.getManagedScript().getScript(), formula1, formula2);
		builder.setFormula(andFormula);

		if (!auxVars.isEmpty()) {
			builder.addAuxVarsButRenameToFreshCopies(auxVars, mCsToolkit.getManagedScript());
		}

		builder.setInfeasibility(Infeasibility.UNPROVEABLE);

		return builder.finishConstruction(mCsToolkit.getManagedScript());
	}

	protected Map<String, CorrectnessResult<L>> runCorrectnessChecks() throws AutomataOperationCanceledException {
		final Map<String, CorrectnessResult<L>> results = new HashMap<>();
		for (final String function : mProgramExtractor.getFunctionNames()) {
			final CorrectnessResult<L> result = runCorrectnessCheck(function);
			results.put(function, result);
		}

		return results;
	}

	// @SuppressWarnings("unchecked")
	protected CorrectnessResult<L> runCorrectnessCheck(final String function)
			throws AutomataOperationCanceledException { // TODO
		// rewrite
		// final L preconditionTransition;
		//
		// final UnmodifiableTransFormula preconditionTransFormula = mPreconditionTransFormulas.get(function);
		//
		// if (preconditionTransFormula != null) {
		// preconditionTransition = (L) new PrePostDummyTransition(function, preconditionTransFormula,
		// String.valueOf(preconditionTransFormula.getFormula()));
		// } else {
		// preconditionTransition = null;
		// }
		//
		// final L postconditionViolatedTransition;
		//
		// final UnmodifiableTransFormula postconditionViolatedTransFormula =
		// mPostconditionViolatedTransFormulas.get(function);
		//
		// if (postconditionViolatedTransFormula != null) {
		// postconditionViolatedTransition = (L) new PrePostDummyTransition(function,
		// postconditionViolatedTransFormula, String.valueOf(postconditionViolatedTransFormula.getFormula()));
		// } else {
		// postconditionViolatedTransition = null;
		// }

		final INestedWordAutomaton<L, IPredicate> abstraction = mProgramExtractor.initializeRawAbstraction(function);

		final TermVariable virtualErrorVariable = mCsToolkit.getManagedScript().getScript().variable("vError",
				SmtSortUtils.getBoolSort(mCsToolkit.getManagedScript()));

		final Term notTerm = mCsToolkit.getManagedScript().getScript().term("not", virtualErrorVariable);

		// mPredicateFactory.newPredicate(notTerm);

		final CorrectnessResult<L> result = checkCorrectness(abstraction);
		System.out.println(result);
		return result;

	}

	public CorrectnessResult<L> checkCorrectness(final INestedWordAutomaton<L, IPredicate> abstraction)
			throws AutomataOperationCanceledException {

		INestedWordAutomaton<L, IPredicate> currentAbstraction = abstraction;

		for (int i = 0; i < 10000000; i++) { // TODO max iterations
			final IsEmpty<L, ?> emptynessCheck =
					new IsEmpty<>(new AutomataLibraryServices(getServices()), currentAbstraction, mSearchStrategy);
			if (emptynessCheck.getResult()) {
				return new CorrectnessResult<>(true, currentAbstraction, null, null);
			}

			final IRun<L, ?> counterexample = emptynessCheck.getNestedRun();

			final FeasabilityResult result = checkFeasability(counterexample);

			final var locations = getControlConfigurationsFromCounterexample(counterexample);
			final var cEx = new Counterexample<>(counterexample.getWord(), locations);

			final boolean feasable = result.isFeasable();
			// if (feasable) {
			// return new CorrectnessResult<>(false, currentAbstraction, result.getCounterexampleState(), cEx);
			// }

			final ITARefinementStrategy<L> strategy = mStrategyFactory.constructStrategy(getServices(), cEx,
					currentAbstraction, new SubtaskIterationIdentifier(mTaskIdentifier, getIteration()),
					mPredicateFactoryInterpolantAutomata, getPreconditionProvider(), getPostconditionProvider());

			final TraceAbstractionRefinementEngine<L> refinementEngine =
					new TraceAbstractionRefinementEngine<>(mServices, mLogger, strategy);
			mRefinementResult = refinementEngine.getResult();

			if (feasable) {
				return new CorrectnessResult<>(false, currentAbstraction, result.getCounterexampleState(), cEx);
			}

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

		throw new RuntimeException("Max iterations reached"); // TODO
	}

	public FeasabilityResult checkFeasability(final IRun<L, ?> counterexample)
			throws AutomataOperationCanceledException {
		final Script script = mCsToolkit.getManagedScript().getScript();

		final Word<L> word = counterexample.getWord();
		final int n = word.length();

		final List<SPredicate> interpolatedPredicates = initPredicates(counterexample);

		// int j = n;
		// while (!(word.getSymbol(j - 1) instanceof Summary)) {
		// final Term wp = mPredicateTransformer.weakestPrecondition(interpolatedPredicates.get(j),
		// word.getSymbol(j - 1).getTransformula());
		//
		// interpolatedPredicates.set(j - 1,
		// mPredicateFactory.newSPredicate(interpolatedPredicates.get(j - 1).getProgramPoint(), wp));
		//
		// if (j == 1) {
		// // final IPredicate notPredicate = mPredicateFactory.not(interpolatedPredicates.get(j - 1));
		// final Term notTerm = SmtUtils.not(script, interpolatedPredicates.get(j - 1).getFormula());
		// final LBool isSat = SmtUtils.checkSatTerm(script, notTerm);
		//
		// switch (isSat) {
		// case SAT:
		// return new FeasabilityResult(true, notTerm, interpolatedPredicates);
		// case UNSAT:
		// break;
		// default:
		// case UNKNOWN:
		// throw new RuntimeException("Unknown Sat"); // TODO handle properly
		//
		// }
		//
		// break;
		// }
		//
		// j--;
		// }

		int k = 0;
		while (k < n) {
			L symbol = word.getSymbol(k);
			final SPredicate preconditionPredicate = interpolatedPredicates.get(k);
			final SPredicate postconditionPredicate = interpolatedPredicates.get(k + 1);
			final Term sp = mPredicateTransformer.strongestPostcondition(interpolatedPredicates.get(k),
					symbol.getTransformula());
			final SPredicate spPredicate =
					mPredicateFactory.newSPredicate(postconditionPredicate.getProgramPoint(), sp);

			boolean strenghtenBackwards = false;
			if (k + 1 == n) { // TODO move this
				final LBool isSat = SmtUtils.checkSatTerm(script, sp);
				switch (isSat) {
				case SAT:
					strenghtenBackwards = true;
					break;
				case UNSAT:
					return new FeasabilityResult(false, script.term("false"), interpolatedPredicates);
				default:
				case UNKNOWN:
					throw new RuntimeException("unknown sat"); // TODO handle

				}
			}

			if (symbol instanceof Summary) {
				final LBool implicationHolds =
						SmtUtils.checkImplication(sp, postconditionPredicate.getFormula(), script);
				switch (implicationHolds) {
				case SAT: // implication holds not
					final Term strengthenedPostState = SmtUtils.and(script, postconditionPredicate.getFormula(), sp);
					interpolatedPredicates.set(k + 1, mPredicateFactory
							.newSPredicate(postconditionPredicate.getProgramPoint(), strengthenedPostState));

					final IPredicate postconditionTransitionedPredicate =
							mProgramExtractor.transformPostcondition(postconditionPredicate);
					final IPredicate spTransitionedPredicate = mProgramExtractor.transformPostcondition(spPredicate);

					final LBool contractedImplicationHolds =
							SmtUtils.checkImplication(spTransitionedPredicate.getFormula(),
									postconditionTransitionedPredicate.getFormula(), script);
					switch (contractedImplicationHolds) {
					case SAT: // contract holds not
						final IPredicate preconditionTransitionedPredicate =
								mProgramExtractor.transformPrecondition(preconditionPredicate);

						// TODO refactor to own function
						final IPredicate postconditionViolatedTransitionedPredicate =
								mPredicateFactory.not(postconditionTransitionedPredicate);

						final String functionName = ((Summary) symbol).getCallStatement().getMethodName();
						final INestedWordAutomaton<L, IPredicate> functionAbstraction =
								mProgramExtractor.initializeFunctionAbstraction(functionName,
										preconditionTransitionedPredicate, postconditionViolatedTransitionedPredicate);
						final CorrectnessResult<L> result = checkCorrectness(functionAbstraction);
						if (result.isCorrect()) {
							final IPredicate refinedPostcondition =
									mProgramExtractor.extractPostcondition(result.getAbstraction());
							strenghtenFunctionContract(functionName, preconditionTransitionedPredicate,
									refinedPostcondition);
						} else {
							final Term counterexampleState = result.getCounterexampleState();
							final Term negatedCounterexample = SmtUtils.not(script, counterexampleState);
							final BasicPredicate negatedCounterexamplePredicate =
									mPredicateFactory.newPredicate(negatedCounterexample);
							final UnmodifiableTransFormula callTransitionReverse = mProgramExtractor
									.getCallTransitionReverse(interpolatedPredicates.get(k).getProgramPoint());

							final Term negatedCounterexampleTransitioned = mPredicateTransformer
									.strongestPostcondition(negatedCounterexamplePredicate, callTransitionReverse);

							final SPredicate predicate = interpolatedPredicates.get(k); // TODO replace with
																						// preconditionPredicate var
							final Term andTerm =
									SmtUtils.and(script, predicate.getFormula(), negatedCounterexampleTransitioned);

							final SPredicate andPredicate =
									mPredicateFactory.newSPredicate(predicate.getProgramPoint(), andTerm);
							interpolatedPredicates.set(k, andPredicate);

							strenghtenBackwards = true;
							k--;
						}
						break;
					case UNSAT: // contract holds
						strenghtenBackwards = true;
						break;
					default:
					case UNKNOWN:
						throw new RuntimeException("unknown sat"); // TODO handle
					}
					break;
				case UNSAT: // implication holds
					interpolatedPredicates.set(k + 1, spPredicate);
					k++;
					continue;
				default:
				case UNKNOWN:
					throw new RuntimeException("unknown sat"); // TODO handle

				}

			} else if (k + 1 != n) {
				interpolatedPredicates.set(k + 1, spPredicate);
				k++;
				continue;
			}

			if (strenghtenBackwards) {
				while (k >= 0) {
					symbol = word.getSymbol(k);
					if (symbol instanceof Summary) {
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
					return new FeasabilityResult(true, notTerm, interpolatedPredicates);
				}

			}

		}

		throw new RuntimeException("Should not happen");
	}

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

	public static class SingleFunctionAutomatonWrapper<L> {
		final INestedWordAutomaton<L, IPredicate> mAbstraction;
		final UnmodifiableTransFormula mPreconditionTransFormula;
		final UnmodifiableTransFormula mPostconditionViolatedTransFormula;

		public SingleFunctionAutomatonWrapper(final INestedWordAutomaton<L, IPredicate> abstraction,
				final UnmodifiableTransFormula preconditionTransFormula,
				final UnmodifiableTransFormula postconditionViolatedTransFormula) {
			mAbstraction = abstraction;
			mPreconditionTransFormula = preconditionTransFormula;
			mPostconditionViolatedTransFormula = postconditionViolatedTransFormula;
		}

		public INestedWordAutomaton<L, IPredicate> getAbstraction() {
			return mAbstraction;
		}

		public UnmodifiableTransFormula getPreconditionTransFormula() {
			return mPreconditionTransFormula;
		}

		public UnmodifiableTransFormula getPostconditionViolatedTransFormula() {
			return mPostconditionViolatedTransFormula;
		}

	}

	public static class CorrectnessResult<L> {
		final boolean mIsCorrect;
		final INestedWordAutomaton<L, IPredicate> mAbstraction;
		final Term mCounterexampleState;
		final Counterexample<L> mCounterexampleTrace;

		public CorrectnessResult(final boolean isCorrect, final INestedWordAutomaton<L, IPredicate> abstraction,
				final Term counterexampleState, final Counterexample<L> counterexampleTrace) {
			mIsCorrect = isCorrect;
			mAbstraction = abstraction;
			mCounterexampleState = counterexampleState;
			mCounterexampleTrace = counterexampleTrace;
		}

		public boolean isCorrect() {
			return mIsCorrect;
		}

		public INestedWordAutomaton<L, IPredicate> getAbstraction() {
			return mAbstraction;
		}

		public Term getCounterexampleState() {
			return mCounterexampleState;
		}

		public Counterexample<L> getCounterexampleTrace() {
			return mCounterexampleTrace;
		}

		@Override
		public String toString() {
			return "CorrectnessResult [mIsCorrect=" + mIsCorrect + ", mAbstraction=" + mAbstraction
					+ ", mCounterexampleState=" + mCounterexampleState + "]";
		}
	}

	public static class FeasabilityResult {
		final boolean mIsFeasable;
		final Term mCounterexampleState;
		final List<SPredicate> mPredicates;

		public FeasabilityResult(final boolean isFeasable, final Term notTerm,
				final List<SPredicate> interpolatedPredicates) {
			mIsFeasable = isFeasable;
			mCounterexampleState = notTerm;
			mPredicates = interpolatedPredicates;
		}

		public boolean isFeasable() {
			return mIsFeasable;
		}

		public Term getCounterexampleState() {
			return mCounterexampleState;
		}

		public List<SPredicate> getPredicates() {
			return mPredicates;
		}

		@Override
		public String toString() {
			return "FeasabilityResult [mIsFeasable=" + mIsFeasable + ", mCounterexampleState=" + mCounterexampleState
					+ ", mPredicates=" + mPredicates + "]";
		}
	}

	/**
	 * Dummy class for Precondition and Postcondition Transitions that need to be dymamically checked
	 */
	public static class PrePostDummyTransition implements IIcfgTransition<IcfgLocation>, IInternalAction {

		private static final long serialVersionUID = -295366297188547709L;

		final String mProcedure;
		final UnmodifiableTransFormula mTransFormula;
		final String mPrettyPrinted;

		public PrePostDummyTransition(final String procedure, final UnmodifiableTransFormula transFormula) {
			this(procedure, transFormula, null);
		}

		public PrePostDummyTransition(final String procedure, final UnmodifiableTransFormula transFormula,
				final String prettyPrinted) {
			mProcedure = procedure;
			mTransFormula = transFormula;
			mPrettyPrinted = prettyPrinted != null ? prettyPrinted : "";
		}

		@Override
		public IPayload getPayload() {
			return new Payload();
		}

		@Override
		public boolean hasPayload() {
			return false;
		}

		@Override
		public String getPrecedingProcedure() {
			return mProcedure;
		}

		@Override
		public String getSucceedingProcedure() {
			return mProcedure;
		}

		@Override
		public UnmodifiableTransFormula getTransformula() {
			return mTransFormula;
		}

		@Override
		public IcfgLocation getSource() {
			return null;
		}

		@Override
		public IcfgLocation getTarget() {
			return null;
		}

		@Override
		public String toString() {
			return mPrettyPrinted;
		}

	}

	public static class AnySet<L> extends HashSet<L> { // TODO remove

		private static final long serialVersionUID = -2475140788612700623L;

		@Override
		public boolean contains(final Object o) {
			return true;
		}

	}

}
