package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
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
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
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
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.ProgramUtilities.AssureStatement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine.ITARefinementStrategy;

public class SummaryCegarLoop<L extends IIcfgTransition<?>> extends NwaCegarLoop<L> {

	// protected BasicPredicateFactory mBasicPredicateFactory;
	protected PredicateTransformer<Term, IPredicate, TransFormula> mPredicateTransformer;
	protected PredicateFactoryRefinement mPredicateFactoryRefinement;

	protected ProgramUtilities<L> mProgramUtilities;

	protected ContractMode mContractMode = ContractMode.GLOBAL_KEEP;

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

		mProgramUtilities = new ProgramUtilities<>(mIcfg, mServices, mPredicateFactory, mPredicateTransformer,
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

	protected void setFunctionContract(final String functionName, final Collection<FunctionContract> contracts) {
		for (final Summary summary : mProgramUtilities.getFunctionSummaries(functionName)) {
			// final UnmodifiableTransFormula transFormula =
			// buildContractTransFormula(summary, precondition, postcondition);

			final UnmodifiableTransFormula transFormula =
					FunctionContract.buildTransFormulaForContracts(summary, contracts, mProgramUtilities);

			// final UnmodifiableTransFormula mergedTransFormula =
			// mergeTransFormulas(summary.getTransformula(), transFormula);

			summary.setTransitionFormula(transFormula);
		}
	}

	protected UnmodifiableTransFormula buildContractTransFormula(final Summary summary, final IPredicate precondition,
			final IPredicate postcondition) {

		final Term transformedPrecondition = mProgramUtilities.callTransitionReverse(summary, precondition);

		// TODO needs transformed pre as param?
		final Term transformedPostcondition = mProgramUtilities.returnTransition(summary, precondition, postcondition);

		final Set<TermVariable> preconditionFreeVars = new HashSet<>();
		Collections.addAll(preconditionFreeVars, transformedPrecondition.getFreeVars());

		final Set<TermVariable> postconditionFreeVars = new HashSet<>();
		Collections.addAll(postconditionFreeVars, transformedPostcondition.getFreeVars());

		final Set<TermVariable> freeVars = new HashSet<>(preconditionFreeVars);
		freeVars.addAll(postconditionFreeVars);

		final Map<TermVariable, IProgramVar> mappedProgramVars = new HashMap<>();
		for (final TermVariable termVar : freeVars) {
			final IProgramVar programVar = mCsToolkit.getSymbolTable().getProgramVar(termVar);
			mappedProgramVars.put(termVar, programVar);
		}

		final Set<IProgramVar> callParams = mProgramUtilities.getCallParams(summary);
		final Set<IProgramVar> returnParams = mProgramUtilities.getReturnParams(summary);

		final Collection<TermVariable> quantifiablePreconditionVars =
				preconditionFreeVars.stream().filter(v -> !callParams.contains(mappedProgramVars.get(v))).toList();
		final Term quantifiedPrecondition = SmtUtils.quantifier(mCsToolkit.getManagedScript().getScript(),
				QuantifiedFormula.EXISTS, quantifiablePreconditionVars, transformedPrecondition);

		final Collection<TermVariable> quantifiablePostconditionVars =
				postconditionFreeVars.stream().filter(v -> !returnParams.contains(mappedProgramVars.get(v))).toList();
		final Term quantifiedPostcondition = SmtUtils.quantifier(mCsToolkit.getManagedScript().getScript(),
				QuantifiedFormula.EXISTS, quantifiablePostconditionVars, transformedPostcondition);

		final Set<TermVariable> quantifiedPreconditionFreeVars = new HashSet<>();
		Collections.addAll(quantifiedPreconditionFreeVars, quantifiedPrecondition.getFreeVars());

		final Set<TermVariable> quantifiedPostconditionFreeVars = new HashSet<>();
		Collections.addAll(quantifiedPostconditionFreeVars, quantifiedPostcondition.getFreeVars());

		final Map<TermVariable, TermVariable> preconditionTermVariableCopies =
				mCsToolkit.getManagedScript().constructFreshCopies(quantifiedPreconditionFreeVars);
		final Term substitutedPrecondition = Substitution.apply(mCsToolkit.getManagedScript(),
				preconditionTermVariableCopies, quantifiedPrecondition);

		final Map<TermVariable, TermVariable> postconditionTermVariableCopies =
				mCsToolkit.getManagedScript().constructFreshCopies(quantifiedPostconditionFreeVars);
		final Term substitutedPostcondition = Substitution.apply(mCsToolkit.getManagedScript(),
				postconditionTermVariableCopies, quantifiedPostcondition);

		final Term implication = SmtUtils.implies(mCsToolkit.getManagedScript().getScript(), substitutedPrecondition,
				substitutedPostcondition);

		final Map<IProgramVar, TermVariable> inVars = new HashMap<>();
		final Map<IProgramVar, TermVariable> outVars = new HashMap<>();

		for (final IProgramVar programVar : mappedProgramVars.values()) {
			final TermVariable termVariable = programVar.getTermVariable();
			final TermVariable preconditionCopy = preconditionTermVariableCopies.get(termVariable);
			final TermVariable postconditionCopy = postconditionTermVariableCopies.get(termVariable);
			if (preconditionCopy != null) {
				inVars.put(programVar, preconditionCopy);
				outVars.put(programVar, preconditionCopy);
			}
			if (postconditionCopy != null) {
				outVars.put(programVar, postconditionCopy);
			}
		}

		final TransFormulaBuilder builder = new TransFormulaBuilder(inVars, outVars, true, null, true, null, true);

		builder.setFormula(implication);
		builder.setInfeasibility(Infeasibility.UNPROVEABLE);

		return builder.finishConstruction(mCsToolkit.getManagedScript());
	}

	protected UnmodifiableTransFormula buildContractsTransFormula1(final Summary summary,
			final Collection<FunctionContract> contracts) {
		final Map<FunctionContract, Term> transformedPreconditions = new HashMap<>();
		final Map<FunctionContract, Term> transformedPostconditions = new HashMap<>();

		final Set<IProgramVar> callParams = mProgramUtilities.getCallParams(summary);
		final Set<IProgramVar> returnParams = mProgramUtilities.getReturnParams(summary);
		final Set<IProgramVar> callReturnParams = new HashSet<>(callParams);
		callReturnParams.addAll(returnParams);

		for (final FunctionContract contract : contracts) {
			final Term transformedPrecondition =
					mProgramUtilities.callTransitionReverse(summary, contract.getPrecondition());

			transformedPreconditions.put(contract, transformedPrecondition);
			final IPredicate transformedPreconditionPredicate = mPredicateFactory.newPredicate(transformedPrecondition);

			final Term transformedPostcondition = mProgramUtilities.returnTransition(summary,
					contract.getPostcondition(), transformedPreconditionPredicate);

			transformedPostconditions.put(contract, transformedPostcondition);
		}

		final Map<FunctionContract, Term> quantifiedPreconditions = new HashMap<>();
		final Map<FunctionContract, Term> quantifiedPostconditions = new HashMap<>();

		for (final FunctionContract contract : contracts) {
			final Term transformedPrecondition = transformedPreconditions.get(contract);
			final Term transformedPostcondition = transformedPostconditions.get(contract);

			final Set<TermVariable> preconditionFreeVars = new HashSet<>();
			Collections.addAll(preconditionFreeVars, transformedPrecondition.getFreeVars());

			final Collection<TermVariable> quantifiablePreconditionVars = preconditionFreeVars.stream()
					.filter(tv -> !callParams.contains(mCsToolkit.getSymbolTable().getProgramVar(tv))).toList();
			final Term quantifiedPrecondition = SmtUtils.quantifier(mCsToolkit.getManagedScript().getScript(),
					QuantifiedFormula.EXISTS, quantifiablePreconditionVars, transformedPrecondition);

			quantifiedPreconditions.put(contract, quantifiedPrecondition);

			final Set<TermVariable> postconditionFreeVars = new HashSet<>();
			Collections.addAll(postconditionFreeVars, transformedPostcondition.getFreeVars());

			final Collection<TermVariable> quantifiablePostconditionVars = postconditionFreeVars.stream()
					.filter(tv -> !callReturnParams.contains(mCsToolkit.getSymbolTable().getProgramVar(tv))).toList();
			final Term quantifiedPostcondition = SmtUtils.quantifier(mCsToolkit.getManagedScript().getScript(),
					QuantifiedFormula.EXISTS, quantifiablePostconditionVars, transformedPostcondition);

			quantifiedPostconditions.put(contract, quantifiedPostcondition);
		}

		final Map<IProgramVar, TermVariable> postVars = new HashMap<>();
		for (final IProgramVar returnParam : returnParams) {
			final TermVariable termVariable = mCsToolkit.getManagedScript().constructFreshTermVariable(
					returnParam.getTermVariable().getName() + "_post", returnParam.getSort());

			postVars.put(returnParam, termVariable);
		}

		final Map<FunctionContract, Term> substitutedPostconditions = new HashMap<>();

		for (final var postconditionEntry : quantifiedPostconditions.entrySet()) {
			final Map<TermVariable, TermVariable> postconditionOutVarMap = new HashMap<>();
			final Term post = postconditionEntry.getValue();
			for (final TermVariable freeVar : post.getFreeVars()) {
				final IProgramVar programVar = mCsToolkit.getSymbolTable().getProgramVar(freeVar);
				if (returnParams.contains(programVar)) {
					postconditionOutVarMap.put(freeVar, postVars.get(programVar));
				}
			}

			final Term substitution = Substitution.apply(mCsToolkit.getManagedScript(), postconditionOutVarMap,
					postconditionEntry.getValue());
			substitutedPostconditions.put(postconditionEntry.getKey(), substitution);
		}

		final Set<Term> implications = new HashSet<>();

		for (final FunctionContract contract : contracts) {
			final Term precondition = quantifiedPreconditions.get(contract);
			final Term postcondition = substitutedPostconditions.get(contract);

			final Term implication =
					SmtUtils.implies(mCsToolkit.getManagedScript().getScript(), precondition, postcondition);

			implications.add(implication);
		}

		final Term formula = SmtUtils.and(mCsToolkit.getManagedScript().getScript(), implications);

		final Map<IProgramVar, TermVariable> inVars = new HashMap<>();
		final Map<IProgramVar, TermVariable> outVars = new HashMap<>();

		for (final IProgramVar callParam : callParams) {
			final TermVariable termVariable = callParam.getTermVariable();
			inVars.put(callParam, termVariable);
			if (!returnParams.contains(callParam)) {
				outVars.put(callParam, termVariable);
			}
		}

		for (final IProgramVar returnParam : returnParams) {
			final TermVariable termVariable = postVars.get(returnParam);
			outVars.put(returnParam, termVariable);
		}

		final TransFormulaBuilder builder = new TransFormulaBuilder(inVars, outVars, true, null, true, null, true);

		builder.setFormula(formula);
		builder.setInfeasibility(Infeasibility.UNPROVEABLE);

		return builder.finishConstruction(mCsToolkit.getManagedScript());
	}

	// protected UnmodifiableTransFormula buildContractsTransFormula2(final Summary summary,
	// final Collection<FunctionContract> contracts) {
	//
	// final Map<FunctionContract, Term> transformedPreconditions = new HashMap<>();
	// final Map<FunctionContract, Term> transformedPostconditions = new HashMap<>();
	//
	// for (final FunctionContract contract : contracts) {
	// final Term transformedPrecondition =
	// mProgramExtractor.callTransitionReverse(summary, contract.getPrecondition());
	//
	// transformedPreconditions.put(contract, transformedPrecondition);
	//
	// // TODO needs transformed as param?
	// final Term transformedPostcondition = mProgramExtractor.returnTransition(summary,
	// contract.getPrecondition(), contract.getPostcondition());
	//
	// transformedPostconditions.put(contract, transformedPostcondition);
	// }
	//
	// final Set<TermVariable> preconditionFreeVars = new HashSet<>();
	// final Set<TermVariable> postconditionFreeVars = new HashSet<>();
	//
	// for (final FunctionContract contract : contracts) {
	// Collections.addAll(preconditionFreeVars, transformedPreconditions.get(contract).getFreeVars());
	// Collections.addAll(postconditionFreeVars, transformedPostconditions.get(contract).getFreeVars());
	// }
	//
	// final Set<TermVariable> freeVars = new HashSet<>(preconditionFreeVars);
	// freeVars.addAll(postconditionFreeVars);
	//
	// final Map<TermVariable, IProgramVar> mappedProgramVars = new HashMap<>();
	// for (final TermVariable termVar : freeVars) {
	// final IProgramVar programVar = mCsToolkit.getSymbolTable().getProgramVar(termVar);
	// mappedProgramVars.put(termVar, programVar);
	// }
	//
	// final Set<IProgramVar> callParams = mProgramExtractor.getCallParams(summary);
	// final Set<IProgramVar> returnParams = mProgramExtractor.getReturnParams(summary);
	//
	// final Map<FunctionContract, Term> quantifiedPreconditions = new HashMap<>();
	// final Map<FunctionContract, Term> quantifiedPostconditions = new HashMap<>();
	//
	// for (final FunctionContract contract : contracts) {
	// final Term transformedPrecondition = transformedPreconditions.get(contract);
	// final Term transformedPostcondition = transformedPostconditions.get(contract);
	//
	// final Collection<TermVariable> quantifiablePreconditionVars =
	// preconditionFreeVars.stream().filter(v -> !callParams.contains(mappedProgramVars.get(v))).toList();
	// final Term quantifiedPrecondition = SmtUtils.quantifier(mCsToolkit.getManagedScript().getScript(),
	// QuantifiedFormula.EXISTS, quantifiablePreconditionVars, transformedPrecondition);
	//
	// quantifiedPreconditions.put(contract, quantifiedPrecondition);
	//
	// final Collection<TermVariable> quantifiablePostconditionVars = postconditionFreeVars.stream()
	// .filter(v -> !returnParams.contains(mappedProgramVars.get(v))).toList();
	// final Term quantifiedPostcondition = SmtUtils.quantifier(mCsToolkit.getManagedScript().getScript(),
	// QuantifiedFormula.EXISTS, quantifiablePostconditionVars, transformedPostcondition);
	//
	// quantifiedPostconditions.put(contract, quantifiedPostcondition);
	// }
	//
	// final Set<TermVariable> quantifiedPreconditionFreeVars = new HashSet<>();
	// Collections.addAll(quantifiedPreconditionFreeVars, quantifiedPrecondition.getFreeVars());
	//
	// final Set<TermVariable> quantifiedPostconditionFreeVars = new HashSet<>();
	// Collections.addAll(quantifiedPostconditionFreeVars, quantifiedPostcondition.getFreeVars());
	//
	// final Map<TermVariable, TermVariable> preconditionTermVariableCopies =
	// mCsToolkit.getManagedScript().constructFreshCopies(quantifiedPreconditionFreeVars);
	// final Term substitutedPrecondition = Substitution.apply(mCsToolkit.getManagedScript(),
	// preconditionTermVariableCopies, quantifiedPrecondition);
	//
	// final Map<TermVariable, TermVariable> postconditionTermVariableCopies =
	// mCsToolkit.getManagedScript().constructFreshCopies(quantifiedPostconditionFreeVars);
	// final Term substitutedPostcondition = Substitution.apply(mCsToolkit.getManagedScript(),
	// postconditionTermVariableCopies, quantifiedPostcondition);
	//
	// return null;
	// }

	protected UnmodifiableTransFormula mergeTransFormulas(final Summary summary,
			final UnmodifiableTransFormula transFormula1, final UnmodifiableTransFormula transFormula2) {
		final Map<IProgramVar, TermVariable> inVars = new HashMap<>();
		final Map<IProgramVar, TermVariable> outVars = new HashMap<>();
		final Set<TermVariable> auxVars = new HashSet<>();

		final Set<IProgramVar> inProgramVars = new HashSet<>(transFormula1.getInVars().keySet());
		inProgramVars.addAll(transFormula2.getInVars().keySet());

		final Set<IProgramVar> outProgramVars = new HashSet<>(transFormula1.getOutVars().keySet());
		outProgramVars.addAll(transFormula2.getOutVars().keySet());

		// final Set<IProgramVar> callParams = mProgramExtractor.getCallParams(summary);
		// final Set<IProgramVar> returnParams = mProgramExtractor.getReturnParams(summary);

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

		mCsToolkit.getManagedScript().constructFreshTermVariable("d", null);

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
		for (final String function : mProgramUtilities.getFunctionsToCheck()) {
			final CorrectnessResult<L> result = runCorrectnessCheck(function);
			results.put(function, result);
		}

		return results;
	}

	protected CorrectnessResult<L> runCorrectnessCheck(final String function)
			throws AutomataOperationCanceledException { // TODO
		// rewrite

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
			return new CorrectnessResult<>(true, null, null, mProgramUtilities.newContractMap(), null, null);
		}

		// final INestedWordAutomaton<L, IPredicate> abstraction = mProgramExtractor.initializeRawAbstraction(function);
		final INestedWordAutomaton<L, IPredicate> abstraction =
				mProgramUtilities.initializeFunctionAbstraction(function, prePred, postViolatedPred);

		// final TermVariable virtualErrorVariable = mCsToolkit.getManagedScript().getScript().variable("vError",
		// SmtSortUtils.getBoolSort(mCsToolkit.getManagedScript()));
		//
		// final Term notTerm = mCsToolkit.getManagedScript().getScript().term("not", virtualErrorVariable);

		// mPredicateFactory.newPredicate(notTerm);

		System.out.println(abstraction);

		// TODO
		final CorrectnessResult<L> result = checkAutomatonCorrectness(abstraction, mProgramUtilities.newContractMap());
		System.out.println(result);
		return result;

	}

	public CorrectnessResult<L> checkCorrectness(final Summary summary,
			final Map<Summary, Collection<FunctionContract>> contracts, final IPredicate preconditionPredicate,
			final IPredicate postconditionViolatedPredicate) throws AutomataOperationCanceledException {
		final String functionName = summary.getCallStatement().getMethodName();
		final INestedWordAutomaton<L, IPredicate> functionAbstraction = mProgramUtilities
				.initializeFunctionAbstraction(functionName, preconditionPredicate, postconditionViolatedPredicate);

		return checkAutomatonCorrectness(functionAbstraction, contracts);

		// final IPredicate betterPost = mProgramExtractor.extractPostcondition(result.getAbstraction());
		//
		// final FunctionContract contract = new FunctionContract(preconditionPredicate, betterPost);

		// assignContractMap(contracts, contracts);

	}

	public CorrectnessResult<L> checkAutomatonCorrectness(final INestedWordAutomaton<L, IPredicate> abstraction,
			final Map<Summary, Collection<FunctionContract>> contracts) throws AutomataOperationCanceledException {

		INestedWordAutomaton<L, IPredicate> currentAbstraction = abstraction;

		final Map<Summary, Collection<FunctionContract>> functionContracts = new HashMap<>(contracts);

		for (int i = 0; i < 10000000; i++) { // TODO max iterations
			final IsEmpty<L, ?> emptynessCheck =
					new IsEmpty<>(new AutomataLibraryServices(getServices()), currentAbstraction, mSearchStrategy);
			if (emptynessCheck.getResult()) {
				// TODO top level automaton
				final FunctionContract contract = extractContract(currentAbstraction);
				return new CorrectnessResult<>(true, currentAbstraction, contract, functionContracts, null, null);
			}

			final IRun<L, ?> counterexample = emptynessCheck.getNestedRun();

			final FeasabilityResult result = checkFeasability(counterexample, functionContracts);
			functionContracts.putAll(result.getContracts());

			final var locations = getControlConfigurationsFromCounterexample(counterexample);
			final var cEx = new Counterexample<>(counterexample.getWord(), locations);

			final boolean feasable = result.isFeasable();
			if (feasable) {
				return new CorrectnessResult<>(false, currentAbstraction, null, functionContracts,
						result.getCounterexampleState(), cEx);
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

		throw new RuntimeException("Max iterations reached"); // TODO
	}

	private FunctionContract extractContract(final INestedWordAutomaton<L, IPredicate> currentAbstraction) {
		final Set<Term> preconditionTerms = new HashSet<>();
		final Set<Term> postconditionTerms = new HashSet<>();

		for (final IPredicate s : currentAbstraction.getStates()) {
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
		final IPredicate precondition = mPredicateFactory
				.newPredicate(SmtUtils.and(mCsToolkit.getManagedScript().getScript(), preconditionTerms));
		final IPredicate postcondition = mPredicateFactory
				.newPredicate(SmtUtils.or(mCsToolkit.getManagedScript().getScript(), postconditionTerms));

		return new FunctionContract(precondition, postcondition);
	}

	public FeasabilityResult checkFeasability(final IRun<L, ?> counterexample,
			final Map<Summary, Collection<FunctionContract>> contracts) throws AutomataOperationCanceledException {
		final Script script = mCsToolkit.getManagedScript().getScript();

		final Word<L> trace = counterexample.getWord();
		final int n = trace.length();

		Map<Summary, Collection<FunctionContract>> functionContracts = new HashMap<>(contracts);
		applyContracts(functionContracts);

		final List<SPredicate> interpolatedPredicates = initPredicates(counterexample);

		final L firstSummary = getFirstSummaryInTrace(trace);
		if (firstSummary == null) {
			return simpleCheck(trace, functionContracts, interpolatedPredicates);
		}

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
			boolean feasibilityProven = false;
			Term violatingTerm = null;

			if (symbol instanceof AssureStatement) {
				final AssureStatement assure = (AssureStatement) symbol;
				final IPredicate preconditionTransitionedPredicate =
						mProgramUtilities.transformPrecondition(assure.getSummary(), preconditionPredicate);

				final Term falseTerm = script.term("false");
				final IPredicate falsePredicate = mPredicateFactory.newPredicate(falseTerm);

				final INestedWordAutomaton<L, IPredicate> functionAbstraction =
						mProgramUtilities.initializeFunctionAbstraction(assure.getAssuredProcedure(),
								preconditionTransitionedPredicate, falsePredicate);
				final CorrectnessResult<L> result = checkAutomatonCorrectness(functionAbstraction, functionContracts);
				functionContracts = assignContractMap(functionContracts, result.getContracts());
				if (result.isCorrect()) {
					final FunctionContract assureContract = result.getFunctionContract();
					functionContracts = assignContract(functionContracts, assure.getSummary(), assureContract);
					applyContracts(functionContracts);

					return new FeasabilityResult(false, functionContracts, script.term("false"),
							interpolatedPredicates);
				}
				applyContracts(functionContracts);

				final Term counterexampleState = result.getCounterexampleState();
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

				if (symbol == firstSummary) {
					feasibilityProven = true;

					final IPredicate counterexampleStatePredicate = mPredicateFactory.newPredicate(counterexampleState);
					final Term counterexampleStateTransitioned =
							mProgramUtilities.callTransitionReverse(assure.getSummary(), counterexampleStatePredicate);

					violatingTerm = counterexampleStateTransitioned;
				}

				strenghtenBackwards = true;
				k--;

			} else if (k + 1 == n) {
				final LBool isSat = SmtUtils.checkSatTerm(script, sp);
				switch (isSat) {
				case SAT:
					strenghtenBackwards = true;
					break;
				case UNSAT:
					return new FeasabilityResult(false, functionContracts, script.term("false"),
							interpolatedPredicates);
				default:
				case UNKNOWN:
					throw new RuntimeException("unknown sat"); // TODO handle

				}
			} else if (symbol instanceof Summary) {
				final Summary summarySymbol = (Summary) symbol;
				final String summaryFunction = summarySymbol.getCallStatement().getMethodName();

				final LBool implicationHolds =
						SmtUtils.checkImplication(sp, postconditionPredicate.getFormula(), script);
				switch (implicationHolds) {
				case SAT: // implication holds not
					// final Term strengthenedPostState = SmtUtils.and(script, postconditionPredicate.getFormula(), sp);
					// interpolatedPredicates.set(k + 1, mPredicateFactory
					// .newSPredicate(postconditionPredicate.getProgramPoint(), strengthenedPostState));

					final IPredicate preconditionTransitionedPredicate =
							mProgramUtilities.transformPrecondition(summarySymbol, preconditionPredicate);

					final Set<TermVariable> toQuantifyPostPredicate = new HashSet<>();
					for (final IProgramVar programVar : postconditionPredicate.getVars()) {
						if (programVar.isOldvar()) {
							toQuantifyPostPredicate.add(programVar.getTermVariable());
						}
					}

					final Term postconditionQ = SmtUtils.quantifier(script, QuantifiedFormula.EXISTS,
							toQuantifyPostPredicate, postconditionPredicate.getFormula());
					final IPredicate postconditionQPredicate =
							mPredicateFactory.newSPredicate(postconditionPredicate.getProgramPoint(), postconditionQ);

					final Set<TermVariable> toQuantifySpPredicate = new HashSet<>();
					for (final IProgramVar programVar : spPredicate.getVars()) {
						if (programVar.isOldvar()) {
							toQuantifySpPredicate.add(programVar.getTermVariable());
						}
					}

					final Term spQ = SmtUtils.quantifier(script, QuantifiedFormula.EXISTS, toQuantifySpPredicate,
							spPredicate.getFormula());
					final IPredicate spQPredicate = mPredicateFactory.newSPredicate(spPredicate.getProgramPoint(), spQ);

					final IPredicate postconditionTransitionedPredicate = mProgramUtilities
							.transformPostcondition(summarySymbol, postconditionPredicate, preconditionPredicate);
					final IPredicate spTransitionedPredicate =
							mProgramUtilities.transformPostcondition(summarySymbol, spPredicate, preconditionPredicate);

					final LBool contractedImplicationHolds =
							SmtUtils.checkImplication(spTransitionedPredicate.getFormula(),
									postconditionTransitionedPredicate.getFormula(), script);

					switch (contractedImplicationHolds) {
					case SAT: // contract holds not
						// TODO refactor to own function
						final IPredicate postconditionViolatedTransitionedPredicate =
								mPredicateFactory.not(postconditionTransitionedPredicate);

						final INestedWordAutomaton<L, IPredicate> functionAbstraction =
								mProgramUtilities.initializeFunctionAbstraction(summaryFunction,
										preconditionTransitionedPredicate, postconditionViolatedTransitionedPredicate);
						final CorrectnessResult<L> result =
								checkAutomatonCorrectness(functionAbstraction, functionContracts);

						functionContracts = assignContractMap(functionContracts, result.getContracts());
						if (result.isCorrect()) {
							final FunctionContract contract = result.getFunctionContract();
							functionContracts = assignContract(functionContracts, summarySymbol, contract);
							applyContracts(functionContracts);
						} else {
							applyContracts(functionContracts);
							final Term counterexampleState = result.getCounterexampleState();
							final Term negatedCounterexample = SmtUtils.not(script, counterexampleState);
							final BasicPredicate negatedCounterexamplePredicate =
									mPredicateFactory.newPredicate(negatedCounterexample);

							final Term negatedCounterexampleTransitioned = mProgramUtilities
									.callTransitionReverse(summarySymbol, negatedCounterexamplePredicate);

							final Term andTerm = SmtUtils.and(script, preconditionPredicate.getFormula(),
									negatedCounterexampleTransitioned);

							final SPredicate andPredicate =
									mPredicateFactory.newSPredicate(preconditionPredicate.getProgramPoint(), andTerm);
							interpolatedPredicates.set(k, andPredicate);

							if (symbol == firstSummary) {
								feasibilityProven = true;

								final IPredicate counterexampleStatePredicate =
										mPredicateFactory.newPredicate(counterexampleState);
								final Term counterexampleStateTransitioned = mProgramUtilities
										.callTransitionReverse(summarySymbol, counterexampleStatePredicate);

								violatingTerm = counterexampleStateTransitioned;
							}

							strenghtenBackwards = true;
							k--;
						}
						break;
					case UNSAT: // contract holds for transformed predicate, check precondition -> false
						final Term trueTerm = script.term("true");
						final IPredicate truePredicate = mPredicateFactory.newPredicate(trueTerm);

						final INestedWordAutomaton<L, IPredicate> reachableEndCheckAbstraction =
								mProgramUtilities.initializeFunctionAbstraction(summaryFunction,
										preconditionTransitionedPredicate, truePredicate);
						final CorrectnessResult<L> reachableEndCheckResult =
								checkAutomatonCorrectness(reachableEndCheckAbstraction, functionContracts);
						functionContracts =
								assignContractMap(functionContracts, reachableEndCheckResult.getContracts());
						if (reachableEndCheckResult.isCorrect()) {
							final FunctionContract contract = reachableEndCheckResult.getFunctionContract();
							functionContracts = assignContract(functionContracts, summarySymbol, contract);
							applyContracts(functionContracts);

							continue;
						}
						applyContracts(functionContracts);

						final Term counterexampleState = reachableEndCheckResult.getCounterexampleState();
						final Term negatedCounterexample = SmtUtils.not(script, counterexampleState);
						final BasicPredicate negatedCounterexamplePredicate =
								mPredicateFactory.newPredicate(negatedCounterexample);

						final Term negatedCounterexampleTransitioned =
								mProgramUtilities.callTransitionReverse(summarySymbol, negatedCounterexamplePredicate);

						final Term andTerm = SmtUtils.and(script, preconditionPredicate.getFormula(),
								negatedCounterexampleTransitioned);

						final SPredicate andPredicate =
								mPredicateFactory.newSPredicate(preconditionPredicate.getProgramPoint(), andTerm);
						interpolatedPredicates.set(k, andPredicate);

						if (symbol == firstSummary) {
							feasibilityProven = true;

							final IPredicate counterexampleStatePredicate =
									mPredicateFactory.newPredicate(counterexampleState);
							final Term counterexampleStateTransitioned = mProgramUtilities
									.callTransitionReverse(summarySymbol, counterexampleStatePredicate);

							violatingTerm = counterexampleStateTransitioned;
						}

						strenghtenBackwards = true;
						k--;

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

			if (feasibilityProven) {
				Term current = violatingTerm;

				while (k >= 0) {
					symbol = trace.getSymbol(k);
					final IPredicate predicate = mPredicateFactory.newPredicate(current);
					current = mPredicateTransformer.pre(predicate, symbol.getTransformula());

					k--;
				}

				return new FeasabilityResult(true, functionContracts, current, interpolatedPredicates);

			}

			if (strenghtenBackwards) {
				while (k >= 0) {
					symbol = trace.getSymbol(k);
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
					throw new AssertionError("Should not have happened, feasibilityProven should have been true");

					// final Term notTerm = SmtUtils.not(script, interpolatedPredicates.get(0).getFormula());
					// return new FeasabilityResult(true, contracts, notTerm, interpolatedPredicates);
				}

			}

		}

		throw new RuntimeException("Should not happen");
	}

	protected FeasabilityResult simpleCheck(final Word<L> trace,
			final Map<Summary, Collection<FunctionContract>> functionContracts,
			final List<SPredicate> interpolatedPredicates) {
		final Script script = mCsToolkit.getManagedScript().getScript();

		Term current = script.term("true");
		final int n = trace.length();

		for (int k = 0; k < n; k++) {
			final L symbol = trace.getSymbol(k);
			final IPredicate predicate = mPredicateFactory.newPredicate(current);
			current = mPredicateTransformer.strongestPostcondition(predicate, symbol.getTransformula());
		}

		final LBool isSat = SmtUtils.checkSatTerm(script, current);
		switch (isSat) {
		case SAT:
			break;
		case UNSAT:
			return new FeasabilityResult(false, functionContracts, script.term("false"), interpolatedPredicates);
		default:
		case UNKNOWN:
			throw new RuntimeException("unknown sat"); // TODO handle

		}

		for (int k = n - 1; k >= 0; k--) {
			final L symbol = trace.getSymbol(k);
			final IPredicate predicate = mPredicateFactory.newPredicate(current);
			current = mPredicateTransformer.pre(predicate, symbol.getTransformula());
		}

		return new FeasabilityResult(true, functionContracts, current, interpolatedPredicates);

	}

	protected L getFirstSummaryInTrace(final Word<L> trace) {
		for (final L symbol : trace) {
			if (symbol instanceof Summary || symbol instanceof AssureStatement) {
				return symbol;
			}
		}

		return null;
	}

	protected static Map<Summary, Collection<FunctionContract>> assignContract(
			final Map<Summary, Collection<FunctionContract>> oldContracts, final Summary summary,
			final FunctionContract contract) {

		final Map<Summary, Collection<FunctionContract>> newMap = new HashMap<>();
		for (final var entry : oldContracts.entrySet()) {
			final Summary entrySummary = entry.getKey();
			final Collection<FunctionContract> old = entry.getValue();
			final Collection<FunctionContract> newContracts = new HashSet<>(old);
			if (summary.getCallStatement().getMethodName().equals(entrySummary.getCallStatement().getMethodName())) {
				newContracts.add(contract);
			}

			newMap.put(entrySummary, newContracts);
		}

		return newMap;

	}

	protected static Map<Summary, Collection<FunctionContract>> assignContractMap(
			final Map<Summary, Collection<FunctionContract>> oldContracts,
			final Map<Summary, Collection<FunctionContract>> contracts) {

		final Map<Summary, Collection<FunctionContract>> newMap = new HashMap<>();
		// TODO modes
		for (final var entry : oldContracts.entrySet()) {
			final Summary summary = entry.getKey();
			final Collection<FunctionContract> old = entry.getValue();

			final Collection<FunctionContract> newContracts = new HashSet<>(old);
			newContracts.addAll(contracts.get(summary));

			newMap.put(summary, newContracts);
		}

		return newMap;

	}

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
		final FunctionContract mFunctionContract;
		final Map<Summary, Collection<FunctionContract>> mContracts;
		final Term mCounterexampleState;
		final Counterexample<L> mCounterexampleTrace;

		public CorrectnessResult(final boolean isCorrect, final INestedWordAutomaton<L, IPredicate> abstraction,
				final FunctionContract functionContract, final Map<Summary, Collection<FunctionContract>> contracts,
				final Term counterexampleState, final Counterexample<L> counterexampleTrace) {
			mIsCorrect = isCorrect;
			mAbstraction = abstraction;
			mFunctionContract = functionContract;
			mContracts = contracts;
			mCounterexampleState = counterexampleState;
			mCounterexampleTrace = counterexampleTrace;
		}

		public boolean isCorrect() {
			return mIsCorrect;
		}

		public INestedWordAutomaton<L, IPredicate> getAbstraction() {
			return mAbstraction;
		}

		public FunctionContract getFunctionContract() {
			return mFunctionContract;
		}

		public Map<Summary, Collection<FunctionContract>> getContracts() {
			return mContracts;
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
		final Map<Summary, Collection<FunctionContract>> mContracts;
		final Term mCounterexampleState;
		final List<SPredicate> mPredicates;

		public FeasabilityResult(final boolean isFeasable, final Map<Summary, Collection<FunctionContract>> contracts,
				final Term counterexampleState, final List<SPredicate> interpolatedPredicates) {
			mIsFeasable = isFeasable;
			mContracts = contracts;
			mCounterexampleState = counterexampleState;
			mPredicates = interpolatedPredicates;
		}

		public Map<Summary, Collection<FunctionContract>> getContracts() {
			return mContracts;
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

	public enum ContractMode {
		GLOBAL_KEEP, GLOBAL_RESET, LOCAL_KEEP, LOCAL_RESET,
	}

	public static class AnySet<L> extends HashSet<L> { // TODO remove

		private static final long serialVersionUID = -2475140788612700623L;

		@Override
		public boolean contains(final Object o) {
			return true;
		}

	}

}
