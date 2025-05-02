package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.core.model.models.Payload;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Spec;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.StringDebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.SPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction.NwaInitialAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.SummaryCegarLoop.SingleFunctionAutomatonWrapper;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;

public class ProgramUtilities<L extends IIcfgTransition<?>> {

	protected IIcfg<?> mIcfg;

	protected IUltimateServiceProvider mServices;
	protected PredicateFactory mPredicateFactory;
	protected PredicateTransformer<Term, IPredicate, TransFormula> mPredicateTransformer;
	protected PredicateFactoryRefinement mStateFactoryForRefinement;
	protected Set<? extends IcfgLocation> mErrorLocs;
	protected CfgSmtToolkit mCsToolkit;
	protected TAPreferences mPref;

	protected Set<String> mFunctionsToCheck;
	protected Map<String, INestedWordAutomaton<L, IPredicate>> mFunctionAutomataRaw;
	protected Map<String, INestedWordAutomaton<L, IPredicate>> mFunctionAutomata;
	protected Map<String, UnmodifiableTransFormula> mPreconditionTransFormulas;
	protected Map<String, UnmodifiableTransFormula> mPostconditionViolatedTransFormulas;

	protected Map<String, Collection<IPredicate[]>> mFunctionContracts; // TODO remove

	protected Map<String, Collection<Summary>> mFunctionSummaries;
	protected Set<String> mFunctionsWithImplementation;
	protected Set<String> mFunctionsToAssure;
	protected Map<Summary, AssureStatement> mAssureStatements;

	protected Map<Call, Summary> mCallSummaries;
	protected Map<Return, Summary> mReturnSummaries;

	protected Map<Summary, UnmodifiableTransFormula> mCallTransitions;
	protected Map<Summary, UnmodifiableTransFormula> mReturnTransitions;

	protected Map<Summary, Set<IProgramVar>> mCallParams;
	protected Map<Summary, Set<IProgramVar>> mReturnParams;

	protected Map<String, IcfgLocation> dummyPreLocations;
	protected Map<String, IcfgLocation> dummyPostLocations;
	protected Map<Summary, IcfgLocation> dummyAssureLocations;

	public ProgramUtilities(final IIcfg<?> icfg, final IUltimateServiceProvider services,
			final PredicateFactory predicateFactory,
			final PredicateTransformer<Term, IPredicate, TransFormula> predicateTransformer,
			final PredicateFactoryRefinement stateFactoryForRefinement, final Set<? extends IcfgLocation> errorLocs,
			final CfgSmtToolkit csToolkit, final TAPreferences pref) {
		mIcfg = icfg;
		mServices = services;
		mPredicateFactory = predicateFactory;
		mPredicateTransformer = predicateTransformer;
		mStateFactoryForRefinement = stateFactoryForRefinement;
		mErrorLocs = errorLocs;
		mCsToolkit = csToolkit;
		mPref = pref;

		final NwaInitialAbstractionProvider<L> nonInterproceduralAbstractionProvider =
				new NwaInitialAbstractionProvider<>(mServices, mStateFactoryForRefinement, false, mPredicateFactory,
						mPref.getHoareSettings());

		final INestedWordAutomaton<L, IPredicate> nonInterproceduralAbstraction =
				nonInterproceduralAbstractionProvider.getInitialAbstraction(mIcfg, mErrorLocs);

		initFunctionAutomata(nonInterproceduralAbstraction);

		mFunctionContracts = null; // TODO remove

		dummyPreLocations = new HashMap<>();
		dummyPostLocations = new HashMap<>();

		mFunctionsWithImplementation = new HashSet<>();
		for (final String function : mIcfg.getProcedureEntryNodes().keySet()) {
			mFunctionsWithImplementation.add(function);
			dummyPreLocations.put(function,
					new IcfgLocation(new StringDebugIdentifier(function + ":dummyPreLoc"), function));
			dummyPostLocations.put(function,
					new IcfgLocation(new StringDebugIdentifier(function + ":dummyPostLoc"), function));
		}

		extractCallReturnTransitions();

		dummyAssureLocations = new HashMap<>();
		mFunctionSummaries.values().stream().flatMap(Collection::stream).forEach(s -> dummyAssureLocations.put(s,
				new IcfgLocation(new StringDebugIdentifier(s + ":dummyAssureLoc"), s.getPrecedingProcedure())));

		final Term trueTerm = mCsToolkit.getManagedScript().getScript().term("true");
		final IPredicate truePredicate = mPredicateFactory.newPredicate(trueTerm);
		final UnmodifiableTransFormula trueTransFormula =
				TransFormulaBuilder.constructTransFormulaFromPredicate(truePredicate, mCsToolkit.getManagedScript());

		extractFunctionsToAssure();

		mAssureStatements = new HashMap<>();
		mFunctionSummaries.values().stream().flatMap(Collection::stream).forEach(s -> {
			dummyAssureLocations.put(s,
					new IcfgLocation(new StringDebugIdentifier(s + ":dummyAssureLoc"), s.getPrecedingProcedure()));
			mAssureStatements.put(s, new AssureStatement(s, trueTransFormula));
		});

		mCallParams = new HashMap<>();
		mReturnParams = new HashMap<>();
		for (final var callTransition : mCallTransitions.entrySet()) {
			final Summary summary = callTransition.getKey();

			final Set<IProgramVar> params = new HashSet<>(callTransition.getValue().getInVars().keySet());
			final Set<IProgramNonOldVar> modifiableGlobalVars = mCsToolkit.getModifiableGlobalsTable()
					.getModifiedBoogieVars(summary.getCallStatement().getMethodName());

			params.addAll(modifiableGlobalVars);
			// params.addAll(modifiableGlobalVars.stream().map(IProgramNonOldVar::getOldVar).toList());
			mCallParams.put(callTransition.getKey(), params);
		}
		for (final var returnTransition : mReturnTransitions.entrySet()) {
			final Summary summary = returnTransition.getKey();

			final Set<IProgramVar> params = new HashSet<>(returnTransition.getValue().getOutVars().keySet());
			final Set<IProgramNonOldVar> modifiableGlobalVars = mCsToolkit.getModifiableGlobalsTable()
					.getModifiedBoogieVars(summary.getCallStatement().getMethodName());

			params.addAll(modifiableGlobalVars);
			// params.addAll(modifiableGlobalVars.stream().map(IProgramNonOldVar::getOldVar).toList());
			mReturnParams.put(summary, params);
		}

	}

	protected void extractFunctionsToAssure() {
		mFunctionsToAssure = new HashSet<>();

		final Set<String> functionsWithErrorState = new HashSet<>();

		final Map<String, Collection<String>> calledFunctions = new HashMap<>();
		mFunctionAutomataRaw.keySet().stream().forEach(f -> calledFunctions.put(f, new HashSet<>()));

		for (final var entry : mFunctionAutomataRaw.entrySet()) {
			final String function = entry.getKey();
			final var automaton = entry.getValue();
			if (!automaton.getFinalStates().isEmpty()) {
				functionsWithErrorState.add(function);
			}

			for (final L symbol : automaton.getAlphabet()) {
				if (symbol instanceof Summary && ((Summary) symbol).getCallStatement() != null) {
					calledFunctions.get(function).add(((Summary) symbol).getCallStatement().getMethodName());
				}
			}
		}

		for (final String f : calledFunctions.keySet()) {
			final Set<String> visited = new HashSet<>();
			final Queue<String> queue = new ArrayDeque<>();
			queue.add(f);

			while (!queue.isEmpty()) {
				final String current = queue.poll();
				if (visited.contains(current)) {
					continue;
				}
				visited.add(current);
				if (functionsWithErrorState.contains(current)) {
					mFunctionsToAssure.add(f);
					break;
				}

				queue.addAll(calledFunctions.get(current));
			}
		}

	}

	protected void extractCallReturnTransitions() {
		mFunctionSummaries = new HashMap<>();

		mCallSummaries = new HashMap<>();
		mReturnSummaries = new HashMap<>();

		mCallTransitions = new HashMap<>();
		mReturnTransitions = new HashMap<>();

		final Set<Call> calls = new HashSet<>();
		final Set<Return> returns = new HashSet<>();
		final Set<Summary> summaries = new HashSet<>();

		final Map<String, ? extends IcfgLocation> entryNodes = mIcfg.getProcedureEntryNodes();

		final Set<IcfgLocation> visited = new HashSet<>();
		final Queue<IcfgLocation> queue = new ArrayDeque<>(entryNodes.values());
		while (!queue.isEmpty()) {
			final IcfgLocation current = queue.remove();
			if (visited.contains(current)) {
				continue;
			}

			visited.add(current);

			for (final IcfgEdge edge : current.getOutgoingEdges()) {
				final IcfgLocation target = edge.getTarget();
				if (edge instanceof Call) {
					calls.add((Call) edge);
				} else if (edge instanceof Return) {
					returns.add((Return) edge);
				}

				if (edge instanceof Summary) {
					summaries.add((Summary) edge);
				}
				queue.add(target);
			}
		}

		for (final Summary summary : summaries) {
			final String functionName = summary.getCallStatement().getMethodName();

			mFunctionSummaries.putIfAbsent(functionName, new ArrayList<>());
			final Collection<Summary> functionSummaries = mFunctionSummaries.get(functionName);
			functionSummaries.add(summary);

			final boolean hasImplementation = summary.calledProcedureHasImplementation();
			if (hasImplementation) {
				final Call callEdge = calls.stream()
						.filter(c -> c.getCallStatement().equals(summary.getCallStatement())).findAny().get();

				final Return returnEdge = returns.stream()
						.filter(r -> r.getCallStatement().equals(summary.getCallStatement())).findAny().get();

				mCallSummaries.put(callEdge, summary);
				mReturnSummaries.put(returnEdge, summary);

				final UnmodifiableTransFormula callTransFormula = callEdge.getTransformula();
				mCallTransitions.put(summary, callTransFormula);

				final UnmodifiableTransFormula returnTransFormula = returnEdge.getTransformula();
				mReturnTransitions.put(summary, returnTransFormula);
			}
		}
	}

	@Deprecated
	protected UnmodifiableTransFormula reverseTransFormulaInOutVars(final UnmodifiableTransFormula transFormula) {
		final TransFormulaBuilder builder = new TransFormulaBuilder(transFormula.getOutVars(), transFormula.getInVars(),
				transFormula.getNonTheoryConsts().isEmpty(), transFormula.getNonTheoryConsts(),
				transFormula.getBranchEncoders().isEmpty(), transFormula.getBranchEncoders(),
				transFormula.getAuxVars().isEmpty());

		for (final TermVariable auxVar : transFormula.getAuxVars()) {
			builder.addAuxVar(auxVar);
		}

		builder.setFormula(transFormula.getFormula());
		builder.setInfeasibility(transFormula.isInfeasible());

		// builder.addAuxVarsButRenameToFreshCopies(null, null);

		return builder.finishConstruction(mCsToolkit.getManagedScript());
	}

	@Deprecated
	protected static Map<Summary, Map<IProgramVar, IProgramVar>>
			extractVarMappings(final Map<Summary, UnmodifiableTransFormula> transitions) {
		final HashMap<Summary, Map<IProgramVar, IProgramVar>> mappings = new HashMap<>();
		for (final var entry : transitions.entrySet()) {
			final Summary summary = entry.getKey();
			final UnmodifiableTransFormula transFormula = entry.getValue();

			final Map<IProgramVar, IProgramVar> varMapping = new HashMap<>();

			final List<Set<TermVariable>> equalities = getEqualities(transFormula);
			final Map<TermVariable, IProgramVar> outTermVarMapping = new HashMap<>();

			for (final Entry<IProgramVar, TermVariable> outVar : transFormula.getOutVars().entrySet()) {
				final IProgramVar programVar = outVar.getKey();
				final TermVariable termVar = outVar.getValue();

				for (final Set<TermVariable> equality : equalities) {
					if (equality.size() == 2 && equality.contains(termVar)) {
						final TermVariable other = equality.stream().filter(tv -> !tv.equals(termVar)).findAny().get();
						outTermVarMapping.put(other, programVar);
					}
				}
			}

			for (final Entry<IProgramVar, TermVariable> inVar : transFormula.getInVars().entrySet()) {
				final IProgramVar programVar = inVar.getKey();
				final TermVariable termVar = inVar.getValue();

				final IProgramVar mappedProgramVar = outTermVarMapping.get(termVar);

				varMapping.put(programVar, mappedProgramVar);
			}

			mappings.put(summary, varMapping);
		}

		return mappings;
	}

	@Deprecated
	protected static List<Set<TermVariable>> getEqualities(final UnmodifiableTransFormula equalityTransFormula) {
		final List<Set<TermVariable>> equalities = new ArrayList<>();

		final ApplicationTerm formula = (ApplicationTerm) equalityTransFormula.getFormula();
		switch (formula.getFunction().getName()) {
		case "=":
			equalities.add(Set.of(formula.getFreeVars()));
			break;
		case "and":
			for (final Term parameter : formula.getParameters()) {
				equalities.add(Set.of(parameter.getFreeVars()));
			}
			break;
		default:
		}

		return equalities;
	}

	public void initFunctionAutomata(final INestedWordAutomaton<L, IPredicate> abstraction) {
		mFunctionsToCheck = new HashSet<>();
		mFunctionAutomata = new HashMap<>();
		mFunctionAutomataRaw = new HashMap<>();
		mPreconditionTransFormulas = new HashMap<>();
		mPostconditionViolatedTransFormulas = new HashMap<>();

		final Set<ISLPredicate> functionAbstractionStartNodes =
				abstraction.getStates().stream().filter(p -> !abstraction.internalPredecessors(p).iterator().hasNext())
						.filter(ISLPredicate.class::isInstance).map(p -> (ISLPredicate) p).collect(Collectors.toSet());

		for (final ISLPredicate startNode : functionAbstractionStartNodes) {
			final String function = startNode.getProgramPoint().getProcedure();

			if (abstraction.isInitial(startNode)) {
				mFunctionsToCheck.add(function);
			}

			final INestedWordAutomaton<L, IPredicate> functionNwaRaw =
					constructSingleFunctionAutomatonRaw(abstraction, startNode);
			mFunctionAutomataRaw.put(function, functionNwaRaw);

			final SingleFunctionAutomatonWrapper<L> functionNwaWrapper =
					constructSingleFunctionAutomaton(abstraction, startNode);
			final INestedWordAutomaton<L, IPredicate> functionNwa = functionNwaWrapper.getAbstraction();
			mFunctionAutomata.put(function, functionNwa);
			mPreconditionTransFormulas.put(function, functionNwaWrapper.getPreconditionTransFormula());
			mPostconditionViolatedTransFormulas.put(function,
					functionNwaWrapper.getPostconditionViolatedTransFormula());
		}
	}

	public INestedWordAutomaton<L, IPredicate> constructSingleFunctionAutomatonRaw(
			final INestedWordAutomaton<L, IPredicate> abstraction, final ISLPredicate initialState) {
		final Set<L> alphabet = new HashSet<>();

		final NestedWordAutomaton<L, IPredicate> automaton = new NestedWordAutomaton<>(
				new AutomataLibraryServices(mServices), new VpAlphabet<>(alphabet), mStateFactoryForRefinement);

		final Map<IPredicate, List<OutgoingInternalTransition<L, IPredicate>>> edges = new HashMap<>();
		final Map<IPredicate, IPredicate> newPredicates = new HashMap<>();
		final Set<IPredicate> visited = new HashSet<>();
		final Queue<IPredicate> queue = new ArrayDeque<>();

		queue.add(initialState);
		while (!queue.isEmpty()) {
			final IPredicate current = queue.remove();
			if (visited.contains(current)) {
				continue;
			}
			visited.add(current);

			final List<OutgoingInternalTransition<L, IPredicate>> outgoing = new ArrayList<>();
			for (final var edge : abstraction.internalSuccessors(current)) {
				final IPredicate succ = edge.getSucc();
				outgoing.add(edge);
				queue.add(succ);
			}

			edges.put(current, outgoing);

			final boolean isInitial = abstraction.isInitial(current);
			final boolean isFinal = abstraction.isFinal(current);

			final IPredicate newPred =
					mPredicateFactory.newSPredicate(((ISLPredicate) current).getProgramPoint(), current.getFormula());
			automaton.addState(isInitial, isFinal, newPred);
			newPredicates.put(current, newPred);
		}

		for (final var outgoingEdges : edges.entrySet()) {
			final IPredicate source = outgoingEdges.getKey();
			for (final var edge : outgoingEdges.getValue()) {
				final IPredicate newSource = newPredicates.get(source);
				final IPredicate newTarget = newPredicates.get(edge.getSucc());
				if (newSource != null && newTarget != null) {
					final L letter = edge.getLetter();
					alphabet.add(letter);
					automaton.addInternalTransition(newSource, letter, newTarget);
				}
			}
		}

		return automaton;
	}

	public SingleFunctionAutomatonWrapper<L> constructSingleFunctionAutomaton(
			final INestedWordAutomaton<L, IPredicate> abstraction, final ISLPredicate initialState) {
		final Set<L> alphabet = new HashSet<>();

		final NestedWordAutomaton<L, IPredicate> automaton = new NestedWordAutomaton<>(
				new AutomataLibraryServices(mServices), new VpAlphabet<>(alphabet), mStateFactoryForRefinement);

		final Map<IPredicate, List<OutgoingInternalTransition<L, IPredicate>>> edges = new HashMap<>();
		final Map<IPredicate, IPredicate> newPredicates = new HashMap<>();
		final Set<IPredicate> visited = new HashSet<>();
		final Queue<IPredicate> queue = new ArrayDeque<>();

		final IcfgEdge preconditionEdge = getPreconditionEdge(initialState);
		IcfgEdge postconditionViolatedEdge = null;
		final IcfgLocation initialLocation;
		if (preconditionEdge != null) {
			initialLocation = preconditionEdge.getTarget();
		} else {
			initialLocation = initialState.getProgramPoint();
		}

		queue.add(initialState);
		while (!queue.isEmpty()) {
			final IPredicate current = queue.remove();
			if (visited.contains(current)) {
				continue;
			}
			visited.add(current);

			final List<OutgoingInternalTransition<L, IPredicate>> outgoing = new ArrayList<>();
			for (final var edge : abstraction.internalSuccessors(current)) {
				final IPredicate succ = edge.getSucc();
				outgoing.add(edge);
				queue.add(succ);
			}

			edges.put(current, outgoing);

			if (current == initialState && preconditionEdge != null) {
				continue; // skip precondition state
			}

			final boolean isTrap = !abstraction.internalSuccessors(current).iterator().hasNext();
			final boolean isFinal = abstraction.isFinal(current);
			if (isTrap) {
				final IcfgEdge edge = getPostconditionEdge((ISLPredicate) current);
				if (edge != null) {
					if (isFinal) {
						if (postconditionViolatedEdge != null) {
							throw new RuntimeException("Duplicate postcondition state"); // Should never happen
						}

						postconditionViolatedEdge = edge;
					}
					continue; // skip postcondition state
				}
			}

			final IPredicate newPred =
					mPredicateFactory.newSPredicate(((ISLPredicate) current).getProgramPoint(), current.getFormula());
			automaton.addState(((ISLPredicate) current).getProgramPoint().equals(initialLocation), isFinal, newPred);
			newPredicates.put(current, newPred);
		}

		for (final var outgoingEdges : edges.entrySet()) {
			final IPredicate source = outgoingEdges.getKey();
			for (final var edge : outgoingEdges.getValue()) {
				final IPredicate newSource = newPredicates.get(source);
				final IPredicate newTarget = newPredicates.get(edge.getSucc());
				if (newSource != null && newTarget != null) {
					final L letter = edge.getLetter();
					alphabet.add(letter);
					automaton.addInternalTransition(newSource, letter, newTarget);
				}
			}

		}

		final UnmodifiableTransFormula preconditionTransFormula =
				preconditionEdge != null ? preconditionEdge.getTransformula() : null;
		final UnmodifiableTransFormula postconditionViolatedTransFormula =
				postconditionViolatedEdge != null ? postconditionViolatedEdge.getTransformula() : null;

		return new SingleFunctionAutomatonWrapper<>(automaton, preconditionTransFormula,
				postconditionViolatedTransFormula);
	}

	protected static IcfgEdge getPreconditionEdge(final ISLPredicate preconditionState) {
		final IcfgLocation location = preconditionState.getProgramPoint();
		if (location.getOutgoingEdges().size() != 1) {
			return null;
		}

		final IcfgEdge edge = location.getOutgoingEdges().getFirst();
		final IAnnotations annotations = edge.getPayload().getAnnotations()
				.get("de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check");
		if (annotations instanceof Check && ((Check) annotations).getSpec().contains(Spec.PRE_CONDITION)
				&& !((BoogieIcfgLocation) edge.getTarget()).isErrorLocation()) {
			return edge;
		}

		return null;
	}

	protected static IcfgEdge getPostconditionEdge(final ISLPredicate postconditionState) {
		final IcfgLocation location = postconditionState.getProgramPoint();
		if (location.getIncomingEdges().size() != 1) {
			return null;
		}

		final IcfgEdge edge = location.getIncomingEdges().getFirst();
		final IAnnotations annotations = edge.getPayload().getAnnotations()
				.get("de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check");
		if (annotations instanceof Check && ((Check) annotations).getSpec().contains(Spec.POST_CONDITION)) {
			return edge;
		}

		return null;

	}

	public INestedWordAutomaton<L, IPredicate> constructSingleAutomaton1(
			final INestedWordAutomaton<L, IPredicate> abstraction, final L preconditionTransition,
			final L postconditionViolatedTransition) {

		final Set<L> alphabet = new HashSet<>(abstraction.getAlphabet());
		if (preconditionTransition != null) {
			alphabet.add(preconditionTransition);
		}
		if (postconditionViolatedTransition != null) {
			alphabet.add(postconditionViolatedTransition);
		}

		final NestedWordAutomaton<L, IPredicate> automaton = new NestedWordAutomaton<>(
				new AutomataLibraryServices(mServices), new VpAlphabet<>(alphabet), mStateFactoryForRefinement);

		final Map<IPredicate, Iterable<OutgoingInternalTransition<L, IPredicate>>> originalEdges = new HashMap<>();
		final Map<IPredicate, IPredicate> newPredicates = new HashMap<>();

		for (final IPredicate state : abstraction.getStates()) {
			final IcfgLocation programPoint = ((ISLPredicate) state).getProgramPoint();

			final IPredicate newState = mPredicateFactory.newSPredicate(programPoint, state.getFormula());

			newPredicates.put(state, newState);
			originalEdges.put(newState, abstraction.internalSuccessors(state));

			final boolean isInitial = abstraction.isInitial(state);
			final boolean isFinal = abstraction.isFinal(state);
			final boolean hasSuccessors = abstraction.internalSuccessors(state).iterator().hasNext();

			automaton.addState(preconditionTransition == null && isInitial, abstraction.isFinal(state), newState);

			if (preconditionTransition != null && isInitial) {
				final Term trueTerm = mCsToolkit.getManagedScript().getScript().term("true");
				final IPredicate newPreconditionState =
						mPredicateFactory.newSPredicate(dummyPreLocations.get(programPoint.getProcedure()), trueTerm);

				automaton.addState(true, false, newPreconditionState);
				automaton.addInternalTransition(newPreconditionState, preconditionTransition, newState);
			}

			if (postconditionViolatedTransition != null && !hasSuccessors && !isFinal) {
				final Term trueTerm = mCsToolkit.getManagedScript().getScript().term("true");
				final IPredicate newPostconditionViolatedState =
						mPredicateFactory.newSPredicate(dummyPostLocations.get(programPoint.getProcedure()), trueTerm);

				automaton.addState(false, true, newPostconditionViolatedState);
				automaton.addInternalTransition(newState, postconditionViolatedTransition,
						newPostconditionViolatedState);
			}

		}

		for (final var entry : originalEdges.entrySet()) {
			final IPredicate newState = entry.getKey();
			final var transitions = entry.getValue();
			for (final var transition : transitions) {
				final IPredicate newSucc = newPredicates.get(transition.getSucc());
				automaton.addInternalTransition(newState, transition.getLetter(), newSucc);
			}
		}

		return automaton;

	}

	// TODO top level
	public INestedWordAutomaton<L, IPredicate> constructFunctionAutomaton(
			final INestedWordAutomaton<L, IPredicate> abstraction, final L preconditionTransition,
			final L postconditionViolatedTransition, Collection<String> functionsToAssure) {

		if (functionsToAssure == null) {
			functionsToAssure = Collections.emptySet();
		}

		final Set<L> alphabet = new HashSet<>(abstraction.getAlphabet());
		alphabet.add(preconditionTransition);
		alphabet.add(postconditionViolatedTransition);

		final NestedWordAutomaton<L, IPredicate> automaton = new NestedWordAutomaton<>(
				new AutomataLibraryServices(mServices), new VpAlphabet<>(alphabet), mStateFactoryForRefinement);

		final Map<IPredicate, Iterable<OutgoingInternalTransition<L, IPredicate>>> originalEdges = new HashMap<>();
		final Map<IPredicate, IPredicate> newPredicates = new HashMap<>();

		SPredicate entryNode = null;
		SPredicate exitNode = null;

		for (final IPredicate state : abstraction.getStates()) {
			final IcfgLocation programPoint = ((ISLPredicate) state).getProgramPoint();

			final SPredicate newState = mPredicateFactory.newSPredicate(programPoint, state.getFormula());

			newPredicates.put(state, newState);
			originalEdges.put(newState, abstraction.internalSuccessors(state));

			if (programPoint.equals(mIcfg.getProcedureEntryNodes().get(programPoint.getProcedure()))) {
				entryNode = newState;
			}
			if (programPoint.equals(mIcfg.getProcedureExitNodes().get(programPoint.getProcedure()))) {
				exitNode = newState;
			}

			automaton.addState(false, abstraction.isFinal(state), newState);
		}

		final Map<Summary, IPredicate> functionPreStates = new HashMap<>();

		for (final var entry : originalEdges.entrySet()) {
			final IPredicate newState = entry.getKey();
			final var transitions = entry.getValue();
			for (final var transition : transitions) {
				if (transition.getLetter() instanceof Summary) {
					functionPreStates.put((Summary) transition.getLetter(), newState);
				}

				final IPredicate newSucc = newPredicates.get(transition.getSucc());
				automaton.addInternalTransition(newState, transition.getLetter(), newSucc);
			}
		}

		final Term trueTerm = mCsToolkit.getManagedScript().getScript().term("true");

		final IPredicate newPreconditionState = mPredicateFactory
				.newSPredicate(dummyPreLocations.get(entryNode.getProgramPoint().getProcedure()), trueTerm);

		automaton.addState(true, false, newPreconditionState);
		automaton.addInternalTransition(newPreconditionState, preconditionTransition, entryNode);

		final IPredicate newPostconditionViolatedState = mPredicateFactory
				.newSPredicate(dummyPostLocations.get(exitNode.getProgramPoint().getProcedure()), trueTerm);

		automaton.addState(false, true, newPostconditionViolatedState);
		automaton.addInternalTransition(exitNode, postconditionViolatedTransition, newPostconditionViolatedState);

		for (final var entry : functionPreStates.entrySet()) {
			final Summary summary = entry.getKey();
			final IPredicate preSummaryState = entry.getValue();

			if (!functionsToAssure.contains(summary.getCallStatement().getMethodName())) {
				continue;
			}

			final IPredicate assureState = mPredicateFactory.newSPredicate(dummyAssureLocations.get(summary), trueTerm);
			automaton.addState(false, true, assureState);

			@SuppressWarnings("unchecked")
			final L assure = (L) mAssureStatements.get(summary);
			alphabet.add(assure);
			automaton.addInternalTransition(preSummaryState, assure, assureState);
		}

		return automaton;

	}

	public INestedWordAutomaton<L, IPredicate> initializeFunctionAbstraction(final String functionName,
			final L preconditionTransition, final L postconditionViolatedTransition) {
		final INestedWordAutomaton<L, IPredicate> abstraction = mFunctionAutomata.get(functionName);
		final INestedWordAutomaton<L, IPredicate> raw = mFunctionAutomataRaw.get(functionName);
		return constructFunctionAutomaton(raw, preconditionTransition, postconditionViolatedTransition,
				mFunctionsToAssure);
	}

	public INestedWordAutomaton<L, IPredicate> initializeFunctionAbstraction(final String functionName,
			final IPredicate precondition, final IPredicate postconditionViolated) {

		final UnmodifiableTransFormula preTransFormula =
				TransFormulaBuilder.constructTransFormulaFromPredicate(precondition, mCsToolkit.getManagedScript());
		final UnmodifiableTransFormula postTransFormula = TransFormulaBuilder
				.constructTransFormulaFromPredicate(postconditionViolated, mCsToolkit.getManagedScript());

		@SuppressWarnings("unchecked")
		final L preconditionTransition =
				(L) new PrePostDummyTransition(functionName, preTransFormula, precondition.toString());
		@SuppressWarnings("unchecked")
		final L postconditionViolatedTransition =
				(L) new PrePostDummyTransition(functionName, postTransFormula, postconditionViolated.toString());

		return initializeFunctionAbstraction(functionName, preconditionTransition, postconditionViolatedTransition);
	}

	protected IPredicate transformPrecondition(final Summary summary, final IPredicate predicate) {
		// final Set<TermVariable> callParams =
		// mCallParams.get(summary).stream().map(IProgramVar::getTermVariable).collect(Collectors.toSet());

		final Set<TermVariable> callParams = new HashSet<>();
		for (final IProgramVar programVariable : mCallParams.get(summary)) {
			callParams.add(programVariable.getTermVariable());
			if (programVariable instanceof ProgramNonOldVar) {
				callParams.add(((ProgramNonOldVar) programVariable).getOldVar().getTermVariable());
			}
		}

		final IPredicate predicateQuantified = quantifyPredicate(predicate, callParams);

		final Term transitionedTerm = callTransition(summary, predicateQuantified);
		return mPredicateFactory.newPredicate(transitionedTerm);

	}

	protected IPredicate transformPostcondition(final Summary summary, final IPredicate predicate,
			final IPredicate prePredicate) {
		// final Set<TermVariable> returnParams =
		// mReturnParams.get(summary).stream().map(IProgramVar::getTermVariable).collect(Collectors.toSet());

		final Set<TermVariable> returnParams = new HashSet<>();
		for (final IProgramVar programVariable : mReturnParams.get(summary)) {
			returnParams.add(programVariable.getTermVariable());
			if (programVariable instanceof ProgramNonOldVar) {
				returnParams.add(((ProgramNonOldVar) programVariable).getOldVar().getTermVariable());
			}
		}

		final IPredicate predicateQuantified = quantifyPredicate(predicate, returnParams);

		// TODO do we actually need to quantify this?
		final IPredicate prePredicateQuantified = quantifyPredicate(prePredicate, returnParams);

		final Term transitionedTerm = returnTransitionReverse(summary, predicateQuantified, prePredicateQuantified);
		return mPredicateFactory.newPredicate(transitionedTerm);
	}

	protected IPredicate quantifyPredicate(final IPredicate predicate, final Set<TermVariable> notToQuantify) {
		final Set<TermVariable> toQuantify = new HashSet<>();
		Collections.addAll(toQuantify, predicate.getFormula().getFreeVars());
		toQuantify.removeAll(notToQuantify);

		final Term quantifiedFormula = SmtUtils.quantifier(mCsToolkit.getManagedScript().getScript(),
				QuantifiedFormula.EXISTS, toQuantify, predicate.getFormula());

		return mPredicateFactory.newPredicate(quantifiedFormula);
	}

	@Deprecated
	protected IPredicate transformPredicate(final IPredicate predicate, final Set<TermVariable> params,
			final UnmodifiableTransFormula transition) {
		final Set<TermVariable> toQuantify = new HashSet<>();
		Collections.addAll(toQuantify, predicate.getFormula().getFreeVars());
		toQuantify.removeAll(params);

		final Term quantifiedFormula = SmtUtils.quantifier(mCsToolkit.getManagedScript().getScript(),
				QuantifiedFormula.EXISTS, toQuantify, predicate.getFormula());

		final BasicPredicate predicateQuantified = mPredicateFactory.newPredicate(quantifiedFormula);

		final Term predicateTransitioned =
				mPredicateTransformer.strongestPostcondition(predicateQuantified, transition);
		return mPredicateFactory.newPredicate(predicateTransitioned);
	}

	@Deprecated
	protected IPredicate extractPostcondition(final INestedWordAutomaton<L, IPredicate> abstraction) {
		final Script script = mCsToolkit.getManagedScript().getScript();
		final Set<IPredicate> states = abstraction.getStates();
		if (states.isEmpty()) {
			return mPredicateFactory.newPredicate(script.term("true"));
		}

		final String function = ((ISLPredicate) states.iterator().next()).getProgramPoint().getProcedure();

		// Check on exit node because postcondition is a dummy transition added after the exit node
		final IcfgLocation exitLocation = mIcfg.getProcedureExitNodes().get(function);
		final List<Term> exitStates = new ArrayList<>();
		for (final IPredicate state : states) {
			if (((ISLPredicate) state).getProgramPoint().equals(exitLocation)) {
				exitStates.add(state.getFormula());
			}
		}

		final Term postcondition = SmtUtils.or(script, exitStates);
		return mPredicateFactory.newPredicate(postcondition);
	}

	public INestedWordAutomaton<L, IPredicate> initializeRawAbstraction(final String functionName) {
		final INestedWordAutomaton<L, IPredicate> abstraction = mFunctionAutomataRaw.get(functionName);
		return constructSingleFunctionAutomatonRaw(abstraction,
				(ISLPredicate) abstraction.getInitialStates().iterator().next()); // copy the automaton
	}

	public Collection<Summary> getFunctionSummaries(final String functionName) {
		return mFunctionSummaries.get(functionName);
	}

	public Set<String> getFunctionsToCheck() {
		return mFunctionsToCheck;
	}

	public UnmodifiableTransFormula getCallTransition(final Summary summary) {
		return mCallTransitions.get(summary);
	}

	public UnmodifiableTransFormula getReturnTransition(final Summary summary) {
		return mReturnTransitions.get(summary);
	}

	public Term callTransition(final Summary summary, final IPredicate callPredicate) {
		final String functionName = summary.getCallStatement().getMethodName();

		final TransFormula globalVarsAssignments =
				mCsToolkit.getOldVarsAssignmentCache().getGlobalVarsAssignment(functionName);
		final TransFormula oldVarAssignments =
				mCsToolkit.getOldVarsAssignmentCache().getOldVarsAssignment(functionName);
		final Set<IProgramNonOldVar> modifiableGlobals =
				mCsToolkit.getModifiableGlobalsTable().getModifiedBoogieVars(functionName);

		final UnmodifiableTransFormula callTransition = getCallTransition(summary);

		return mPredicateTransformer.strongestPostconditionCall(callPredicate, callTransition, globalVarsAssignments,
				oldVarAssignments, modifiableGlobals);

		// return mPredicateTransformer.strongestPostcondition(callPredicate, callTransition);
	}

	public Term callTransitionReverse(final Summary summary, final IPredicate callPredicate) {
		final String functionName = summary.getCallStatement().getMethodName();

		final TransFormula globalVarsAssignments =
				mCsToolkit.getOldVarsAssignmentCache().getGlobalVarsAssignment(functionName);
		final TransFormula oldVarAssignments =
				mCsToolkit.getOldVarsAssignmentCache().getOldVarsAssignment(functionName);
		final Set<IProgramNonOldVar> modifiableGlobals =
				mCsToolkit.getModifiableGlobalsTable().getModifiedBoogieVars(functionName);

		final UnmodifiableTransFormula callTransition = getCallTransition(summary);

		return mPredicateTransformer.weakestPreconditionCall(callPredicate, callTransition, globalVarsAssignments,
				oldVarAssignments, modifiableGlobals);

		// return mPredicateTransformer.weakestPrecondition(callPredicate, callTransition);
	}

	public Term returnTransition(final Summary summary, final IPredicate returnPredicate,
			final IPredicate callPredicate) {
		final String functionName = summary.getCallStatement().getMethodName();

		final TransFormula globalVarsAssignments =
				mCsToolkit.getOldVarsAssignmentCache().getGlobalVarsAssignment(functionName);
		final TransFormula oldVarAssignments =
				mCsToolkit.getOldVarsAssignmentCache().getOldVarsAssignment(functionName);
		final Set<IProgramNonOldVar> modifiableGlobals =
				mCsToolkit.getModifiableGlobalsTable().getModifiedBoogieVars(functionName);

		final UnmodifiableTransFormula returnTransition = getReturnTransition(summary);

		return mPredicateTransformer.strongestPostconditionReturn(returnPredicate, callPredicate, returnTransition,
				globalVarsAssignments, oldVarAssignments, modifiableGlobals);

		// return mPredicateTransformer.strongestPostcondition(returnPredicate, returnTransition);
	}

	public Term returnTransitionReverse(final Summary summary, final IPredicate returnPredicate,
			final IPredicate callPredicate) {
		final String functionName = summary.getCallStatement().getMethodName();

		final TransFormula globalVarsAssignments =
				mCsToolkit.getOldVarsAssignmentCache().getGlobalVarsAssignment(functionName);
		final TransFormula oldVarAssignments =
				mCsToolkit.getOldVarsAssignmentCache().getOldVarsAssignment(functionName);
		final Set<IProgramNonOldVar> modifiableGlobals =
				mCsToolkit.getModifiableGlobalsTable().getModifiedBoogieVars(functionName);

		final UnmodifiableTransFormula returnTransition = getReturnTransition(summary);

		return mPredicateTransformer.weakestPreconditionReturn(returnPredicate, callPredicate, returnTransition,
				globalVarsAssignments, oldVarAssignments, modifiableGlobals);

		// return mPredicateTransformer.weakestPrecondition(returnPredicate, returnTransition);
	}

	public Set<IProgramVar> getCallParams(final Summary summary) {
		return mCallParams.get(summary);
	}

	public Set<IProgramVar> getReturnParams(final Summary summary) {
		return mReturnParams.get(summary);
	}

	public AssureStatement getAssureStatement(final Summary summary) {
		return mAssureStatements.get(summary);
	}

	public boolean functionHasImplementation(final String functionName) {
		return mFunctionsWithImplementation.contains(functionName);
	}

	public Map<Summary, Collection<FunctionContract>> newContractMap() {
		final Map<Summary, Collection<FunctionContract>> map = new HashMap<>();
		mFunctionSummaries.values().stream().flatMap(Collection::stream).forEach(c -> map.put(c, new HashSet<>()));
		return map;
	}

	public UnmodifiableTransFormula getPreconditionTransition(final String function) {
		return mPreconditionTransFormulas.get(function);
	}

	public UnmodifiableTransFormula getPostconditionViolatedTransition(final String function) {
		return mPostconditionViolatedTransFormulas.get(function);
	}

	public CfgSmtToolkit getCsToolkit() {
		return mCsToolkit;
	}

	public PredicateFactory getPredicateFactory() {
		return mPredicateFactory;
	}

	/**
	 * Dummy class for Precondition and Postcondition Transitions that need to be dymamically checked
	 */
	public static class PrePostDummyTransition implements IIcfgTransition<IcfgLocation>, IInternalAction {

		private static final long serialVersionUID = -295366297188547709L;

		Payload mPayload;

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
			if (hasPayload()) {
				return mPayload;
			}

			mPayload = new Payload();
			return mPayload;
		}

		@Override
		public boolean hasPayload() {
			return mPayload != null;
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

	public static class AssureStatement implements IIcfgTransition<IcfgLocation>, IInternalAction {

		private static final long serialVersionUID = -851307156749743054L;

		Payload mPayload;

		final Summary mSummary;
		final String mProcedure;
		UnmodifiableTransFormula mTransFormula;
		String mPrettyPrinted;

		public AssureStatement(final Summary summary, final UnmodifiableTransFormula transFormula) {
			mSummary = summary;
			mProcedure = summary.getPrecedingProcedure();
			setTransformula(transFormula);
		}

		@Override
		public IPayload getPayload() {
			if (hasPayload()) {
				return mPayload;
			}

			mPayload = new Payload();
			return mPayload;
		}

		@Override
		public boolean hasPayload() {
			return mPayload != null;
		}

		@Override
		public String getPrecedingProcedure() {
			return mProcedure;
		}

		@Override
		public String getSucceedingProcedure() {
			return mProcedure;
		}

		public void setTransformula(final UnmodifiableTransFormula transFormula) {
			mTransFormula = transFormula;
			mPrettyPrinted = "Assure: " + transFormula.toString();
		}

		public Summary getSummary() {
			return mSummary;
		}

		public String getAssuredProcedure() {
			return mSummary.getCallStatement().getMethodName();
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
}
