package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.SPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction.NwaInitialAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;

/**
 * Class for various utility functions for a given program.
 *
 * @param <L>
 */
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
	protected Map<String, INestedWordAutomaton<L, IPredicate>> mFunctionAutomata;
	protected Map<String, UnmodifiableTransFormula> mPreconditionTransFormulas;
	protected Map<String, UnmodifiableTransFormula> mPostconditionViolatedTransFormulas;

	protected Map<String, Collection<Summary>> mFunctionSummaries;
	protected Set<String> mFunctionsWithImplementation;
	protected Set<String> mFunctionsToAssure;
	protected Map<Summary, AssureStatement> mAssureStatements;

	protected Map<Call, Summary> mCallSummaries;
	protected Map<Return, Summary> mReturnSummaries;
	protected Map<Summary, Call> mCallSummariesInverse;
	protected Map<Summary, Return> mReturnSummariesInverse;

	protected Map<Summary, UnmodifiableTransFormula> mCallTransitions;
	protected Map<Summary, UnmodifiableTransFormula> mReturnTransitions;

	protected Map<Summary, Set<IProgramVar>> mCallParams;
	protected Map<Summary, Set<IProgramVar>> mReturnParams;

	protected Map<String, IcfgLocation> dummyPreLocations;
	protected Map<String, IcfgLocation> dummyPostLocations;
	protected Map<Summary, IcfgLocation> dummyAssureLocations;

	/**
	 * Constructs a new {@link ProgramUtilities} object.
	 *
	 * @param icfg
	 * @param services
	 * @param predicateFactory
	 * @param predicateTransformer
	 * @param stateFactoryForRefinement
	 * @param errorLocs
	 * @param csToolkit
	 * @param pref
	 */
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
			mCallParams.put(callTransition.getKey(), params);
		}
		for (final var returnTransition : mReturnTransitions.entrySet()) {
			final Summary summary = returnTransition.getKey();

			final Set<IProgramVar> params = new HashSet<>(returnTransition.getValue().getOutVars().keySet());
			final Set<IProgramNonOldVar> modifiableGlobalVars = mCsToolkit.getModifiableGlobalsTable()
					.getModifiedBoogieVars(summary.getCallStatement().getMethodName());

			params.addAll(modifiableGlobalVars);
			mReturnParams.put(summary, params);
		}

	}

	/**
	 * Extracts the functions that need to be assured, meaning functions that may violate an assert statement.
	 */
	protected void extractFunctionsToAssure() {
		mFunctionsToAssure = new HashSet<>();

		final Set<String> functionsWithErrorState = new HashSet<>();

		final Map<String, Collection<String>> calledFunctions = new HashMap<>();
		mFunctionAutomata.keySet().stream().forEach(f -> calledFunctions.put(f, new HashSet<>()));

		for (final var entry : mFunctionAutomata.entrySet()) {
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

	/**
	 * Extracts summaries of the program and the corresponding call and return transitions.
	 */
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

		mCallSummariesInverse =
				mCallSummaries.entrySet().stream().collect(Collectors.toMap(Entry::getValue, Entry::getKey));
		mReturnSummariesInverse =
				mReturnSummaries.entrySet().stream().collect(Collectors.toMap(Entry::getValue, Entry::getKey));

	}

	public Map<Call, Summary> getCallSummaries() {
		return mCallSummaries;
	}

	public Map<Return, Summary> getReturnSummaries() {
		return mReturnSummaries;
	}

	public Map<Summary, Call> getCallSummariesInverse() {
		return mCallSummariesInverse;
	}

	public Map<Summary, Return> getReturnSummariesInverse() {
		return mReturnSummariesInverse;
	}

	/**
	 * Gets the equalities of a transformula that contains equalities.
	 *
	 * @param equalityTransFormula
	 * @return a list of pairs of program vars
	 */
	protected static List<List<IProgramVar>> getEqualities(final UnmodifiableTransFormula equalityTransFormula) {
		final List<List<IProgramVar>> equalities = new ArrayList<>();

		final Map<TermVariable, IProgramVar> mapping = new HashMap<>();
		for (final var entry : equalityTransFormula.getInVars().entrySet()) {
			mapping.put(entry.getValue(), entry.getKey());
		}
		for (final var entry : equalityTransFormula.getOutVars().entrySet()) {
			mapping.put(entry.getValue(), entry.getKey());
		}

		final ApplicationTerm formula = (ApplicationTerm) equalityTransFormula.getFormula();
		switch (formula.getFunction().getName()) {
		case "=":
			equalities.add(Arrays.stream(formula.getFreeVars()).map(tv -> mapping.get(tv)).toList());
			break;
		case "and":
			for (final Term parameter : formula.getParameters()) {
				equalities.add(Arrays.stream(parameter.getFreeVars()).map(tv -> mapping.get(tv)).toList());
			}
			break;
		default:
		}

		return equalities;
	}

	public void initFunctionAutomata(final INestedWordAutomaton<L, IPredicate> abstraction) {
		mFunctionsToCheck = new HashSet<>();
		mFunctionAutomata = new HashMap<>();
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
			mFunctionAutomata.put(function, functionNwaRaw);

			final SingleFunctionAutomatonWrapper<L> functionNwaWrapper =
					constructSingleFunctionAutomaton(abstraction, startNode);
			mPreconditionTransFormulas.put(function, functionNwaWrapper.getPreconditionTransFormula());
			mPostconditionViolatedTransFormulas.put(function,
					functionNwaWrapper.getPostconditionViolatedTransFormula());
		}
	}

	/**
	 * Extracts the single function automatons from the given abstraction.
	 *
	 * @param abstraction
	 * @param initialState
	 * @return an {@link INestedWordAutomaton}
	 */
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

	/**
	 * Constructs a function automaton, including pre- and postcondition edges, and assure edges for the summaries of
	 * the given functions.
	 *
	 * @param abstraction
	 * @param preconditionTransition
	 * @param postconditionViolatedTransition
	 * @param functionsToAssure
	 * @return an {@link INestedWordAutomaton}
	 */
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

	/**
	 * Constructs a function automaton, including pre- and postcondition edges and required assure edges.
	 *
	 * @param functionName
	 * @param preconditionTransition
	 * @param postconditionViolatedTransition
	 * @return an {@link INestedWordAutomaton}
	 */
	public INestedWordAutomaton<L, IPredicate> initializeFunctionAbstraction(final String functionName,
			final L preconditionTransition, final L postconditionViolatedTransition) {
		final INestedWordAutomaton<L, IPredicate> abstraction = mFunctionAutomata.get(functionName);
		return constructFunctionAutomaton(abstraction, preconditionTransition, postconditionViolatedTransition,
				mFunctionsToAssure);
	}

	/**
	 * Constructs a function automaton, including pre- and postcondition edges and required assure edges. The given
	 * predicates are converted to transitions.
	 *
	 * @param functionName
	 * @param precondition
	 * @param postconditionViolated
	 * @return an {@link INestedWordAutomaton}
	 */
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

	/**
	 * Transforms the precondition predicate by applying the call transition.
	 *
	 * @param summary
	 * @param predicate
	 * @return an {@link IPredicate}
	 */
	protected IPredicate transformPrecondition(final Summary summary, final IPredicate predicate) {
		final Set<TermVariable> callParams = new HashSet<>();
		for (final IProgramVar programVariable : mCallParams.get(summary)) {
			callParams.add(programVariable.getTermVariable());
			if (programVariable instanceof ProgramNonOldVar) {
				callParams.add(((ProgramNonOldVar) programVariable).getOldVar().getTermVariable());
			}
		}

		final Term transitionedTerm = callTransition(summary, predicate);
		return mPredicateFactory.newPredicate(transitionedTerm);

	}

	/**
	 * Transforms the postcondition predicate by applying the return transition.
	 *
	 * @param summary
	 * @param predicate
	 * @param prePredicate
	 * @return an {@link IPredicate}
	 */
	protected IPredicate transformPostcondition(final Summary summary, final IPredicate predicate,
			final IPredicate prePredicate) {

		final Set<TermVariable> returnParams = new HashSet<>();
		for (final IProgramVar programVariable : mReturnParams.get(summary)) {
			returnParams.add(programVariable.getTermVariable());
			if (programVariable instanceof ProgramNonOldVar) {
				returnParams.add(((ProgramNonOldVar) programVariable).getOldVar().getTermVariable());
			}
		}

		final Term transitionedTerm = returnTransitionReverse(summary, predicate, prePredicate);

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

	public INestedWordAutomaton<L, IPredicate> constructAbstraction(final String functionName) {
		final INestedWordAutomaton<L, IPredicate> abstraction = mFunctionAutomata.get(functionName);
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

	/**
	 * Computes the call transition using {@link PredicateTransformer#strongestPostconditionCall
	 * strongestPostconditionCall}.
	 *
	 * @param summary
	 * @param callPredicate
	 * @return
	 */
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
	}

	/**
	 * Computes the reverse call transition using {@link PredicateTransformer#preCall preCall}.
	 *
	 * @param summary
	 * @param callPredicate
	 * @return
	 */
	public Term callTransitionReverse(final Summary summary, final IPredicate callPredicate) {
		final String functionName = summary.getCallStatement().getMethodName();

		final TransFormula globalVarsAssignments =
				mCsToolkit.getOldVarsAssignmentCache().getGlobalVarsAssignment(functionName);
		final TransFormula oldVarAssignments =
				mCsToolkit.getOldVarsAssignmentCache().getOldVarsAssignment(functionName);
		final Set<IProgramNonOldVar> modifiableGlobals =
				mCsToolkit.getModifiableGlobalsTable().getModifiedBoogieVars(functionName);

		final UnmodifiableTransFormula callTransition = getCallTransition(summary);

		return mPredicateTransformer.preCall(callPredicate, callTransition, globalVarsAssignments, oldVarAssignments,
				modifiableGlobals);
	}

	/**
	 * Computes the return transition using {@link PredicateTransformer#strongestPostconditionReturn
	 * strongestPostconditionReturn}.
	 *
	 * @param summary
	 * @param returnPredicate
	 * @param callPredicate
	 * @return
	 */
	public Term returnTransition(final Summary summary, final IPredicate returnPredicate,
			final IPredicate callPredicate) {
		final String functionName = summary.getCallStatement().getMethodName();

		final TransFormula oldVarAssignments =
				mCsToolkit.getOldVarsAssignmentCache().getOldVarsAssignment(functionName);
		final Set<IProgramNonOldVar> modifiableGlobals =
				mCsToolkit.getModifiableGlobalsTable().getModifiedBoogieVars(functionName);

		final UnmodifiableTransFormula callTransition = getCallTransition(summary);
		final UnmodifiableTransFormula returnTransition = getReturnTransition(summary);

		return mPredicateTransformer.strongestPostconditionReturn(returnPredicate, callPredicate, returnTransition,
				callTransition, oldVarAssignments, modifiableGlobals);
	}

	/**
	 * Computes the reverse return transition using {@link PredicateTransformer#preReturn preReturn}.
	 *
	 * @param summary
	 * @param returnPredicate
	 * @param callPredicate
	 * @return
	 */
	public Term returnTransitionReverse(final Summary summary, final IPredicate returnPredicate,
			final IPredicate callPredicate) {
		final String functionName = summary.getCallStatement().getMethodName();

		final TransFormula oldVarAssignments =
				mCsToolkit.getOldVarsAssignmentCache().getOldVarsAssignment(functionName);
		final Set<IProgramNonOldVar> modifiableGlobals =
				mCsToolkit.getModifiableGlobalsTable().getModifiedBoogieVars(functionName);

		final UnmodifiableTransFormula callTransition = getCallTransition(summary);
		final UnmodifiableTransFormula returnTransition = getReturnTransition(summary);

		return mPredicateTransformer.preReturn(returnPredicate, callPredicate, returnTransition, callTransition,
				oldVarAssignments, modifiableGlobals);
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

	public Set<String> getFunctionsWithImplementation() {
		return mFunctionsWithImplementation;
	}

	/**
	 * Returns <code>true</code> if the given function has an given implementation, else <code>false</code>
	 *
	 * @param functionName
	 * @return a boolean
	 */
	public boolean functionHasImplementation(final String functionName) {
		return mFunctionsWithImplementation.contains(functionName);
	}

	/**
	 * Constructs a new, empty contract map that contains an empty set as value for all summaries for functions that
	 * have implementations.
	 *
	 * @return a {@link Map}
	 */
	public Map<Summary, Collection<FunctionContract>> newContractMap() {
		final Map<Summary, Collection<FunctionContract>> map = new HashMap<>();
		mFunctionSummaries.values().stream().flatMap(Collection::stream)
				.filter(Summary::calledProcedureHasImplementation).forEach(s -> map.put(s, new HashSet<>()));
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

	public PredicateTransformer<Term, IPredicate, TransFormula> getPredicateTransformer() {
		return mPredicateTransformer;
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

	/**
	 * Class that represents an Assure Statement. The assure statement is used to check if an assert statement can be
	 * violated inside a function given by a summary.
	 */
	public static class AssureStatement implements IIcfgTransition<IcfgLocation>, IInternalAction {

		private static final long serialVersionUID = -851307156749743054L;

		Payload mPayload;

		final Summary mSummary;
		final String mProcedure;
		UnmodifiableTransFormula mTransFormula;
		String mPrettyPrinted;

		/**
		 * Constructs a new {@link AssureStatement}.
		 *
		 * @param summary
		 * @param transFormula
		 */
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
