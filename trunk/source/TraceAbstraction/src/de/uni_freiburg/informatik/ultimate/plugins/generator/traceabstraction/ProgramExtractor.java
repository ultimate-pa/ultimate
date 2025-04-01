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
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Spec;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.StringDebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
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
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.SummaryCegarLoop.PrePostDummyTransition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.SummaryCegarLoop.SingleFunctionAutomatonWrapper;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;

public class ProgramExtractor<L extends IIcfgTransition<?>> {

	protected IIcfg<?> mIcfg;

	protected IUltimateServiceProvider mServices;
	protected PredicateFactory mPredicateFactory;
	protected PredicateTransformer<Term, IPredicate, TransFormula> mPredicateTransformer;
	protected PredicateFactoryRefinement mStateFactoryForRefinement;
	protected Set<? extends IcfgLocation> mErrorLocs;
	protected CfgSmtToolkit mCsToolkit;
	protected TAPreferences mPref;

	protected Map<String, INestedWordAutomaton<L, IPredicate>> mFunctionAutomataRaw;
	protected Map<String, INestedWordAutomaton<L, IPredicate>> mFunctionAutomata;
	protected Map<String, UnmodifiableTransFormula> mPreconditionTransFormulas;
	protected Map<String, UnmodifiableTransFormula> mPostconditionViolatedTransFormulas;

	protected Map<String, Collection<IPredicate[]>> mFunctionContracts;

	protected Map<String, Collection<Summary>> mFunctionSummaries;

	protected Map<IcfgLocation, UnmodifiableTransFormula> mCallTransitions; // TODO
	protected Map<IcfgLocation, UnmodifiableTransFormula> mCallTransitionsReverse;
	protected Map<IcfgLocation, UnmodifiableTransFormula> mReturnTransitions;
	protected Map<IcfgLocation, UnmodifiableTransFormula> mReturnTransitionsReverse;

	protected Map<IcfgLocation, Map<IProgramVar, IProgramVar>> mCallVarMappings;
	protected Map<IcfgLocation, Map<IProgramVar, IProgramVar>> mReturnVarMappings;

	protected Map<IcfgLocation, Set<IProgramVar>> mCallParams;
	protected Map<IcfgLocation, Set<IProgramVar>> mReturnParams;

	protected Map<String, IcfgLocation> dummyPreLocations;
	protected Map<String, IcfgLocation> dummyPostLocations;

	public ProgramExtractor(final IIcfg<?> icfg, final IUltimateServiceProvider services,
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
		mFunctionSummaries = new HashMap<>();
		dummyPreLocations = new HashMap<>();
		dummyPostLocations = new HashMap<>();

		for (final String function : mIcfg.getProcedureEntryNodes().keySet()) {
			mFunctionSummaries.put(function, new ArrayList<>());
			dummyPreLocations.put(function,
					new IcfgLocation(new StringDebugIdentifier(function + ":dummyPreLoc"), function));
			dummyPostLocations.put(function,
					new IcfgLocation(new StringDebugIdentifier(function + ":dummyPostLoc"), function));
		}

		initCallReturnTransitions();
		initCallReturnVarMappings();

		mCallParams = new HashMap<>();
		mReturnParams = new HashMap<>();
		for (final var callTransition : mCallTransitions.entrySet()) {
			final Set<IProgramVar> params = Collections.unmodifiableSet(callTransition.getValue().getInVars().keySet());
			mCallParams.put(callTransition.getKey(), params);
		}
		for (final var returnTransition : mReturnTransitions.entrySet()) {
			final Set<IProgramVar> params =
					Collections.unmodifiableSet(returnTransition.getValue().getOutVars().keySet());
			mReturnParams.put(returnTransition.getKey(), params);
		}

	}

	protected void initCallReturnTransitions() {
		mCallTransitions = new HashMap<>();
		mCallTransitionsReverse = new HashMap<>();
		mReturnTransitions = new HashMap<>();
		mReturnTransitionsReverse = new HashMap<>();

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
					final UnmodifiableTransFormula transFormula = edge.getTransformula();
					mCallTransitions.put(current, transFormula);

					final UnmodifiableTransFormula reversedTransFormula = reverseTransFormulaInOutVars(transFormula);
					mCallTransitionsReverse.put(current, reversedTransFormula);
				} else if (edge instanceof Return) {
					final UnmodifiableTransFormula transFormula = edge.getTransformula();
					mReturnTransitions.put(target, transFormula);

					final UnmodifiableTransFormula reversedTransFormula = reverseTransFormulaInOutVars(transFormula);
					mReturnTransitionsReverse.put(target, reversedTransFormula);
				}

				if (edge instanceof Summary) { // TODO use summary for everything
					final String functionName = ((Summary) edge).getCallStatement().getMethodName();
					final Collection<Summary> summaries = mFunctionSummaries.get(functionName);
					summaries.add((Summary) edge);
				}
				queue.add(target);
			}

		}

	}

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

		return builder.finishConstruction(mCsToolkit.getManagedScript()); // TODO aux vars
	}

	protected void initCallReturnVarMappings() {
		mCallVarMappings = extractVarMappings(mCallTransitionsReverse);
		mReturnVarMappings = extractVarMappings(mReturnTransitions);
	}

	protected static Map<IcfgLocation, Map<IProgramVar, IProgramVar>>
			extractVarMappings(final Map<IcfgLocation, UnmodifiableTransFormula> transitions) {
		final HashMap<IcfgLocation, Map<IProgramVar, IProgramVar>> mappings = new HashMap<>();
		for (final var entry : transitions.entrySet()) {
			final IcfgLocation location = entry.getKey();
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

			mappings.put(location, varMapping);
		}

		return mappings;
	}

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
		mFunctionAutomata = new HashMap<>();
		mFunctionAutomataRaw = new HashMap<>();
		mPreconditionTransFormulas = new HashMap<>();
		mPostconditionViolatedTransFormulas = new HashMap<>();

		for (final IPredicate initialState : abstraction.getInitialStates()) {
			final String function = ((ISLPredicate) initialState).getProgramPoint().getProcedure();

			final INestedWordAutomaton<L, IPredicate> functionNwaRaw =
					constructSingleFunctionAutomatonRaw(abstraction, (ISLPredicate) initialState);
			mFunctionAutomataRaw.put(function, functionNwaRaw);

			final SingleFunctionAutomatonWrapper<L> functionNwaWrapper =
					constructSingleFunctionAutomaton(abstraction, (ISLPredicate) initialState);
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

	public INestedWordAutomaton<L, IPredicate> constructSingleAutomaton(
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

	public INestedWordAutomaton<L, IPredicate> initializeFunctionAbstraction(final String functionName,
			final L preconditionTransition, final L postconditionViolatedTransition) {
		final INestedWordAutomaton<L, IPredicate> abstraction = mFunctionAutomata.get(functionName);
		return constructSingleAutomaton(abstraction, preconditionTransition, postconditionViolatedTransition);
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

	protected IPredicate transformPrecondition(final SPredicate predicate) {
		final Set<TermVariable> callParams = mCallParams.get(predicate.getProgramPoint()).stream()
				.map(IProgramVar::getTermVariable).collect(Collectors.toSet());
		final UnmodifiableTransFormula callTransition = mCallTransitions.get(predicate.getProgramPoint());
		return transformPredicate(predicate, callParams, callTransition);
	}

	protected IPredicate transformPostcondition(final SPredicate predicate) {
		final Set<TermVariable> returnParams = mReturnParams.get(predicate.getProgramPoint()).stream()
				.map(IProgramVar::getTermVariable).collect(Collectors.toSet());
		final UnmodifiableTransFormula returnTransitionReverse =
				mReturnTransitionsReverse.get(predicate.getProgramPoint());
		return transformPredicate(predicate, returnParams, returnTransitionReverse);
	}

	protected IPredicate transformPredicate(final SPredicate predicate, final Set<TermVariable> params,
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

	public Map<IProgramVar, IProgramVar> getCallVarMapping(final IcfgLocation source) {
		return mCallVarMappings.get(source);
	}

	public Map<IProgramVar, IProgramVar> getReturnVarMapping(final IcfgLocation target) {
		return mCallVarMappings.get(target);
	}

	public Collection<Summary> getFunctionSummaries(final String functionName) {
		return mFunctionSummaries.get(functionName);
	}

	public Set<String> getFunctionNames() {
		return mFunctionAutomata.keySet();
	}

	public UnmodifiableTransFormula getCallTransition(final IcfgLocation programPoint) {
		return mCallTransitions.get(programPoint);
	}

	public UnmodifiableTransFormula getCallTransitionReverse(final IcfgLocation programPoint) {
		return mCallTransitionsReverse.get(programPoint);
	}

	public UnmodifiableTransFormula getReturnTransition(final IcfgLocation programPoint) {
		return mReturnTransitions.get(programPoint);
	}

	public UnmodifiableTransFormula getReturnTransitionReverse(final IcfgLocation programPoint) {
		return mReturnTransitionsReverse.get(programPoint);
	}

}
