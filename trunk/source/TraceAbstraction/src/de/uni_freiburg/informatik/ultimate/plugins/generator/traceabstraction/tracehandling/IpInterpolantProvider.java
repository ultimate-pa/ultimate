package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.mcr.IInterpolantProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.IInterpolatingTraceCheck;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.TopologicalSorter;

/**
 * IInterpolantProvider using DAG interpolation. To apply DAG interpolation, we encode the DAG in a (linear) trace and
 * calculate interpolants for this trace.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class IpInterpolantProvider<LETTER extends IIcfgTransition<?>> implements IInterpolantProvider<LETTER> {
	private final TaCheckAndRefinementPreferences<LETTER> mPrefs;
	private final IPredicateUnifier mPredicateUnifier;
	private final PredicateFactory mPredicateFactory;
	private final AssertionOrderModulation<LETTER> mAssertionOrderModulation;
	private final TaskIdentifier mTaskIdentifier;
	private final ILogger mLogger;
	private final ManagedScript mManagedScript;
	private final IcfgEdgeFactory mEdgeFactory;
	private final IUltimateServiceProvider mServices;
	private final Class<LETTER> mTransitionClazz;
	private final IIcfgSymbolTable mSymbolTable;

	public IpInterpolantProvider(final TaCheckAndRefinementPreferences<LETTER> prefs,
			final IPredicateUnifier predicateUnifier, final AssertionOrderModulation<LETTER> assertionOrderModulation,
			final TaskIdentifier taskIdentifier, final ILogger logger, final Class<LETTER> transitionClazz) {
		mPrefs = prefs;
		mServices = prefs.getUltimateServices();
		mPredicateUnifier = predicateUnifier;
		mAssertionOrderModulation = assertionOrderModulation;
		mTaskIdentifier = taskIdentifier;
		mLogger = logger;
		final CfgSmtToolkit cfgSmtToolkit = prefs.getCfgSmtToolkit();
		mManagedScript = cfgSmtToolkit.getManagedScript();
		mSymbolTable = cfgSmtToolkit.getSymbolTable();
		mPredicateFactory = new PredicateFactory(mServices, mManagedScript, mSymbolTable);
		mEdgeFactory = cfgSmtToolkit.getIcfgEdgeFactory();
		mTransitionClazz = transitionClazz;
	}

	@Override
	public <STATE> Map<STATE, IPredicate> getInterpolants(final INestedWordAutomaton<LETTER, STATE> automaton,
			final Map<STATE, IPredicate> stateMap) {
		// Sort the DAG topologically and create aux vars for each state
		final List<STATE> topOrder = topSort(automaton, stateMap);
		if (topOrder.isEmpty()) {
			return Collections.emptyMap();
		}
		final Map<STATE, IProgramVar> variables = new HashMap<>();
		for (final STATE state : topOrder) {
			// TODO: This is only a workaround for a fresh variable name...
			final TermVariable tv =
					mManagedScript.constructFreshTermVariable("loc", SmtSortUtils.getBoolSort(mManagedScript));
			final IProgramVar var = ProgramVarUtils.constructGlobalProgramVarPair(tv.getName(),
					SmtSortUtils.getBoolSort(mManagedScript), mManagedScript, this);
			variables.put(state, var);
		}
		// Encode the DAG in a trace and get interpolants for it
		final List<LETTER> trace = encodeDag(automaton, stateMap, topOrder, variables);
		mLogger.info("Encoded the DAG in a trace of size " + trace.size());
		final IPredicateUnifier predicateUnifier =
				new NoopPredicateUnifier(mPredicateFactory, mManagedScript.getScript());
		final IInterpolatingTraceCheck<LETTER> traceCheck =
				new IpTcStrategyModulePreferences<>(mTaskIdentifier, mServices, mPrefs, new StatelessRun<>(trace),
						predicateUnifier.getTruePredicate(), predicateUnifier.getFalsePredicate(),
						mAssertionOrderModulation, predicateUnifier, mPredicateFactory, mTransitionClazz)
								.getOrConstruct();
		assert traceCheck.isCorrect() == LBool.UNSAT : "The trace is feasible";
		final IPredicate[] interpolants = traceCheck.getInterpolants();
		assert interpolants.length == topOrder.size();
		// Map the states (sorted topologically) to the corresponding interpolants
		final Map<STATE, IPredicate> result = new HashMap<>();
		final Term trueTerm = mManagedScript.getScript().term("true");
		final Term falseTerm = mManagedScript.getScript().term("false");
		final Map<Term, Term> substitution =
				variables.values().stream().collect(Collectors.toMap(x -> x.getTermVariable(), x -> falseTerm));
		for (int i = 0; i < topOrder.size(); i++) {
			final STATE state = topOrder.get(i);
			final Term var = variables.get(state).getTermVariable();
			// Substitute the current variable by true the other ones by false
			final Term term = interpolants[i].getFormula();
			substitution.put(var, trueTerm);
			final Term substituted = new Substitution(mManagedScript, substitution).transform(term);
			substitution.put(var, falseTerm);
			result.put(state, mPredicateUnifier.getOrConstructPredicate(substituted));
		}
		return result;
	}

	private <STATE> List<STATE> topSort(final INestedWordAutomaton<LETTER, STATE> automaton,
			final Map<STATE, IPredicate> stateMap) {
		final Map<STATE, Set<STATE>> successors = new HashMap<>();
		for (final STATE state : automaton.getStates()) {
			if (stateMap.containsKey(state)) {
				continue;
			}
			final Set<STATE> succs = new HashSet<>();
			for (final OutgoingInternalTransition<LETTER, STATE> edge : automaton.internalSuccessors(state)) {
				final STATE succ = edge.getSucc();
				if (!stateMap.containsKey(succ)) {
					succs.add(succ);
				}
			}
			successors.put(state, succs);
		}
		return new TopologicalSorter<>(successors::get).topologicalOrdering(successors.keySet()).get();
	}

	private <STATE> List<LETTER> encodeDag(final INestedWordAutomaton<LETTER, STATE> automaton,
			final Map<STATE, IPredicate> stateMap, final List<STATE> topOrder,
			final Map<STATE, IProgramVar> variables) {
		final List<LETTER> result = new ArrayList<>();
		final List<UnmodifiableTransFormula> initialTfs = new ArrayList<>();
		final Script script = mManagedScript.getScript();
		LETTER initialTransition = null;
		for (final STATE state : topOrder) {
			final List<UnmodifiableTransFormula> succTfs = new ArrayList<>();
			LETTER transition = null;
			final IProgramVar var = variables.get(state);
			final UnmodifiableTransFormula varIsTrue = TransFormulaBuilder
					.constructTransFormulaFromTerm(var.getTermVariable(), Collections.singleton(var), mManagedScript);
			for (final OutgoingInternalTransition<LETTER, STATE> edge : automaton.internalSuccessors(state)) {
				final STATE succ = edge.getSucc();
				final IPredicate succPredicate = stateMap.get(succ);
				transition = edge.getLetter();
				final UnmodifiableTransFormula tf = transition.getTransformula();
				UnmodifiableTransFormula afterTf;
				if (succPredicate == null) {
					// Set the successor var to true afterwards
					afterTf = assignVarToTrue(variables.get(succ));
				} else {
					// Add [!succPredicate] afterwards
					afterTf = TransFormulaBuilder.constructTransFormulaFromTerm(
							SmtUtils.not(script, succPredicate.getFormula()), succPredicate.getVars(), mManagedScript);
				}
				// Construct a new transformula with [var], executing the original tf and afterTf
				succTfs.add(sequentialComposition(Arrays.asList(varIsTrue, tf, afterTf)));
			}
			// Add [!var] as a disjunct
			succTfs.add(TransFormulaUtils.negate(varIsTrue, mManagedScript, mServices, mLogger, null, null));
			result.add(createTransition(transition, parallelComposition(succTfs)));
			// Check if any predecessor has an interpolant. If so, add [pre]; tf; var:=true to the initial edges
			for (final IncomingInternalTransition<LETTER, STATE> edge : automaton.internalPredecessors(state)) {
				final IPredicate predicate = stateMap.get(edge.getPred());
				if (predicate == null) {
					continue;
				}
				initialTransition = edge.getLetter();
				final UnmodifiableTransFormula pre =
						TransFormulaBuilder.constructTransFormulaFromPredicate(predicate, mManagedScript);
				initialTfs.add(sequentialComposition(
						Arrays.asList(pre, initialTransition.getTransformula(), assignVarToTrue(var))));
			}
		}
		// Set all cfgVariables initially to false
		final UnmodifiableTransFormula initialFalse =
				TransFormulaBuilder.constructAssignment(new ArrayList<>(variables.values()),
						Collections.nCopies(variables.size(), script.term("false")), mSymbolTable, mManagedScript);
		final UnmodifiableTransFormula initialTf =
				sequentialComposition(Arrays.asList(initialFalse, parallelComposition(initialTfs)));
		result.add(0, createTransition(initialTransition, initialTf));
		return result;
	}

	@SuppressWarnings("unchecked")
	private LETTER createTransition(final LETTER transition, final UnmodifiableTransFormula transformula) {
		return (LETTER) mEdgeFactory.createInternalTransition(transition.getSource(), transition.getTarget(),
				transition.getPayload(), transformula);
	}

	private UnmodifiableTransFormula assignVarToTrue(final IProgramVar var) {
		return TransFormulaBuilder.constructAssignment(Collections.singletonList(var),
				Collections.singletonList(mManagedScript.getScript().term("true")), mSymbolTable, mManagedScript);
	}

	private UnmodifiableTransFormula sequentialComposition(final List<UnmodifiableTransFormula> transformulas) {
		return TransFormulaUtils.sequentialComposition(mLogger, mServices, mManagedScript, false, true, false, null,
				null, transformulas);
	}

	private UnmodifiableTransFormula parallelComposition(final List<UnmodifiableTransFormula> transformulas) {
		return TransFormulaUtils.parallelComposition(mLogger, mServices, transformulas.hashCode(), mManagedScript, null,
				false, null, transformulas.toArray(new UnmodifiableTransFormula[transformulas.size()]));
	}
}

class StatelessRun<LETTER, STATE> implements IRun<LETTER, STATE> {
	private final Word<LETTER> mWord;

	@SuppressWarnings("unchecked")
	public StatelessRun(final List<LETTER> list) {
		final LETTER[] array = (LETTER[]) list.toArray(new Object[list.size()]);
		mWord = new Word<>(array);
	}

	@Override
	public Word<LETTER> getWord() {
		return mWord;
	}

	@Override
	public LETTER getSymbol(final int position) {
		return mWord.getSymbol(position);
	}

	@Override
	public int getLength() {
		return mWord.length();
	}

	@Override
	public List<STATE> getStateSequence() {
		throw new UnsupportedOperationException(getClass().getName() + " cannot provide a state sequence");
	}
}
