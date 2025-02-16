package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.arraytheory.SMTTheoryOperationProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ForkThreadCurrent;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ForkThreadOther;

public class RelationalInterferingPostOperator implements IAbstractPostOperator<RelationalInterferingState, IcfgEdge> {
	private String mCurrentThreadName;
	private final IDomain mSifaDomain;
	private final PredicateTransformer<Term, IPredicate, TransFormula> mPredicateHandler;
	private final RelationalInterferingStateFactoryAndPredicateHelper mStateFactory;
	private final IUltimateServiceProvider mServiceProvider;

	private final ManagedScript mScript;
	private final ILogger mLogger;

	private final PrimedTermvariableHelper mPrimedVarMap;
	private final RelationalInterferenceState mInterferences;

	public RelationalInterferingPostOperator(final IDomain sifaDomain, final String currentThreadName,
			final RelationalInterferingStateFactoryAndPredicateHelper factory, final IIcfg<?> cfg,
			final IUltimateServiceProvider serviceProvider, final RelationalInterferenceState interferences,
			final PrimedTermvariableHelper primedVarMap) {
		mLogger = serviceProvider.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mSifaDomain = sifaDomain;
		mCurrentThreadName = currentThreadName;
		mStateFactory = factory;
		mScript = cfg.getCfgSmtToolkit().getManagedScript();
		mServiceProvider = serviceProvider;
		final var opProvider = new SMTTheoryOperationProvider(mServiceProvider, cfg.getCfgSmtToolkit());
		mPredicateHandler = new PredicateTransformer<>(cfg.getCfgSmtToolkit().getManagedScript(), opProvider);
		mInterferences = interferences;
		mPrimedVarMap = primedVarMap;
	}

	@Override
	public Collection<RelationalInterferingState> apply(final RelationalInterferingState oldstate,
			final IcfgEdge transition) {
		mLogger.info("\n");
		mLogger.info("\n");
		mLogger.error("START postOperator----------------");
		mLogger.error("current Thread: " + transition.getPrecedingProcedure());
		mCurrentThreadName = transition.getPrecedingProcedure();
		final Collection<RelationalInterferingState> postStates = new HashSet<>();

		if (transition instanceof ForkThreadCurrent || transition instanceof ForkThreadOther) {
			mLogger.warn("Fork transition, no postOp, no interference created");
			return applyFork(oldstate, transition);
		}
		mLogger.warn("Applying postoperator to ");
		mLogger.warn("state: " + oldstate.toLogString());
		mLogger.warn("transitionTerm: " + transition.getTransformula().getFormula());

		// 1. normal poststate
		final Term postState =
				mPredicateHandler.strongestPostcondition(oldstate.getPredicate(), transition.getTransformula());
		var postRelationalState = mStateFactory.getOrConstructState(postState, oldstate.getVariables(),
				new ThreadInstanceCounter(oldstate.getThreadInstanceState().getThreadInstances()));
		// alpha(state) (TODO: atm doesnt alpha thread/loc info)
		postRelationalState = mStateFactory.getOrConstructState(mSifaDomain.alpha(postRelationalState.getPredicate()),
				oldstate.getVariables(), oldstate.getThreadInstanceState());
		mLogger.warn("state after: " + postRelationalState.toLogString());

		// add new interference to global map
		final var interf = createInterference(transition.getTransformula(), oldstate);
		mInterferences.addInterference(mCurrentThreadName, interf);
		mLogger.error("Interference created: " + interf.toString());

		// 2. Interferences to change postRelationalState
		final Set<String> threadNameSet = postRelationalState.getThreadInstanceState().getThreadNameSet();
		final Set<String> possibleInterferenceSet = new HashSet<>();
		final var procedureMap = postRelationalState.getThreadInstanceState().getThreadInstances();
		for (final String threadName : threadNameSet) {
			final int threadInstances = procedureMap.get(threadName);
			if (threadInstances > 3 || threadName != mCurrentThreadName && threadInstances > 0) {
				possibleInterferenceSet.add(threadName);
			}
		}
		mLogger.error("Before interferences: " + postRelationalState.getPredicate());
		postRelationalState =
				postRelationalState.union(interferenceFixpoint(possibleInterferenceSet, postRelationalState));
		mLogger.error("After interferences: " + postRelationalState.getPredicate());
		postStates.add(postRelationalState);

		mLogger.error("----------------END postOperator");
		return postStates;
	}

	private Collection<RelationalInterferingState> applyFork(final RelationalInterferingState oldstate,
			final IcfgEdge transition) {
		var newState = mStateFactory.getOrConstructState(oldstate.getPredicate(), oldstate.getVariables(),
				new ThreadInstanceCounter(oldstate.getThreadInstanceState()));
		if (transition instanceof final ForkThreadCurrent fork1) {
			newState.getThreadInstanceState().incrementThread(fork1.getNameOfForkedProcedure());
		} else if (transition instanceof final ForkThreadOther fork2) {
			newState.getThreadInstanceState().incrementThread(fork2.getSucceedingProcedure());
		}
		final Set<String> threadNameSet = newState.getThreadInstanceState().getThreadNameSet();
		final Set<String> possibleInterferenceSet = new HashSet<>();
		final var procedureMap = newState.getThreadInstanceState().getThreadInstances();
		for (final String threadName : threadNameSet) {
			final int threadInstances = procedureMap.get(threadName);
			if (threadInstances > 3 || threadName != mCurrentThreadName && threadInstances > 0) {
				possibleInterferenceSet.add(threadName);
			}
		}
		mLogger.error("Before interferences: " + newState.getPredicate());
		newState = newState.union(interferenceFixpoint(possibleInterferenceSet, newState));
		mLogger.error("After interferences: " + newState.getPredicate());
		return Collections.singleton(newState);
	}

	private RelationalInterferingState interferenceFixpoint(final Set<String> interferenceSet,
			RelationalInterferingState state) {
		boolean changed = true;
		while (changed) {
			for (final String interference : interferenceSet) {
				if (state.getInterferencesForThread(interference).isEmpty()) {
					continue;
				}
				// TODO: Make it real fixpoint computation
				RelationalInterferingState postState = mStateFactory.getBottomState();
				for (final Term interferenceTerm : state.getInterferencesForThread(interference)) {
					mLogger.error("Applying interference: " + interferenceTerm);
					postState = postState.union(mStateFactory.getOrConstructState(
							termPost(state.getTerm(mScript.getScript()), interferenceTerm), state.getVariables(),
							state.getThreadInstanceState()));

					state = state.union(postState);
				}
			}
			// changed = oldstate.isSubsetOf(fullState) != SubsetResult.NONE ? false : true;
			changed = false;
		}
		return state;
	}

	private Term termPost(final Term state, final Term interference) {
		final Set<TermVariable> freeVarsState = Set.of(state.getFreeVars());
		final Set<TermVariable> freeVarsInterf = Set.of(interference.getFreeVars());
		final Set<TermVariable> allVars = new HashSet<>(freeVarsState);
		allVars.addAll(freeVarsInterf);

		final Map<Term, Term> substitutionMapping = new HashMap<>();
		final List<TermVariable> oldVarsToQuantify = new ArrayList<>();

		// oldVar != old(var), just vars to be renamed
		for (final TermVariable oldVar : allVars) {
			final String name = oldVar.getName();
			if (!name.contains("'")) {
				// nonprimed var -> rename to doublePrimed and existentially quantify later
				final TermVariable doublePrimedTv = mPrimedVarMap.getOrConstructDoublePrimedVar(oldVar);
				substitutionMapping.put(oldVar, doublePrimedTv);
				oldVarsToQuantify.add(doublePrimedTv);
			}
		}

		final Term renamedState = Substitution.apply(mScript, substitutionMapping, state);
		final Term renamedInterf = Substitution.apply(mScript, substitutionMapping, interference);

		final Map<Term, Term> substitutionMapping2 = new HashMap<>();
		for (final TermVariable oldVar : allVars) {
			final String name = oldVar.getName();
			if (name.contains("'")) {
				// primed var -> rename to nonprimed
				substitutionMapping2.put(oldVar, mPrimedVarMap.getUnPrimed(oldVar));
			}
		}

		final Term renamedState2 = Substitution.apply(mScript, substitutionMapping2, renamedState);
		final Term renamedInterf2 = Substitution.apply(mScript, substitutionMapping2, renamedInterf);

		final Term combined = SmtUtils.and(mScript.getScript(), renamedState2, renamedInterf2);

		final Term withQuant =
				SmtUtils.quantifier(mScript.getScript(), QuantifiedFormula.EXISTS, oldVarsToQuantify, combined);

		return PartialQuantifierElimination.eliminate(mServiceProvider, mScript, withQuant,
				SimplificationTechnique.SIMPLIFY_DDA2);
	}

	private Term createInterference(final UnmodifiableTransFormula transFormula,
			final RelationalInterferingState relState) {
		// rename out/in vars to primed/unprimed
		final Map<IProgramVar, TermVariable> inVars = transFormula.getInVars();
		final Map<IProgramVar, TermVariable> outVars = transFormula.getOutVars();
		final Term transFormulaTerm = transFormula.getFormula();

		final Map<Term, Term> substitutionMapping = new HashMap<>();

		final Collection<IProgramVar> occuringVars = new ArrayList<>(inVars.keySet());
		occuringVars.addAll(outVars.keySet());

		// replacing Invars x* with Termvar x
		for (final IProgramVar var : inVars.keySet()) {
			final TermVariable oldVar = inVars.get(var);
			final TermVariable newVar = mPrimedVarMap.getOrConstructNonPrimedVar(var);
			substitutionMapping.put(oldVar, newVar);
		}

		// replacing Outvars x* with Termvar x'
		for (final IProgramVar var : outVars.keySet()) {
			final TermVariable oldVar = outVars.get(var);
			final TermVariable newVar = mPrimedVarMap.getOrConstructPrimedVar(var);
			substitutionMapping.put(oldVar, newVar);
		}

		// quantify auxvars
		final Term formula = Substitution.apply(mScript, substitutionMapping, transFormulaTerm);
		final Collection<TermVariable> auxVarsCollection = transFormula.getAuxVars();
		final Term existentialized =
				SmtUtils.quantifier(mScript.getScript(), QuantifiedFormula.EXISTS, auxVarsCollection, formula);

		// Have to collect all missing (from tranformula) vars x and put x = x' into conjunct
		final List<Term> conjuncts = new ArrayList<>();
		final var assinged = transFormula.getAssignedVars();
		for (final IProgramVarOrConst programVarOrConst : relState.getVariables()) {
			if (assinged.contains(programVarOrConst)) {
				continue;
			}
			if (programVarOrConst instanceof final IProgramVar programVar) {
				// TODO: decide if we want to have old(x)' = old(x) in our formula
				if (programVar.isOldvar()) {
					continue;
				}
				final TermVariable unprimed = mPrimedVarMap.getOrConstructNonPrimedVar(programVar);
				final TermVariable primed = mPrimedVarMap.getOrConstructPrimedVar(programVar);
				conjuncts.add(SmtUtils.binaryEquality(mScript.getScript(), primed, unprimed));
			} else if (programVarOrConst instanceof IProgramConst) {
				continue;
			} else {
				throw new IllegalArgumentException("Unexprected variable type.");
			}
		}
		conjuncts.add(existentialized);

		// add our prestate
		conjuncts.add(relState.getPredicate().getFormula());
		return SmtUtils.and(mScript.getScript(), conjuncts);
	}

	@Override
	public List<RelationalInterferingState> apply(final RelationalInterferingState stateBeforeLeaving,
			final RelationalInterferingState secondState, final IcfgEdge transition) {
		throw new UnsupportedOperationException("Not implemented.");
	}

	@Override
	public EvalResult evaluate(final RelationalInterferingState state, final Term formula, final Script script) {
		throw new UnsupportedOperationException("Not implemented.");
	}

}
