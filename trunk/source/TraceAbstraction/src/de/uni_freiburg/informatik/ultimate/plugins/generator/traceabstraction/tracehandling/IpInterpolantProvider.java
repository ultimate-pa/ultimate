package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.mcr.IInterpolantProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SubstitutionWithLocalSimplification;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.MultiElementCounter;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.TopologicalSorter;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * IInterpolantProvider using DAG interpolation. To apply DAG interpolation, we create out own SSA based on the states.
 * For every state we use the disjunction of incoming edges as SSA term.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class IpInterpolantProvider<LETTER extends IIcfgTransition<?>> implements IInterpolantProvider<LETTER> {
	private final IPredicateUnifier mPredicateUnifier;
	private final ILogger mLogger;
	private final ManagedScript mManagedScript;
	private final IUltimateServiceProvider mServices;
	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;
	private final MultiElementCounter<IProgramVar> mConstVarCounter;

	public IpInterpolantProvider(final IUltimateServiceProvider services, final ILogger logger,
			final ManagedScript managedScript, final IPredicateUnifier predicateUnifier,
			final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique) {
		mServices = services;
		mPredicateUnifier = predicateUnifier;
		mLogger = logger;
		// TODO: Use another managedScript?
		mManagedScript = managedScript;
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
		mConstVarCounter = new MultiElementCounter<>();
	}

	@Override
	public <STATE> void addInterpolants(final INestedWordAutomaton<LETTER, STATE> automaton,
			final Map<STATE, IPredicate> states2Predicates) {
		final List<STATE> topOrder = topSort(automaton, states2Predicates);
		final Map<IProgramVar, Term> initialVarMapping = new HashMap<>();
		final Map<IProgramVar, Term> finalVarMapping = new HashMap<>();
		final Map<STATE, Map<IProgramVar, Term>> stateVarMappings = new HashMap<>(topOrder.size());
		final List<Term> ssa = new ArrayList<>(topOrder.size() + 1);
		final List<List<Triple<STATE, UnmodifiableTransFormula, STATE>>> transitions =
				extractTransitions(automaton, states2Predicates);
		final Set<IProgramVar> vars =
				states2Predicates.values().stream().flatMap(x -> x.getVars().stream()).collect(Collectors.toSet());
		// TODO: Can we put "parallel" states together to reduce the length of the ssa?
		for (final List<Triple<STATE, UnmodifiableTransFormula, STATE>> t : transitions) {
			final List<Term> disjuncts = new ArrayList<>();
			for (final Triple<STATE, UnmodifiableTransFormula, STATE> triple : t) {
				UnmodifiableTransFormula tf = triple.getSecond();
				final STATE pred = triple.getFirst();
				final IPredicate prevPred = states2Predicates.get(pred);
				final Map<IProgramVar, Term> inVarMapping;
				if (prevPred != null) {
					inVarMapping = initialVarMapping;
					tf = addCondition(tf, prevPred, true);
				} else {
					inVarMapping = stateVarMappings.get(pred);
				}
				final STATE succ = triple.getThird();
				final IPredicate succPred = states2Predicates.get(succ);
				Map<IProgramVar, Term> outVarMapping;
				if (succPred != null) {
					outVarMapping = finalVarMapping;
					tf = addCondition(tf, succPred, false);
				} else {
					outVarMapping = stateVarMappings.get(succ);
					if (outVarMapping == null) {
						outVarMapping = new HashMap<>();
						stateVarMappings.put(succ, outVarMapping);
					}
				}
				disjuncts.add(substituteTransformula(tf, inVarMapping, outVarMapping, vars));
			}
			ssa.add(SmtUtils.or(mManagedScript.getScript(), disjuncts));
		}
		final ScopedHashMap<Term, Term> mapping = new ScopedHashMap<>();
		stateVarMappings.values().forEach(
				x -> x.forEach((k, v) -> mapping.put(v, mManagedScript.constructFreshCopy(k.getTermVariable()))));
		mLogger.info("Calculating interpolants for SSA");
		final Term[] craigInterpolants = getInterpolantsForSsa(ssa);
		mLogger.info("Finished");
		for (int i = 0; i < craigInterpolants.length; i++) {
			final STATE state = topOrder.get(i);
			mapping.beginScope();
			stateVarMappings.get(state).forEach((x, y) -> mapping.put(y, x.getTermVariable()));
			final Term newTerm = renameAndAbstract(craigInterpolants[i], mapping, vars);
			states2Predicates.put(state, mPredicateUnifier.getOrConstructPredicate(newTerm));
			mapping.endScope();
		}
	}

	private UnmodifiableTransFormula addCondition(final UnmodifiableTransFormula tf, final IPredicate pred,
			final boolean precondition) {
		final Term term =
				precondition ? pred.getFormula() : SmtUtils.not(mManagedScript.getScript(), pred.getFormula());
		final UnmodifiableTransFormula assume =
				TransFormulaBuilder.constructTransFormulaFromTerm(term, pred.getVars(), mManagedScript);
		final List<UnmodifiableTransFormula> tfs = precondition ? Arrays.asList(assume, tf) : Arrays.asList(tf, assume);
		return TransFormulaUtils.sequentialComposition(mLogger, mServices, mManagedScript, false, true, false,
				mXnfConversionTechnique, mSimplificationTechnique, tfs);
	}

	private <STATE> List<List<Triple<STATE, UnmodifiableTransFormula, STATE>>> extractTransitions(
			final INestedWordAutomaton<LETTER, STATE> automaton, final Map<STATE, IPredicate> stateMap) {
		final List<STATE> topOrder = topSort(automaton, stateMap);
		final List<List<Triple<STATE, UnmodifiableTransFormula, STATE>>> result = new ArrayList<>(topOrder.size() + 1);
		final List<Triple<STATE, UnmodifiableTransFormula, STATE>> finalTransitions = new ArrayList<>();
		for (final STATE state : topOrder) {
			final List<Triple<STATE, UnmodifiableTransFormula, STATE>> currentTransitions = new ArrayList<>();
			for (final IncomingInternalTransition<LETTER, STATE> edge : automaton.internalPredecessors(state)) {
				currentTransitions.add(new Triple<>(edge.getPred(), edge.getLetter().getTransformula(), state));
			}
			result.add(currentTransitions);
			for (final OutgoingInternalTransition<LETTER, STATE> edge : automaton.internalSuccessors(state)) {
				final STATE succ = edge.getSucc();
				if (stateMap.containsKey(succ)) {
					finalTransitions.add(new Triple<>(state, edge.getLetter().getTransformula(), succ));
				}
			}
		}
		result.add(finalTransitions);
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

	private Term substituteTransformula(final TransFormula tf, final Map<IProgramVar, Term> inVarMapping,
			final Map<IProgramVar, Term> outVarMapping, final Set<IProgramVar> vars) {
		final Map<Term, Term> mapping = new HashMap<>();
		final List<Term> conjuncts = new ArrayList<>();
		final Script script = mManagedScript.getScript();
		for (final Entry<IProgramVar, TermVariable> entry : tf.getInVars().entrySet()) {
			final IProgramVar var = entry.getKey();
			if (vars.contains(var)) {
				mapping.put(entry.getValue(), getOrConstructConstant(var, inVarMapping));
			}
		}
		for (final Entry<IProgramVar, TermVariable> entry : tf.getOutVars().entrySet()) {
			final IProgramVar var = entry.getKey();
			if (vars.contains(var)) {
				mapping.put(entry.getValue(), getOrConstructConstant(var, outVarMapping));
			}
		}
		for (final IProgramVar var : vars) {
			if (!tf.getAssignedVars().contains(var)) {
				final Term inTerm = getOrConstructConstant(var, inVarMapping);
				final Term outTerm = getOrConstructConstant(var, outVarMapping);
				// TODO: If all predecessors have the same var, this can be avoided (and the same used again instead)
				conjuncts.add(SmtUtils.binaryEquality(script, outTerm, inTerm));
			}
		}
		conjuncts.add(renameAndAbstract(tf.getFormula(), mapping, vars));
		return SmtUtils.and(script, conjuncts);
	}

	private Term getOrConstructConstant(final IProgramVar var, final Map<IProgramVar, Term> mapping) {
		Term result = mapping.get(var);
		if (result == null) {
			final String basename = SmtUtils.removeSmtQuoteCharacters(var.getGloballyUniqueId());
			final String name = "c_" + basename + "_" + mConstVarCounter.increment(var);
			mManagedScript.getScript().declareFun(name, new Sort[0], var.getSort());
			result = mManagedScript.getScript().term(name);
			mapping.put(var, result);
		}
		return result;
	}

	private Term renameAndAbstract(final Term term, final Map<Term, Term> mapping, final Set<IProgramVar> varsToKeep) {
		final Term substituted = new SubstitutionWithLocalSimplification(mManagedScript, mapping).transform(term);
		final Set<TermVariable> nonQuantifiedVars =
				varsToKeep.stream().map(IProgramVar::getTermVariable).collect(Collectors.toSet());
		final List<TermVariable> quantifiedVars = Arrays.stream(substituted.getFreeVars())
				.filter(x -> !nonQuantifiedVars.contains(x)).collect(Collectors.toList());
		final Term quantified =
				SmtUtils.quantifier(mManagedScript.getScript(), QuantifiedFormula.EXISTS, quantifiedVars, substituted);
		return PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mManagedScript, quantified,
				mSimplificationTechnique, mXnfConversionTechnique);
	}

	private Term[] getInterpolantsForSsa(final List<Term> ssa) {
		int i = 0;
		final Script script = mManagedScript.getScript();
		final Term[] partition = new Term[ssa.size()];
		mManagedScript.lock(this);
		mManagedScript.push(this, 1);
		for (final Term t : ssa) {
			final String name = "ssa_" + i;
			mManagedScript.assertTerm(this, script.annotate(t, new Annotation(":named", name)));
			partition[i++] = script.term(name);
		}
		if (mManagedScript.checkSat(this) != LBool.UNSAT) {
			throw new AssertionError("The SSA of the DAG is satisfiable!");
		}
		final Term[] result = mManagedScript.getInterpolants(this, partition);
		mManagedScript.pop(this, 1);
		mManagedScript.unlock(this);
		return result;
	}
}
