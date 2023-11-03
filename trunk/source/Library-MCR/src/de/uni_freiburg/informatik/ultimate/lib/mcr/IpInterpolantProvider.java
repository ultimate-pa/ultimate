package de.uni_freiburg.informatik.ultimate.lib.mcr;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.MultiElementCounter;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;

/**
 * IInterpolantProvider using DAG interpolation. To apply DAG interpolation, we create out own SSA based on the states.
 * For every state we use the disjunction of incoming edges as SSA term.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
// TODO: Current approach has bad performance. Other approach?
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
		final List<List<STATE>> topOrder = getTopologicalHierachicalSort(automaton, states2Predicates);
		final Map<IProgramVar, Term> initialVarMapping = new HashMap<>();
		final Map<IProgramVar, Term> finalVarMapping = new HashMap<>();
		final Map<STATE, Map<IProgramVar, Term>> stateVarMappings =
				topOrder.stream().flatMap(List::stream).collect(Collectors.toMap(x -> x, x -> new HashMap<>()));
		final List<Term> ssa = new ArrayList<>(topOrder.size() + 1);
		final Set<IProgramVar> vars =
				states2Predicates.values().stream().flatMap(x -> x.getVars().stream()).collect(Collectors.toSet());
		final Script script = mManagedScript.getScript();
		final List<TransFormula> finalTransformulas = new ArrayList<>();
		final List<Map<IProgramVar, Term>> finalInVarMappings = new ArrayList<>();
		for (final List<STATE> states : topOrder) {
			final List<Term> conjuncts = new ArrayList<>();
			for (final STATE state : states) {
				final List<TransFormula> transformulas = new ArrayList<>();
				final List<Map<IProgramVar, Term>> inVarMappings = new ArrayList<>();
				final Map<IProgramVar, Term> currentMapping = stateVarMappings.get(state);
				for (final IncomingInternalTransition<LETTER, STATE> edge : automaton.internalPredecessors(state)) {
					final STATE pred = edge.getPred();
					final IPredicate predPredicate = states2Predicates.get(pred);
					final UnmodifiableTransFormula tf = edge.getLetter().getTransformula();
					if (predPredicate == null) {
						transformulas.add(tf);
						inVarMappings.add(stateVarMappings.get(pred));
					} else {
						transformulas.add(addCondition(tf, predPredicate, true));
						inVarMappings.add(initialVarMapping);
					}
				}
				conjuncts.add(substituteTransformulas(transformulas, inVarMappings, currentMapping, vars));
				for (final OutgoingInternalTransition<LETTER, STATE> edge : automaton.internalSuccessors(state)) {
					final IPredicate predicate = states2Predicates.get(edge.getSucc());
					if (predicate == null) {
						continue;
					}
					finalTransformulas.add(addCondition(edge.getLetter().getTransformula(), predicate, false));
					finalInVarMappings.add(currentMapping);
				}
			}
			ssa.add(SmtUtils.and(script, conjuncts));
		}
		ssa.add(substituteTransformulas(finalTransformulas, finalInVarMappings, finalVarMapping, vars));
		mLogger.info("Calculating interpolants for SSA");
		final Term[] craigInterpolants = getInterpolantsForSsa(ssa);
		mLogger.info("Finished");
		final ScopedHashMap<Term, Term> mapping = new ScopedHashMap<>();
		stateVarMappings.values().forEach(
				x -> x.forEach((k, v) -> mapping.put(v, mManagedScript.constructFreshCopy(k.getTermVariable()))));
		final Set<TermVariable> tvs = McrUtils.getTermVariables(vars);
		for (int i = 0; i < craigInterpolants.length; i++) {
			for (final STATE state : topOrder.get(i)) {
				mapping.beginScope();
				stateVarMappings.get(state).forEach((k, v) -> mapping.put(v, k.getTermVariable()));
				final Term newTerm = renameAndAbstract(craigInterpolants[i], mapping, tvs);
				states2Predicates.put(state, mPredicateUnifier.getOrConstructPredicate(newTerm));
				mapping.endScope();
			}
		}
	}

	private <STATE> List<List<STATE>> getTopologicalHierachicalSort(final INestedWordAutomaton<LETTER, STATE> automaton,
			final Map<STATE, IPredicate> states2Predicates) {
		final List<List<STATE>> result = new ArrayList<>();
		List<STATE> currentStates = new ArrayList<>();
		final Map<STATE, Set<STATE>> predecessors = new HashMap<>();
		for (final STATE state : automaton.getStates()) {
			if (states2Predicates.containsKey(state)) {
				continue;
			}
			final Set<STATE> preds = new HashSet<>();
			for (final IncomingInternalTransition<LETTER, STATE> edge : automaton.internalPredecessors(state)) {
				final STATE pred = edge.getPred();
				if (!states2Predicates.containsKey(pred)) {
					preds.add(pred);
				}
			}
			if (preds.isEmpty()) {
				currentStates.add(state);
			} else {
				predecessors.put(state, preds);
			}
		}
		while (!currentStates.isEmpty()) {
			final List<STATE> newStates = new ArrayList<>();
			result.add(currentStates);
			for (final STATE state : currentStates) {
				predecessors.remove(state);
				for (final OutgoingInternalTransition<LETTER, STATE> edge : automaton.internalSuccessors(state)) {
					final Set<STATE> succs = predecessors.get(edge.getSucc());
					if (succs != null && succs.remove(state) && succs.isEmpty()) {
						newStates.add(edge.getSucc());
					}
				}
			}
			currentStates = newStates;
		}
		return result;
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

	private Term substituteTransformulas(final List<TransFormula> tfs, final List<Map<IProgramVar, Term>> inVarMappings,
			final Map<IProgramVar, Term> outVarMapping, final Set<IProgramVar> vars) {
		// Calculate all unassigned variables, where the in vars are equal for all transformulas
		final Set<IProgramVar> assignedVars =
				tfs.stream().flatMap(x -> x.getAssignedVars().stream()).collect(Collectors.toSet());
		final Set<IProgramVar> equalVars = new HashSet<>();
		for (final IProgramVar var : vars) {
			if (!assignedVars.contains(var)
					&& inVarMappings.stream().map(x -> x.get(var)).distinct().limit(2).count() < 2) {
				equalVars.add(var);
			}
		}
		final List<Term> disjuncts = new ArrayList<>(tfs.size());
		final Script script = mManagedScript.getScript();
		for (int i = 0; i < tfs.size(); i++) {
			final Map<Term, Term> mapping = new HashMap<>();
			final List<Term> conjuncts = new ArrayList<>();
			final TransFormula tf = tfs.get(i);
			final Map<IProgramVar, Term> inVarMapping = inVarMappings.get(i);
			for (final IProgramVar var : vars) {
				final Term inTerm = getOrConstructConstant(var, inVarMapping);
				final Term outTerm;
				if (equalVars.contains(var)) {
					// If var is mapped to the same term for all predecessors, we can just use inTerm as outTerm
					outTerm = inTerm;
					outVarMapping.put(var, outTerm);
				} else {
					// Otherwise use a fresh constant as outTerm (and add an equality if not assigned)
					outTerm = getOrConstructConstant(var, outVarMapping);
					if (!tf.getAssignedVars().contains(var)) {
						conjuncts.add(SmtUtils.binaryEquality(script, outTerm, inTerm));
					}
				}
				final Term inVar = tf.getInVars().get(var);
				if (inVar != null) {
					mapping.put(inVar, inTerm);
				}
				final Term outVar = tf.getOutVars().get(var);
				if (outVar != null) {
					mapping.put(outVar, outTerm);
				}
			}
			conjuncts.add(renameAndAbstract(tf.getFormula(), mapping, Collections.emptySet()));
			disjuncts.add(SmtUtils.and(script, conjuncts));
		}
		return SmtUtils.or(script, disjuncts);
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

	private Term renameAndAbstract(final Term term, final Map<Term, Term> mapping, final Set<TermVariable> varsToKeep) {
		final Term substituted = Substitution.apply(mManagedScript, mapping, term);
		final Term abstracted = McrUtils.abstractVariables(substituted, varsToKeep, QuantifiedFormula.EXISTS,
				mManagedScript, mServices, mLogger, mSimplificationTechnique, mXnfConversionTechnique);
		return PartialQuantifierElimination.eliminateCompat(mServices, mManagedScript, mSimplificationTechnique, abstracted);
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
