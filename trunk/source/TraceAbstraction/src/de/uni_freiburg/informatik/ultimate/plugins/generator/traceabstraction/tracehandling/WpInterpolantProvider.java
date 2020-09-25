package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.mcr.IInterpolantProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.TermDomainOperationProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.QuantifierUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.TopologicalSorter;

/**
 * IInterpolantProvider using weakest precondition. For every state we use the conjunction of wp for all outgoing
 * transitions. For better interpolants, we abstract all variables away (using forall), that are not present in the
 * initial interpolants.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class WpInterpolantProvider<LETTER extends IIcfgTransition<?>> implements IInterpolantProvider<LETTER> {

	private final ManagedScript mManagedScript;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;
	private final IPredicateUnifier mPredicateUnifier;
	private final PredicateTransformer<Term, IPredicate, TransFormula> mPredicateTransformer;

	public WpInterpolantProvider(final IUltimateServiceProvider services, final ILogger logger,
			final ManagedScript managedScript, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique, final IPredicateUnifier predicateUnifier) {
		mManagedScript = managedScript;
		mServices = services;
		mLogger = logger;
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
		mPredicateUnifier = predicateUnifier;
		mPredicateTransformer =
				new PredicateTransformer<>(mManagedScript, new TermDomainOperationProvider(mServices, mManagedScript));
	}

	private <STATE> List<STATE> revTopSort(final INestedWordAutomaton<LETTER, STATE> automaton,
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
		return new TopologicalSorter<>(successors::get).reversedTopologicalOrdering(successors.keySet()).get();
	}

	@Override
	public <STATE> Map<STATE, IPredicate> getInterpolants(final INestedWordAutomaton<LETTER, STATE> automaton,
			final Map<STATE, IPredicate> stateMap) {
		final Set<TermVariable> ipVars = stateMap.values().stream()
				.flatMap(x -> x.getVars().stream().map(IProgramVar::getTermVariable)).collect(Collectors.toSet());
		for (final STATE state : revTopSort(automaton, stateMap)) {
			// Calculate the conjunction of wp for all successors (if not ignored)
			final List<Term> wpConjuncts = new ArrayList<>();
			for (final OutgoingInternalTransition<LETTER, STATE> edge : automaton.internalSuccessors(state)) {
				final IPredicate succ = stateMap.get(edge.getSucc());
				if (succ != null) {
					final Term wp = mPredicateTransformer.weakestPrecondition(succ, edge.getLetter().getTransformula());
					wpConjuncts.add(wp);
				}
			}
			if (wpConjuncts.isEmpty()) {
				continue;
			}
			// Quantify variables not contained in the original interpolants away
			final Term wp = SmtUtils.and(mManagedScript.getScript(), wpConjuncts);
			final Set<TermVariable> unnecessaryVars =
					Arrays.stream(wp.getFreeVars()).filter(x -> !ipVars.contains(x)).collect(Collectors.toSet());
			final Term quantified =
					SmtUtils.quantifier(mManagedScript.getScript(), QuantifiedFormula.FORALL, unnecessaryVars, wp);
			final Term term = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mManagedScript,
					quantified, mSimplificationTechnique, mXnfConversionTechnique);
			// Ignore the interpolant, if it still contains quantifiers or store
			// This is workaround to avoid "too big" interpolants
			if (!QuantifierUtils.isQuantifierFree(term) || SmtUtils.containsFunctionApplication(term, "store")) {
				continue;
			}
			// Add the wp conjunction as a predicate
			stateMap.put(state, mPredicateUnifier.getOrConstructPredicate(term));
		}
		return stateMap;
	}
}
