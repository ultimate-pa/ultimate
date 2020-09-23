package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import java.util.ArrayDeque;
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
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

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

	@Override
	public <STATE> Map<STATE, IPredicate> getInterpolants(final INestedWordAutomaton<LETTER, STATE> automaton,
			final Map<STATE, IPredicate> stateMap) {
		final Set<TermVariable> ipVars = stateMap.values().stream()
				.flatMap(x -> x.getVars().stream().map(IProgramVar::getTermVariable)).collect(Collectors.toSet());
		final ArrayDeque<STATE> dequeue = new ArrayDeque<>();
		final Map<STATE, Set<STATE>> unlabeledSuccessors = new HashMap<>();
		for (final STATE state : automaton.getStates()) {
			final Set<STATE> succs = new HashSet<>();
			for (final OutgoingInternalTransition<LETTER, STATE> edge : automaton.internalSuccessors(state)) {
				final STATE succ = edge.getSucc();
				if (!stateMap.containsKey(succ)) {
					succs.add(succ);
				}
			}
			if (succs.isEmpty()) {
				dequeue.add(state);
			} else {
				unlabeledSuccessors.put(state, succs);
			}
		}
		final Script script = mManagedScript.getScript();
		while (!dequeue.isEmpty()) {
			final STATE state = dequeue.pop();
			unlabeledSuccessors.remove(state);
			IPredicate predicate = stateMap.get(state);
			if (predicate == null) {
				// Add new states (with state as only unlabeled successor) to the queue
				for (final Entry<STATE, Set<STATE>> entry : unlabeledSuccessors.entrySet()) {
					final Set<STATE> succs = entry.getValue();
					if (succs.remove(state) && succs.isEmpty()) {
						dequeue.add(entry.getKey());
					}
				}
				// Calculate the conjunction of wp for all successors (if not ignored)
				final List<Term> wpConjuncts = new ArrayList<>();
				for (final OutgoingInternalTransition<LETTER, STATE> outgoing : automaton.internalSuccessors(state)) {
					final IPredicate succ = stateMap.get(outgoing.getSucc());
					if (succ != null) {
						wpConjuncts.add(mPredicateTransformer.weakestPrecondition(succ,
								outgoing.getLetter().getTransformula()));
					}
				}
				// Quantify variables not contained in the original interpolants away
				final Term wpAnd = SmtUtils.and(script, wpConjuncts);
				final Set<TermVariable> unnecessaryVars =
						Arrays.stream(wpAnd.getFreeVars()).filter(x -> !ipVars.contains(x)).collect(Collectors.toSet());
				final Term wpQuantified = SmtUtils.quantifier(script, QuantifiedFormula.FORALL, unnecessaryVars, wpAnd);
				final Term wpEliminated = PartialQuantifierElimination.tryToEliminate(mServices, mLogger,
						mManagedScript, wpQuantified, mSimplificationTechnique, mXnfConversionTechnique);
				// Ignore the interpolant, if it still contains quantifiers or stores or has no successors
				if (wpConjuncts.isEmpty() || !QuantifierUtils.isQuantifierFree(wpEliminated)
						|| SmtUtils.containsFunctionApplication(wpEliminated, "store")) {
					continue;
				}
				// Add the wp conjunction as a predicate
				predicate = mPredicateUnifier.getOrConstructPredicate(wpEliminated);
				stateMap.put(state, predicate);
			}
		}
		return stateMap;
	}
}
