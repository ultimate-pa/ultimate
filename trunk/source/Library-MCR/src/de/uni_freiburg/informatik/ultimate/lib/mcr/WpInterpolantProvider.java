package de.uni_freiburg.informatik.ultimate.lib.mcr;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * IInterpolantProvider using weakest precondition. For every state we use the conjunction of wp for all outgoing
 * transitions.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class WpInterpolantProvider<LETTER extends IIcfgTransition<?>> extends SpWpInterpolantProvider<LETTER> {
	public WpInterpolantProvider(final IUltimateServiceProvider services, final ILogger logger,
			final ManagedScript managedScript, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique, final IPredicateUnifier predicateUnifier,
			final IHoareTripleChecker htc) {
		super(services, logger, managedScript, simplificationTechnique, xnfConversionTechnique, predicateUnifier, htc);
	}

	@Override
	protected <STATE> Term calculateTerm(final INestedWordAutomaton<LETTER, STATE> automaton, final STATE state,
			final Map<STATE, IPredicate> stateMap, final Set<TermVariable> importantVars) {
		final List<Term> conjuncts = new ArrayList<>();
		for (final var edge : automaton.internalSuccessors(state)) {
			final IPredicate succ = stateMap.get(edge.getSucc());
			if (succ != null) {
				conjuncts.add(mPredicateTransformer.weakestPrecondition(succ, edge.getLetter().getTransformula()));
			}
		}
		final var script = mManagedScript.getScript();
		final Term wp = McrUtils.abstractVariables(SmtUtils.and(script, conjuncts), importantVars,
				QuantifiedFormula.FORALL, mManagedScript, mServices);
		// Overapproximate all quantifiers and check if this is sufficient as an interpolant
		final Term wpApprox = McrUtils.replaceQuantifiers(wp, script.term("true"));
		final IPredicate predWpApprox = mPredicateUnifier.getOrConstructPredicate(wpApprox);
		for (final var edge : automaton.internalSuccessors(state)) {
			final IPredicate succ = stateMap.get(edge.getSucc());
			if (succ != null && !isValidHoareTriple(predWpApprox, edge.getLetter(), succ)) {
				// If it is not sufficient for any edge, fall back to wp
				return wp;
			}
		}
		return predWpApprox.getFormula();
	}

	@Override
	protected boolean useReversedOrder() {
		return true;
	}
}
