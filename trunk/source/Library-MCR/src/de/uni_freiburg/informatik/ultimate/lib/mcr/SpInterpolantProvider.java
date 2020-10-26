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
 * IInterpolantProvider using strongest postcondition. For every state we use the disjunction of sp for all incoming
 * transitions.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class SpInterpolantProvider<LETTER extends IIcfgTransition<?>> extends SpWpInterpolantProvider<LETTER> {
	public SpInterpolantProvider(final IUltimateServiceProvider services, final ILogger logger,
			final ManagedScript managedScript, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique, final IPredicateUnifier predicateUnifier,
			final IHoareTripleChecker htc) {
		super(services, logger, managedScript, simplificationTechnique, xnfConversionTechnique, predicateUnifier, htc);
	}

	@Override
	protected <STATE> Term calculateTerm(final INestedWordAutomaton<LETTER, STATE> automaton, final STATE state,
			final Map<STATE, IPredicate> stateMap, final Set<TermVariable> importantVars) {
		final List<Term> disjuncts = new ArrayList<>();
		for (final var edge : automaton.internalPredecessors(state)) {
			final IPredicate pred = stateMap.get(edge.getPred());
			if (pred != null) {
				disjuncts.add(mPredicateTransformer.strongestPostcondition(pred, edge.getLetter().getTransformula()));
			}
		}
		final var script = mManagedScript.getScript();
		final Term sp = McrUtils.abstractVariables(SmtUtils.or(script, disjuncts), importantVars,
				QuantifiedFormula.EXISTS, mManagedScript, mServices);
		// Underapproximate all quantifiers and check if this is sufficient as an interpolant
		final Term spApprox = McrUtils.replaceQuantifiers(sp, script.term("false"));
		final IPredicate predSpApprox = mPredicateUnifier.getOrConstructPredicate(spApprox);
		for (final var edge : automaton.internalPredecessors(state)) {
			final IPredicate pred = stateMap.get(edge.getPred());
			if (pred != null && !isValidHoareTriple(pred, edge.getLetter(), predSpApprox)) {
				// If it is not sufficient for any edge, fall back to sp
				return sp;
			}
		}
		return predSpApprox.getFormula();
	}

	@Override
	protected boolean useReversedOrder() {
		return false;
	}
}
