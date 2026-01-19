package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class TransFormulaToPredicate {

	private final ManagedScript mManagedScript;
	private final BasicPredicateFactory mPredicateFactory;

	public TransFormulaToPredicate(final ManagedScript managedScript, final BasicPredicateFactory predicateFactory) {
		mManagedScript = managedScript;
		mPredicateFactory = predicateFactory;
	}

	public IPredicate translate(final TransFormula tf) {
		final Map<Term, Term> substitution = new HashMap<>();

		// TODO: might just translate directly to termvars instead of constants

		// Substitute inVars with default constants
		for (final Entry<IProgramVar, TermVariable> entry : tf.getInVars().entrySet()) {
			substitution.put(entry.getValue(), entry.getKey().getDefaultConstant());
		}

		// Substitute outVars with primed constants
		for (final Entry<IProgramVar, TermVariable> entry : tf.getOutVars().entrySet()) {
			substitution.put(entry.getValue(), entry.getKey().getPrimedConstant());
		}

		Term translated = Substitution.apply(mManagedScript, substitution, tf.getFormula());

		// Add equalities for unchanged variables ( inVar == outVar)
		final Script script = mManagedScript.getScript();
		final List<Term> equalities = new ArrayList<>();
		for (final Entry<IProgramVar, TermVariable> entry : tf.getInVars().entrySet()) {
			final TermVariable inVar = entry.getValue();
			final TermVariable outVar = tf.getOutVars().get(entry.getKey());
			if (inVar == outVar) {
				equalities.add(SmtUtils.binaryEquality(script, entry.getKey().getDefaultConstant(),
						entry.getKey().getPrimedConstant()));
			}
		}
		equalities.add(translated);
		translated = SmtUtils.and(script, equalities);

		return mPredicateFactory.newPredicate(translated);

	}
}
