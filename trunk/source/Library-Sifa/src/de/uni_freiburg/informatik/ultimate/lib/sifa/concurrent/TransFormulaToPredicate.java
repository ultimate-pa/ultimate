package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Translates {@link TransFormula}s to relational predicates using canonical term variables from a
 * {@link PrimedDefaultIcfgSymbolTable}.
 */
public class TransFormulaToPredicate {

	private final IUltimateServiceProvider mServices;
	private final ManagedScript mManagedScript;
	private final BasicPredicateFactory mPredicateFactory;
	private final PrimedDefaultIcfgSymbolTable mSymbolTable;

	public TransFormulaToPredicate(final IUltimateServiceProvider services, final ManagedScript managedScript,
			final BasicPredicateFactory predicateFactory, final PrimedDefaultIcfgSymbolTable symbolTable) {
		mServices = services;
		mManagedScript = managedScript;
		mPredicateFactory = predicateFactory;
		mSymbolTable = symbolTable;
	}

	/**
	 * Translates a TransFormula to a relational predicate. Uses unprimed term variables for pre-state (inVars) and
	 * primed term variables for post-state (outVars).
	 */
	public IPredicate translate(final TransFormula tf) {
		final Map<Term, Term> substitution = new HashMap<>();
		final List<IProgramVar> unchangedVars = new ArrayList<>();

		for (final Entry<IProgramVar, TermVariable> entry : tf.getInVars().entrySet()) {
			substitution.put(entry.getValue(), entry.getKey().getTermVariable());
		}

		for (final Entry<IProgramVar, TermVariable> entry : tf.getOutVars().entrySet()) {
			final IProgramVar pv = entry.getKey();
			substitution.put(entry.getValue(), mSymbolTable.getPrimedVar(pv));
			if (entry.getValue() == tf.getInVars().get(pv)) {
				unchangedVars.add(pv);
			}
		}

		Term formula = Substitution.apply(mManagedScript, substitution, tf.getFormula());
		formula = addIdentityConstraints(formula, unchangedVars);
		return mPredicateFactory.newPredicate(formula);
	}

	/**
	 * Translates a TransFormula directly to a global relational predicate. Local variables are existentially quantified
	 * away, making the result suitable for use as an interference relation across threads.
	 */
	public IPredicate translateToGlobal(final TransFormula tf) {
		final Map<Term, Term> substitution = new HashMap<>();
		final Set<TermVariable> localVars = new HashSet<>();
		final List<IProgramVar> unchangedGlobals = new ArrayList<>();

		for (final Entry<IProgramVar, TermVariable> entry : tf.getInVars().entrySet()) {
			final IProgramVar pv = entry.getKey();
			if (pv.isGlobal()) {
				substitution.put(entry.getValue(), pv.getTermVariable());
			} else {
				localVars.add(entry.getValue());
			}
		}

		for (final Entry<IProgramVar, TermVariable> entry : tf.getOutVars().entrySet()) {
			final IProgramVar pv = entry.getKey();
			if (pv.isGlobal()) {
				substitution.put(entry.getValue(), mSymbolTable.getPrimedVar(pv));
				if (entry.getValue() == tf.getInVars().get(pv)) {
					unchangedGlobals.add(pv);
				}
			} else {
				localVars.add(entry.getValue());
			}
		}

		Term formula = Substitution.apply(mManagedScript, substitution, tf.getFormula());
		formula = addIdentityConstraints(formula, unchangedGlobals);
		formula = RelationalPredicateUtils.existentiallyProject(formula, localVars, mServices, mManagedScript, true);
		return mPredicateFactory.newPredicate(formula);
	}

	public PrimedDefaultIcfgSymbolTable getSymbolTable() {
		return mSymbolTable;
	}

	private Term addIdentityConstraints(final Term formula, final List<IProgramVar> unchangedVars) {
		final List<Term> identities = RelationalPredicateUtils.buildIdentityConstraints(unchangedVars, mSymbolTable,
				mManagedScript.getScript());
		return RelationalPredicateUtils.conjoinWithIdentities(formula, identities, mManagedScript.getScript());
	}
}
