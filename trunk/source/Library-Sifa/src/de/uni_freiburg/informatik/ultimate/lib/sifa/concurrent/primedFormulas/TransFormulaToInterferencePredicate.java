package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas;

import java.util.HashMap;
import java.util.HashSet;
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

public class TransFormulaToInterferencePredicate {

	private final IUltimateServiceProvider mServices;
	private final ManagedScript mManagedScript;
	private final BasicPredicateFactory mPredicateFactory;
	private final PrimedDefaultIcfgSymbolTable mSymbolTable;

	public TransFormulaToInterferencePredicate(final IUltimateServiceProvider services,
			final ManagedScript managedScript, final BasicPredicateFactory predicateFactory,
			final PrimedDefaultIcfgSymbolTable symbolTable) {
		mServices = services;
		mManagedScript = managedScript;
		mPredicateFactory = predicateFactory;
		mSymbolTable = symbolTable;
	}

	public IPredicate translate(final TransFormula tf) {
		final Set<TermVariable> localVars = new HashSet<>();
		final Map<Term, Term> substitution = buildSubstitution(tf, localVars);

		Term formula = applySubstitution(tf.getFormula(), substitution);
		formula = projectAwayLocals(formula, localVars);
		return mPredicateFactory.newPredicate(formula);
	}

	private Map<Term, Term> buildSubstitution(final TransFormula tf, final Set<TermVariable> localVars) {
		final Map<Term, Term> substitution = new HashMap<>();
		addInVarSubstitutions(tf, substitution, localVars);
		addOutVarSubstitutions(tf, substitution, localVars);
		return substitution;
	}

	private static void addInVarSubstitutions(final TransFormula tf, final Map<Term, Term> substitution,
			final Set<TermVariable> localVars) {
		for (final Entry<IProgramVar, TermVariable> entry : tf.getInVars().entrySet()) {
			final IProgramVar pv = entry.getKey();
			if (pv.isGlobal()) {
				substitution.put(entry.getValue(), pv.getTermVariable());
			} else {
				localVars.add(entry.getValue());
			}
		}
	}

	private void addOutVarSubstitutions(final TransFormula tf, final Map<Term, Term> substitution,
			final Set<TermVariable> localVars) {
		for (final Entry<IProgramVar, TermVariable> entry : tf.getOutVars().entrySet()) {
			final IProgramVar pv = entry.getKey();
			if (pv.isGlobal()) {
				substitution.put(entry.getValue(), mSymbolTable.getPrimedVar(pv));
			} else {
				localVars.add(entry.getValue());
			}
		}
	}

	private Term applySubstitution(final Term formula, final Map<Term, Term> substitution) {
		return Substitution.apply(mManagedScript, substitution, formula);
	}

	private Term projectAwayLocals(final Term formula, final Set<TermVariable> localVars) {
		return RelationalPredicateUtils.existentiallyProject(formula, localVars, mServices, mManagedScript);
	}

	public PrimedDefaultIcfgSymbolTable getSymbolTable() {
		return mSymbolTable;
	}
}
