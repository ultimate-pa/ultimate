package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.transformers;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.PrimedDefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Transformer that removes pre-state constraints from interferences. (Note: THis is not useful if we just get
 * non-prestate interferences directly during collection, since that would also be more performant.)
 */
public class PreStateRemovingTransformer implements IInterferenceTransformer {

	private final IUltimateServiceProvider mServices;
	private final ManagedScript mManagedScript;
	private final BasicPredicateFactory mPredicateFactory;
	private final PrimedDefaultIcfgSymbolTable mSymbolTable;

	public PreStateRemovingTransformer(final IUltimateServiceProvider services, final ManagedScript managedScript,
			final BasicPredicateFactory predicateFactory, final PrimedDefaultIcfgSymbolTable symbolTable) {
		mServices = services;
		mManagedScript = managedScript;
		mPredicateFactory = predicateFactory;
		mSymbolTable = symbolTable;
	}

	@Override
	public IPredicate transformPredicate(final IPredicate interference) {
		// Collect unprimed variables (pre-state variables) to project away
		final Set<TermVariable> unprimedVars = new HashSet<>();
		for (final IProgramVar pv : interference.getVars()) {
			if (!mSymbolTable.isPrimedVar(pv)) {
				unprimedVars.add(pv.getTermVariable());
			}
		}

		if (unprimedVars.isEmpty()) {
			// No unprimed variables, nothing to remove
			return interference;
		}

		// Existentially quantify unprimed variables and eliminate
		final Term quantified = SmtUtils.quantifier(mManagedScript.getScript(), Script.EXISTS, unprimedVars,
				interference.getFormula());
		final Term projected = PartialQuantifierElimination.eliminate(mServices, mManagedScript, quantified,
				SimplificationTechnique.SIMPLIFY_DDA);

		return mPredicateFactory.newPredicate(projected);
	}
}
