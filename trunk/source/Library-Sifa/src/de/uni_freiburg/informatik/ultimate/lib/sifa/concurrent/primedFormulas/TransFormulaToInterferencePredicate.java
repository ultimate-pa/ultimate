package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ThreadModularSifaSettings;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ghostvariables.GhostVariableManager;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class TransFormulaToInterferencePredicate {

	private final IUltimateServiceProvider mServices;
	private final ManagedScript mManagedScript;
	private final BasicPredicateFactory mPredicateFactory;
	private final PrimedDefaultIcfgSymbolTable mSymbolTable;
	private final ThreadModularSifaSettings mSettings;
	private final GhostVariableManager mGhostVariables;

	public TransFormulaToInterferencePredicate(final IUltimateServiceProvider services,
			final ManagedScript managedScript, final BasicPredicateFactory predicateFactory,
			final PrimedDefaultIcfgSymbolTable symbolTable, final ThreadModularSifaSettings settings,
			final GhostVariableManager ghostVariables) {
		mServices = services;
		mManagedScript = managedScript;
		mPredicateFactory = predicateFactory;
		mSymbolTable = symbolTable;
		mSettings = settings;
		mGhostVariables = ghostVariables;
	}

	public IPredicate translateForInterference(final TransFormula tf, final String interferingThread,
			final IcfgLocation sourceLocation, final IcfgLocation targetLocation) {
		final Term baseTerm = translateBase(tf);

		final var script = mManagedScript.getScript();
		Term combined = baseTerm;

		// Identity constraints for unchanged globals (always, not just for ghost mode)
		final Term unchanged = createIdentityConstraintsForUnchangedGlobals(tf, interferingThread);
		combined = SmtUtils.and(script, combined, unchanged);

		if (mSettings.useGhostLocations()) {
			// loc_interferingThread = alpha(sourceLocation)
			combined = SmtUtils.and(script, combined,
					mGhostVariables.createLocationConstraint(interferingThread, sourceLocation));
			// loc_interferingThread' = alpha(targetLocation)
			combined = SmtUtils.and(script, combined,
					mGhostVariables.createPrimedLocationConstraint(interferingThread, targetLocation, mSymbolTable));
			// loc_other' = loc_other is already covered by identity constraints above
		}

		return mPredicateFactory.newPredicate(combined);
	}

	/** Renames globals to unprimed/primed TermVariables and projects away locals. */
	private Term translateBase(final TransFormula tf) {
		final Set<TermVariable> localVars = new HashSet<>();
		final Map<Term, Term> substitution = buildSubstitution(tf, localVars);

		Term formula = applySubstitution(tf.getFormula(), substitution);
		formula = projectAwayLocals(formula, localVars);
		return formula;
	}

	private Term createIdentityConstraintsForUnchangedGlobals(final TransFormula tf, final String interferingThread) {
		final var script = mManagedScript.getScript();
		final Set<IProgramVar> modified = tf.getOutVars().keySet();
		final TermVariable interferingLoc = mSettings.useGhostLocations()
				? mGhostVariables.getLocationTermVar(interferingThread) : null;

		final List<Term> conjuncts = new ArrayList<>();
		for (final IProgramVar pv : mSymbolTable.getAllGlobalBaseVars()) {
			if (modified.contains(pv)) {
				continue;
			}
			if (interferingLoc != null && pv.getTermVariable().equals(interferingLoc)) {
				// this thread's location is updated explicitly via ghost constraints
				continue;
			}
			final TermVariable primed = mSymbolTable.getPrimedVar(pv);
			if (primed == null) {
				continue;
			}
			conjuncts.add(SmtUtils.binaryEquality(script, primed, pv.getTermVariable()));
		}
		return SmtUtils.and(script, conjuncts);
	}

	private Map<Term, Term> buildSubstitution(final TransFormula tf, final Set<TermVariable> localVars) {
		final Map<Term, Term> substitution = new HashMap<>();
		addInVarSubstitutions(tf, substitution, localVars);
		addOutVarSubstitutions(tf, substitution, localVars);
		return substitution;
	}

	// Globals: inVar -> unprimed TermVariable (pre-state value)
	// Locals: collected for existential projection
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

	// Globals: outVar -> primed TermVariable (post-state value)
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
