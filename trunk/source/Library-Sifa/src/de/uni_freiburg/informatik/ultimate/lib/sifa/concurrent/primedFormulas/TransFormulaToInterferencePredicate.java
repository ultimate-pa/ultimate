package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ghostvariables.GhostVariableManager;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.ThreadModularSifaSettings.QuantifierEliminationMode;
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
	private final GhostVariableManager mGhostVariables;
	private final Map<IcfgLocation, Integer> mAbstractLocationIds;
	private final Map<String, IcfgLocation> mEntryLocations;
	private final QuantifierEliminationMode mEliminationMode;

	public TransFormulaToInterferencePredicate(final IUltimateServiceProvider services,
			final ManagedScript managedScript, final BasicPredicateFactory predicateFactory,
			final PrimedDefaultIcfgSymbolTable symbolTable, final GhostVariableManager ghostVariables) {
		this(services, managedScript, predicateFactory, symbolTable, ghostVariables, Map.of(), Map.of(),
				QuantifierEliminationMode.LIGHT);
	}

	public TransFormulaToInterferencePredicate(final IUltimateServiceProvider services,
			final ManagedScript managedScript, final BasicPredicateFactory predicateFactory,
			final PrimedDefaultIcfgSymbolTable symbolTable, final GhostVariableManager ghostVariables,
			final QuantifierEliminationMode eliminationMode) {
		this(services, managedScript, predicateFactory, symbolTable, ghostVariables, Map.of(), Map.of(),
				eliminationMode);
	}

	public TransFormulaToInterferencePredicate(final IUltimateServiceProvider services,
			final ManagedScript managedScript, final BasicPredicateFactory predicateFactory,
			final PrimedDefaultIcfgSymbolTable symbolTable, final GhostVariableManager ghostVariables,
			final Map<IcfgLocation, Integer> abstractLocationIds, final Map<String, IcfgLocation> entryLocations,
			final QuantifierEliminationMode eliminationMode) {
		mServices = services;
		mManagedScript = managedScript;
		mPredicateFactory = predicateFactory;
		mSymbolTable = symbolTable;
		mGhostVariables = ghostVariables;
		mAbstractLocationIds = Map.copyOf(Objects.requireNonNull(abstractLocationIds));
		mEntryLocations = Map.copyOf(Objects.requireNonNull(entryLocations));
		mEliminationMode = eliminationMode;
	}

	public IPredicate translateForInterference(final TransFormula tf, final String interferingThread,
			final IcfgLocation sourceLocation, final IcfgLocation targetLocation) {
		return translateForInterferenceInternal(tf, interferingThread, sourceLocation, targetLocation, null, null);
	}

	public IPredicate translateForInterferenceWithFork(final TransFormula tf, final String interferingThread,
			final IcfgLocation sourceLocation, final IcfgLocation targetLocation, final String forkedThreadId,
			final IcfgLocation forkedEntry) {
		return translateForInterferenceInternal(tf, interferingThread, sourceLocation, targetLocation, forkedThreadId,
				forkedEntry);
	}

	private IPredicate translateForInterferenceInternal(final TransFormula tf, final String interferingThread,
			final IcfgLocation sourceLocation, final IcfgLocation targetLocation, final String forkedThreadId,
			final IcfgLocation forkedEntry) {
		final Term baseTerm = translateBase(tf);

		final var script = mManagedScript.getScript();
		Term combined = baseTerm;

		final Term unchanged = createIdentityConstraintsForUnchangedGlobals(tf, interferingThread, forkedThreadId);
		combined = SmtUtils.and(script, combined, unchanged);

		if (mGhostVariables != null) {
			combined = SmtUtils.and(script, combined,
					mGhostVariables.createLocationConstraint(interferingThread, sourceLocation));
			combined = SmtUtils.and(script, combined,
					mGhostVariables.createPrimedLocationConstraint(interferingThread, targetLocation, mSymbolTable));

			if (forkedThreadId != null && forkedEntry != null) {
				combined = SmtUtils.and(script, combined,
						mGhostVariables.createPrimedLocationConstraint(forkedThreadId, forkedEntry, mSymbolTable));
			}
		}

		return mPredicateFactory.newPredicate(combined);
	}

	private Term translateBase(final TransFormula tf) {
		final Set<TermVariable> projectedVars = new HashSet<>();
		final Map<Term, Term> substitution = buildSubstitution(tf, projectedVars);

		final Term formula = applySubstitution(tf.getFormula(), substitution);
		addProjectedTransitionVars(tf, formula, projectedVars);
		return projectAwayLocals(formula, projectedVars);
	}

	private void addProjectedTransitionVars(final TransFormula tf, final Term formula,
			final Set<TermVariable> projectedVars) {
		projectedVars.addAll(tf.getAuxVars());
		if (tf instanceof final UnmodifiableTransFormula utf) {
			projectedVars.addAll(utf.getBranchEncoders());
		}
		for (final TermVariable freeVar : formula.getFreeVars()) {
			if (mSymbolTable.getProgramVar(freeVar) == null) {
				projectedVars.add(freeVar);
			}
		}
	}

	private Term createIdentityConstraintsForUnchangedGlobals(final TransFormula tf, final String interferingThread,
			final String forkedThreadId) {
		final var script = mManagedScript.getScript();
		final Set<IProgramVar> modified = tf.getOutVars().keySet();
		final TermVariable interferingLoc = mGhostVariables == null ? null
				: mGhostVariables.getLocationTermVar(interferingThread);
		final TermVariable forkedLoc = mGhostVariables == null || forkedThreadId == null ? null
				: mGhostVariables.getLocationTermVar(forkedThreadId);

		final List<Term> conjuncts = new ArrayList<>();
		for (final IProgramVar pv : mSymbolTable.getAllGlobalBaseVars()) {
			if (modified.contains(pv)) {
				continue;
			}
			final TermVariable tv = pv.getTermVariable();
			if (interferingLoc != null && tv.equals(interferingLoc)) {
				continue;
			}
			if (forkedLoc != null && tv.equals(forkedLoc)) {
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
		return RelationalPredicateUtils.existentiallyProject(formula, localVars, mServices, mManagedScript,
				mEliminationMode);
	}

	public PrimedDefaultIcfgSymbolTable getSymbolTable() {
		return mSymbolTable;
	}

	public boolean isLocationStutterStep(final IcfgLocation sourceLocation, final IcfgLocation targetLocation) {
		final Integer sourceAbs = mAbstractLocationIds.get(sourceLocation);
		final Integer targetAbs = mAbstractLocationIds.get(targetLocation);
		if (sourceAbs == null || targetAbs == null) {
			return false;
		}
		return sourceAbs.equals(targetAbs);
	}

	public Integer getAbstractLocationIdOrNull(final IcfgLocation location) {
		return mAbstractLocationIds.get(location);
	}

	public boolean hasAbstractLocationIds() {
		return !mAbstractLocationIds.isEmpty();
	}

	public IcfgLocation getEntryLocation(final String threadId) {
		final IcfgLocation entry = mEntryLocations.get(threadId);
		if (entry != null) {
			return entry;
		}
		if (mGhostVariables != null) {
			return mGhostVariables.getEntryLocation(threadId);
		}
		return null;
	}

	public TermVariable getLocationTermVarOrNull(final String threadId) {
		if (mGhostVariables == null) {
			return null;
		}
		return mGhostVariables.getLocationTermVar(threadId);
	}
}
