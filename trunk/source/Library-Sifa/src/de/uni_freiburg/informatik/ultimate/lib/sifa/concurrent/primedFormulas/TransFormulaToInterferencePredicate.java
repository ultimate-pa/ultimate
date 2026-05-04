package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ghostvariables.GhostVariableManager;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.Script;
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

	public TransFormulaToInterferencePredicate(final IUltimateServiceProvider services,
			final ManagedScript managedScript, final BasicPredicateFactory predicateFactory,
			final PrimedDefaultIcfgSymbolTable symbolTable, final GhostVariableManager ghostVariables) {
		this(services, managedScript, predicateFactory, symbolTable, ghostVariables, Map.of(), Map.of());
	}

	public TransFormulaToInterferencePredicate(final IUltimateServiceProvider services,
			final ManagedScript managedScript, final BasicPredicateFactory predicateFactory,
			final PrimedDefaultIcfgSymbolTable symbolTable, final GhostVariableManager ghostVariables,
			final Map<IcfgLocation, Integer> abstractLocationIds, final Map<String, IcfgLocation> entryLocations) {
		mServices = services;
		mManagedScript = managedScript;
		mPredicateFactory = predicateFactory;
		mSymbolTable = symbolTable;
		mGhostVariables = ghostVariables;
		mAbstractLocationIds = Map.copyOf(Objects.requireNonNull(abstractLocationIds));
		mEntryLocations = Map.copyOf(Objects.requireNonNull(entryLocations));
	}

	public IPredicate translateForInterference(final TransFormula tf, final String interferingThread,
			final IcfgLocation sourceLocation, final IcfgLocation targetLocation) {
		return translateForInterference(tf, interferingThread, sourceLocation, targetLocation, Set.of());
	}

	public IPredicate translateForInterference(final TransFormula tf, final String interferingThread,
			final IcfgLocation sourceLocation, final IcfgLocation targetLocation,
			final Set<IProgramVar> additionallyModifiedGlobals) {
		return translateForInterferenceInternal(tf, interferingThread, sourceLocation, targetLocation, null, null,
				additionallyModifiedGlobals);
	}

	public IPredicate translateForInterferenceWithFork(final TransFormula tf, final String interferingThread,
			final IcfgLocation sourceLocation, final IcfgLocation targetLocation, final String forkedThreadId,
			final IcfgLocation forkedEntry) {
		return translateForInterferenceWithFork(tf, interferingThread, sourceLocation, targetLocation, forkedThreadId,
				forkedEntry, Set.of());
	}

	public IPredicate translateForInterferenceWithFork(final TransFormula tf, final String interferingThread,
			final IcfgLocation sourceLocation, final IcfgLocation targetLocation, final String forkedThreadId,
			final IcfgLocation forkedEntry, final Set<IProgramVar> additionallyModifiedGlobals) {
		return translateForInterferenceInternal(tf, interferingThread, sourceLocation, targetLocation, forkedThreadId,
				forkedEntry, additionallyModifiedGlobals);
	}

	private IPredicate translateForInterferenceInternal(final TransFormula tf, final String interferingThread,
			final IcfgLocation sourceLocation, final IcfgLocation targetLocation, final String forkedThreadId,
			final IcfgLocation forkedEntry, final Set<IProgramVar> additionallyModifiedGlobals) {
		final Set<IProgramVar> extraModified = additionallyModifiedGlobals == null ? Set.of()
				: Set.copyOf(additionallyModifiedGlobals);
		final List<Term> conjuncts = new ArrayList<>();
		conjuncts.add(translateBase(tf));
		conjuncts.add(createIdentityConstraintsForUnchangedGlobals(tf, interferingThread, forkedThreadId, extraModified));
		addLocationConstraints(conjuncts, interferingThread, sourceLocation, targetLocation, forkedThreadId, forkedEntry);
		return mPredicateFactory.newPredicate(SmtUtils.and(mManagedScript.getScript(), conjuncts));
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
			final String forkedThreadId, final Set<IProgramVar> additionallyModifiedGlobals) {
		final var script = mManagedScript.getScript();
		final Set<IProgramVar> modified = InterferenceUtils.getChangedGlobals(tf, additionallyModifiedGlobals);
		final TermVariable interferingLoc = getLocationTermVarOrNull(interferingThread);
		final TermVariable forkedLoc = getLocationTermVarOrNull(forkedThreadId);

		final List<Term> conjuncts = new ArrayList<>();
		for (final IProgramVar pv : mSymbolTable.getAllGlobalBaseVars()) {
			if (shouldKeepIdentityConstraint(pv, modified, interferingLoc, forkedLoc)) {
				final TermVariable primed = mSymbolTable.getPrimedVar(pv);
				if (primed != null) {
					conjuncts.add(SmtUtils.binaryEquality(script, primed, pv.getTermVariable()));
				}
			}
		}
		return SmtUtils.and(script, conjuncts);
	}

	private void addLocationConstraints(final List<Term> conjuncts, final String interferingThread,
			final IcfgLocation sourceLocation, final IcfgLocation targetLocation, final String forkedThreadId,
			final IcfgLocation forkedEntry) {
		if (mGhostVariables == null) {
			return;
		}
		conjuncts.add(mGhostVariables.createLocationConstraint(interferingThread, sourceLocation));
		conjuncts.add(mGhostVariables.createPrimedLocationConstraint(interferingThread, targetLocation, mSymbolTable));
		if (forkedThreadId != null && forkedEntry != null) {
			conjuncts.add(mGhostVariables.createNotForkedConstraint(forkedThreadId));
			conjuncts.add(mGhostVariables.createPrimedLocationConstraint(forkedThreadId, forkedEntry, mSymbolTable));
		}
	}

	private static boolean shouldKeepIdentityConstraint(final IProgramVar variable, final Set<IProgramVar> modified,
			final TermVariable interferingLoc, final TermVariable forkedLoc) {
		if (modified.contains(variable)) {
			return false;
		}
		final TermVariable termVariable = variable.getTermVariable();
		return !termVariable.equals(interferingLoc) && !termVariable.equals(forkedLoc);
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
				if (entry.getValue() == tf.getInVars().get(pv)) {
					continue;
				}
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

	public IUltimateServiceProvider getServices() {
		return mServices;
	}

	public ManagedScript getManagedScript() {
		return mManagedScript;
	}

	public BasicPredicateFactory getPredicateFactory() {
		return mPredicateFactory;
	}

	public GhostVariableManager getGhostVariables() {
		return mGhostVariables;
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

	public IcfgLocation getEntryLocation(final String threadId) {
		final IcfgLocation entry = mEntryLocations.get(threadId);
		return entry != null ? entry : mGhostVariables == null ? null : mGhostVariables.getEntryLocation(threadId);
	}

	public TermVariable getLocationTermVarOrNull(final String threadId) {
		if (mGhostVariables == null || threadId == null) {
			return null;
		}
		return mGhostVariables.getLocationTermVar(threadId);
	}

	public IPredicate projectPreStateToSharedState(final IPredicate preState) {
		final Set<TermVariable> localsToProject = preState.getVars().stream().filter(var -> !var.isGlobal())
				.map(IProgramVar::getTermVariable).collect(Collectors.toSet());
		if (localsToProject.isEmpty()) {
			return preState;
		}
		final Term projected = RelationalPredicateUtils.existentiallyProject(preState.getFormula(), localsToProject,
				mServices, mManagedScript);
		return mPredicateFactory.newPredicate(projected);
	}
}
