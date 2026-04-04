package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
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
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.GuardedPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
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

	public GuardedPredicate translateGuardedExactUpdateOrNull(final IPredicate sharedPreState, final TransFormula tf,
			final String interferingThread, final IcfgLocation sourceLocation, final IcfgLocation targetLocation,
			final String forkedThreadId, final IcfgLocation forkedEntry, final Set<TermVariable> modifiedGlobals) {
		if (!tf.getAuxVars().isEmpty()) {
			return null;
		}
		if (tf instanceof final UnmodifiableTransFormula utf && !utf.getBranchEncoders().isEmpty()) {
			return null;
		}
		final Set<TermVariable> modified =
				modifiedGlobals == null ? Set.of() : Set.copyOf(modifiedGlobals);
		final Set<TermVariable> localVars = new HashSet<>();
		final Map<Term, Term> substitution = buildSubstitution(tf, localVars);
		final Term substituted = applySubstitution(tf.getFormula(), substitution);
		final Map<TermVariable, TermVariable> primedToBaseModified = buildPrimedToBaseModifiedMap(modified);
		if (primedToBaseModified == null) {
			return null;
		}

		final List<Term> guardConjuncts = new ArrayList<>();
		if (sharedPreState != null && !SmtUtils.isTrueLiteral(sharedPreState.getFormula())) {
			guardConjuncts.add(sharedPreState.getFormula());
		}
		final Script script = mManagedScript.getScript();
		if (mGhostVariables != null) {
			final Term sourceLocationGuard = mGhostVariables.createLocationConstraint(interferingThread, sourceLocation);
			if (!SmtUtils.isTrueLiteral(sourceLocationGuard)) {
				guardConjuncts.add(sourceLocationGuard);
			}
			if (forkedThreadId != null) {
				final Term notForkedGuard = mGhostVariables.createNotForkedConstraint(forkedThreadId);
				if (!SmtUtils.isTrueLiteral(notForkedGuard)) {
					guardConjuncts.add(notForkedGuard);
				}
			}
		}

		final Map<TermVariable, Term> exactUpdates = new LinkedHashMap<>();
		addManualLocationUpdates(exactUpdates, modified, interferingThread, targetLocation, forkedThreadId, forkedEntry, script);

		final List<Term> conjuncts = new ArrayList<>();
		InterferenceUtils.collectConjuncts(substituted, conjuncts);
		for (final Term conjunct : conjuncts) {
			if (SmtUtils.isTrueLiteral(conjunct)) {
				continue;
			}
			final UpdateMatch exactUpdate = extractExactUpdateOrNull(conjunct, primedToBaseModified);
			if (exactUpdate != null) {
				final Term previous = exactUpdates.putIfAbsent(exactUpdate.baseVariable(), exactUpdate.updateConstraint());
				if (previous != null && !previous.equals(exactUpdate.updateConstraint())) {
					return null;
				}
				continue;
			}
			if (isExplicitIdentityOnUnchangedGlobal(conjunct, modified)) {
				continue;
			}
			if (isPureUnprimedGlobalConjunct(conjunct)) {
				guardConjuncts.add(conjunct);
				continue;
			}
			return null;
		}

		if (!exactUpdates.keySet().containsAll(modified)) {
			return null;
		}
		final IPredicate guard = guardConjuncts.isEmpty() ? null
				: mPredicateFactory.newPredicate(guardConjuncts.size() == 1 ? guardConjuncts.get(0)
						: SmtUtils.and(script, guardConjuncts.toArray(new Term[0])));
		final Term effectFormula = exactUpdates.isEmpty() ? script.term("true")
				: exactUpdates.size() == 1 ? exactUpdates.values().iterator().next()
						: SmtUtils.and(script, exactUpdates.values().toArray(new Term[0]));
		final IPredicate effect = mPredicateFactory.newPredicate(effectFormula);
		return new GuardedPredicate(guard, effect, modified);
	}

	private IPredicate translateForInterferenceInternal(final TransFormula tf, final String interferingThread,
			final IcfgLocation sourceLocation, final IcfgLocation targetLocation, final String forkedThreadId,
			final IcfgLocation forkedEntry, final Set<IProgramVar> additionallyModifiedGlobals) {
		final Set<IProgramVar> extraModified =
				additionallyModifiedGlobals == null ? Set.of() : Set.copyOf(additionallyModifiedGlobals);
		final Term baseTerm = translateBase(tf);

		final var script = mManagedScript.getScript();
		Term combined = baseTerm;

		final Term unchanged =
				createIdentityConstraintsForUnchangedGlobals(tf, interferingThread, forkedThreadId, extraModified);
		combined = SmtUtils.and(script, combined, unchanged);

		if (mGhostVariables != null) {
			combined = SmtUtils.and(script, combined,
					mGhostVariables.createLocationConstraint(interferingThread, sourceLocation));
			combined = SmtUtils.and(script, combined,
					mGhostVariables.createPrimedLocationConstraint(interferingThread, targetLocation, mSymbolTable));

			if (forkedThreadId != null && forkedEntry != null) {
				combined = SmtUtils.and(script, combined, mGhostVariables.createNotForkedConstraint(forkedThreadId));
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
			final String forkedThreadId, final Set<IProgramVar> additionallyModifiedGlobals) {
		final var script = mManagedScript.getScript();
		final Set<IProgramVar> modified = InterferenceUtils.getChangedGlobals(tf, additionallyModifiedGlobals);
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

	private Map<TermVariable, TermVariable> buildPrimedToBaseModifiedMap(final Set<TermVariable> modifiedGlobals) {
		final Map<TermVariable, TermVariable> primedToBase = new HashMap<>();
		for (final TermVariable modifiedGlobal : modifiedGlobals) {
			final IProgramVar programVar = mSymbolTable.getProgramVar(modifiedGlobal);
			if (programVar == null) {
				return null;
			}
			final IProgramVar baseVar = mSymbolTable.getBaseVar(programVar);
			final TermVariable primedVar = mSymbolTable.getPrimedVar(baseVar);
			if (primedVar == null) {
				return null;
			}
			primedToBase.put(primedVar, baseVar.getTermVariable());
		}
		return primedToBase;
	}

	private void addManualLocationUpdates(final Map<TermVariable, Term> exactUpdates, final Set<TermVariable> modifiedGlobals,
			final String interferingThread, final IcfgLocation targetLocation, final String forkedThreadId,
			final IcfgLocation forkedEntry, final Script script) {
		if (mGhostVariables == null) {
			return;
		}
		addManualLocationUpdate(exactUpdates, modifiedGlobals, mGhostVariables.getLocationTermVar(interferingThread),
				interferingThread, targetLocation, script);
		if (forkedThreadId != null && forkedEntry != null) {
			addManualLocationUpdate(exactUpdates, modifiedGlobals, mGhostVariables.getLocationTermVar(forkedThreadId),
					forkedThreadId, forkedEntry, script);
		}
	}

	private void addManualLocationUpdate(final Map<TermVariable, Term> exactUpdates, final Set<TermVariable> modifiedGlobals,
			final TermVariable baseLocationVar, final String threadId, final IcfgLocation targetLocation, final Script script) {
		if (baseLocationVar == null || !modifiedGlobals.contains(baseLocationVar)) {
			return;
		}
		final IProgramVar programVar = mSymbolTable.getProgramVar(baseLocationVar);
		if (programVar == null) {
			return;
		}
		final TermVariable primedLocationVar = mSymbolTable.getPrimedVar(mSymbolTable.getBaseVar(programVar));
		if (primedLocationVar == null) {
			return;
		}
		final Term primedConstraint = mGhostVariables.createPrimedLocationConstraint(threadId, targetLocation, mSymbolTable);
		final Term renamed = Substitution.apply(mManagedScript, Map.of(primedLocationVar, baseLocationVar), primedConstraint);
		exactUpdates.put(baseLocationVar, renamed);
	}

	private UpdateMatch extractExactUpdateOrNull(final Term conjunct, final Map<TermVariable, TermVariable> primedToBaseModified) {
		if (!(conjunct instanceof final ApplicationTerm app) || !"=".equals(app.getFunction().getName())
				|| app.getParameters().length != 2) {
			return null;
		}
		final UpdateMatch left = extractExactUpdateOrNull(app.getParameters()[0], app.getParameters()[1], conjunct,
				primedToBaseModified);
		if (left != null) {
			return left;
		}
		return extractExactUpdateOrNull(app.getParameters()[1], app.getParameters()[0], conjunct, primedToBaseModified);
	}

	private UpdateMatch extractExactUpdateOrNull(final Term maybePrimedVar, final Term maybeConstant, final Term fullConjunct,
			final Map<TermVariable, TermVariable> primedToBaseModified) {
		if (maybeConstant.getFreeVars().length != 0) {
			return null;
		}
		final TermVariable primedVar = extractSingleFreeVar(maybePrimedVar);
		if (primedVar == null) {
			return null;
		}
		final TermVariable baseVar = primedToBaseModified.get(primedVar);
		if (baseVar == null) {
			return null;
		}
		final Term renamed = Substitution.apply(mManagedScript, Map.of(primedVar, baseVar), fullConjunct);
		return new UpdateMatch(baseVar, renamed);
	}

	private boolean isExplicitIdentityOnUnchangedGlobal(final Term conjunct, final Set<TermVariable> modifiedGlobals) {
		if (!(conjunct instanceof final ApplicationTerm app) || !"=".equals(app.getFunction().getName())
				|| app.getParameters().length != 2) {
			return false;
		}
		final VariableRef left = describeGlobalReference(app.getParameters()[0]);
		final VariableRef right = describeGlobalReference(app.getParameters()[1]);
		if (left == null || right == null || left.primed() == right.primed()) {
			return false;
		}
		return left.baseVariable().equals(right.baseVariable()) && !modifiedGlobals.contains(left.baseVariable());
	}

	private boolean isPureUnprimedGlobalConjunct(final Term conjunct) {
		for (final TermVariable freeVar : conjunct.getFreeVars()) {
			final IProgramVar programVar = mSymbolTable.getProgramVar(freeVar);
			if (programVar == null || !programVar.isGlobal() || mSymbolTable.isPrimedVar(programVar)) {
				return false;
			}
		}
		return true;
	}

	private VariableRef describeGlobalReference(final Term term) {
		final TermVariable freeVar = extractSingleFreeVar(term);
		if (freeVar == null) {
			return null;
		}
		final IProgramVar programVar = mSymbolTable.getProgramVar(freeVar);
		if (programVar == null || !programVar.isGlobal()) {
			return null;
		}
		return new VariableRef(mSymbolTable.getBaseVar(programVar).getTermVariable(), mSymbolTable.isPrimedVar(programVar));
	}

	private static TermVariable extractSingleFreeVar(final Term term) {
		final TermVariable[] freeVars = term.getFreeVars();
		return freeVars.length == 1 ? freeVars[0] : null;
	}

	private static record UpdateMatch(TermVariable baseVariable, Term updateConstraint) {
	}

	private static record VariableRef(TermVariable baseVariable, boolean primed) {
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

	public IPredicate projectPreStateToSharedState(final IPredicate preState) {
		final Set<TermVariable> localsToProject = new HashSet<>();
		for (final IProgramVar var : preState.getVars()) {
			if (!var.isGlobal()) {
				localsToProject.add(var.getTermVariable());
			}
		}
		if (localsToProject.isEmpty()) {
			return preState;
		}
		final Term projected = RelationalPredicateUtils.existentiallyProject(preState.getFormula(), localsToProject,
				mServices, mManagedScript);
		return mPredicateFactory.newPredicate(projected);
	}
}
