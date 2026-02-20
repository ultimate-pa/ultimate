package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

import java.util.Map;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.cfgpreprocessing.LocationMarkerTransition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ghostvariables.GhostVariableManager;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterference;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceCollection;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicateUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.InitialStateFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.ThreadActivityPreanalysis;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.ThreadModularSifaSettings;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class ConcurrentSymbolicTools extends SymbolicTools {

	private final IUltimateServiceProvider mServices;
	private final ThreadModularSifaSettings mSettings;
	private final InitialStateFactory mInitialStateFactory;
	private GhostVariableManager mGhostVariables;
	private ThreadActivityPreanalysis mThreadActivityPreanalysis;
	private ThreadAnalysisContext mThreadContext;

	public ConcurrentSymbolicTools(final IUltimateServiceProvider services, final SifaStats stats,
			final IIcfg<IcfgLocation> icfg, final SimplificationTechnique simplification,
			final IIcfgSymbolTable symbolTable, final ThreadModularSifaSettings settings) {
		super(services, stats, icfg, simplification, symbolTable);
		mServices = services;
		mSettings = settings;
		mInitialStateFactory = new InitialStateFactory(this, icfg);
	}

	public ThreadModularSifaSettings getSettings() {
		return mSettings;
	}

	public GhostVariableManager getGhostVariables() {
		return mGhostVariables;
	}

	public ThreadActivityPreanalysis getThreadActivityPreanalysis() {
		return mThreadActivityPreanalysis;
	}

	public void configureStaticAnalysis(final GhostVariableManager ghostVariables,
			final ThreadActivityPreanalysis activityPreanalysis) {
		mGhostVariables = ghostVariables;
		mThreadActivityPreanalysis = Objects.requireNonNull(activityPreanalysis);
		mInitialStateFactory.configureStaticAnalysis(ghostVariables);
	}

	public void configureForThread(final String threadId, final InterferenceCollection interferences,
			final Map<IcfgLocation, IPredicate> locationPredicates, final IDomain analysisDomain,
			final IDomain interferenceDomain, final RelationalPredicatePostcondition postcondition) {
		mThreadContext = new ThreadAnalysisContext(Objects.requireNonNull(threadId),
				Objects.requireNonNull(interferences), Objects.requireNonNull(interferenceDomain),
				Objects.requireNonNull(postcondition));
		mInitialStateFactory.configureForThread(Objects.requireNonNull(locationPredicates),
				Objects.requireNonNull(analysisDomain));
	}

	@Override
	public IPredicate post(final IPredicate input, final IIcfgTransition<IcfgLocation> transition) {
		final IPredicate spResult = super.post(input, transition);
		return updateGhostvarsAndApplyInterferences(spResult, transition);
	}

	@Override
	public IPredicate postCall(final IPredicate input, final IIcfgCallTransition<IcfgLocation> transition) {
		throw new UnsupportedOperationException();
	}

	@Override
	public IPredicate postReturn(final IPredicate inputBeforeCall, final IPredicate inputBeforeReturn,
			final IIcfgReturnTransition<IcfgLocation, IIcfgCallTransition<IcfgLocation>> returnTransition) {
		throw new UnsupportedOperationException();
	}

	public IPredicate postNoOpTransition(final IPredicate input, final IIcfgTransition<IcfgLocation> transition) {
		if (transition instanceof LocationMarkerTransition) {
			return input;
		}
		return updateGhostvarsAndApplyInterferences(input, transition);
	}

	public IPredicate applyInterferences(final IPredicate state, final IcfgLocation location) {
		final InterferenceCollection interferences = mThreadContext.interferences();
		if (interferences.isEmpty()) {
			return state;
		}
		if (SmtUtils.isTrueLiteral(state.getFormula()) || SmtUtils.isFalseLiteral(state.getFormula())) {
			return state;
		}

		final String threadId = mThreadContext.threadId();
		final IDomain domain = mThreadContext.interferenceDomain();
		final RelationalPredicatePostcondition postcondition = mThreadContext.postcondition();
		final boolean includeSelf = mThreadActivityPreanalysis.getMultiForkedThreads().contains(threadId);

		final java.util.List<String> sortedThreadIds = new java.util.ArrayList<>(interferences.getThreadIds());
		java.util.Collections.sort(sortedThreadIds);
		final java.util.List<IInterference> applicableInterferences = new java.util.ArrayList<>();
		for (final String otherThreadId : sortedThreadIds) {
			if (otherThreadId.equals(threadId) && !includeSelf) {
				continue;
			}
			if (!mThreadActivityPreanalysis.mayBeActiveAt(location, otherThreadId)) {
				continue;
			}
			final IInterference itf = interferences.getInterferenceForThread(otherThreadId);
			if (itf == null || itf.isTrivial()) {
				continue;
			}
			applicableInterferences.add(itf);
		}
		if (applicableInterferences.isEmpty()) {
			return state;
		}

		IPredicate current = state;
		for (;;) {
			final IPredicate roundStart = current;
			for (final IInterference itf : applicableInterferences) {
				current = itf.applyUntilFixpoint(current, domain, postcondition, mGhostVariables, getManagedScript(),
						getFactory(), mSettings.innerWideningThreshold(), getStats());
			}
			if (domain.isSubsetEq(current, roundStart).isTrueForAbstraction()) {
				return roundStart;
			}
		}
	}

	private IPredicate addLocationUpdate(final IPredicate postState, final IIcfgTransition<IcfgLocation> transition) {
		return addLocationUpdateForThread(postState, mThreadContext.threadId(), transition.getTarget());
	}

	public IPredicate addLocationUpdateForThread(final IPredicate postState, final String threadId,
			final IcfgLocation targetLocation) {
		if (mGhostVariables == null) {
			return postState;
		}
		if (SmtUtils.isFalseLiteral(postState.getFormula())) {
			return postState;
		}

		final TermVariable currentLocTv = mGhostVariables.getLocationTermVar(threadId);
		if (currentLocTv == null) {
			return postState;
		}
		final Term locConstraint = mGhostVariables.createLocationConstraint(threadId, targetLocation);
		if (SmtUtils.isTrueLiteral(postState.getFormula())) {
			return predicate(locConstraint);
		}
		if (!containsFreeVar(postState.getFormula(), currentLocTv)) {
			return predicate(SmtUtils.and(getScript(), postState.getFormula(), locConstraint));
		}

		final Term projected = RelationalPredicateUtils.existentiallyProject(postState.getFormula(),
				Set.of(currentLocTv), mServices, getManagedScript(), mSettings.quantifierEliminationMode());
		final Term combined = SmtUtils.and(getScript(), projected, locConstraint);
		return predicate(combined);
	}

	private IPredicate updateGhostvarsAndApplyInterferences(final IPredicate state,
			final IIcfgTransition<IcfgLocation> transition) {
		IPredicate updated = addLocationUpdate(state, transition);
		if (transition instanceof final IIcfgForkTransitionThreadCurrent<?> fork && mGhostVariables != null) {
			final String forkedThreadId = fork.getNameOfForkedProcedure();
			final IcfgLocation forkedEntry = mGhostVariables.getEntryLocation(forkedThreadId);
			updated = addLocationUpdateForThread(updated, forkedThreadId, forkedEntry);
		}
		if (!transitionTouchesGlobals(transition)) {
			return updated;
		}
		return applyInterferences(updated, transition.getTarget());
	}

	private static boolean transitionTouchesGlobals(final IIcfgTransition<IcfgLocation> transition) {
		final var tf = transition.getTransformula();
		if (tf == null) {
			return false;
		}
		if (transition instanceof IIcfgForkTransitionThreadCurrent<?>) {
			return true;
		}
		for (final var pv : tf.getInVars().keySet()) {
			if (pv.isGlobal()) {
				return true;
			}
		}
		for (final var pv : tf.getOutVars().keySet()) {
			if (pv.isGlobal()) {
				return true;
			}
		}
		return false;
	}

	public IPredicate getInitialStatePredicate(final String threadId) {
		return mInitialStateFactory.getInitialStatePredicate(threadId);
	}

	private static boolean containsFreeVar(final Term formula, final TermVariable variable) {
		for (final TermVariable freeVar : formula.getFreeVars()) {
			if (freeVar == variable) {
				return true;
			}
		}
		return false;
	}

	private static record ThreadAnalysisContext(String threadId, InterferenceCollection interferences,
			IDomain interferenceDomain, RelationalPredicatePostcondition postcondition) {
	}
}
