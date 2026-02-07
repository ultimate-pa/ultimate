package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ConcurrencyInformation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ghostvariables.GhostVariableManager;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicateUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class ConcurrentSymbolicTools extends SymbolicTools {

	private static final String MAIN_THREAD = "ULTIMATE.start";

	private final IIcfg<IcfgLocation> mIcfg;
	private final IUltimateServiceProvider mServices;
	private final ThreadModularSifaSettings mSettings;
	private GhostVariableManager mGhostVariables;

	private String mCurrentThreadId;
	private IInterferenceAbstraction mInterferences;
	private Map<IcfgLocation, IPredicate> mLocationPredicates;
	private IDomain mDomain;

	public ConcurrentSymbolicTools(final IUltimateServiceProvider services, final SifaStats stats,
			final IIcfg<IcfgLocation> icfg, final SimplificationTechnique simplification,
			final IIcfgSymbolTable symbolTable, final ThreadModularSifaSettings settings) {
		super(services, stats, icfg, simplification, symbolTable);
		mIcfg = icfg;
		mServices = services;
		mSettings = settings;
	}

	public ThreadModularSifaSettings getSettings() {
		return mSettings;
	}

	public void setGhostVariableManager(final GhostVariableManager ghostVariables) {
		mGhostVariables = ghostVariables;
	}

	// Mutable per-thread config: set before each thread's analysis in the fixpoint loop.
	public void configureForThread(final String threadId, final IInterferenceAbstraction interferences,
			final Map<IcfgLocation, IPredicate> locationPredicates, final IDomain domain) {
		mCurrentThreadId = threadId;
		mInterferences = interferences;
		mLocationPredicates = locationPredicates;
		mDomain = domain;
	}

	@Override
	public IPredicate post(final IPredicate input, final IIcfgTransition<IcfgLocation> transition) {
		final IPredicate basePostState = super.post(input, transition);
		return applyInterferencesIfAny(addLocationUpdate(basePostState, transition));
	}

	@Override
	public IPredicate postCall(final IPredicate input, final IIcfgCallTransition<IcfgLocation> transition) {
		final IPredicate basePostState = super.postCall(input, transition);
		return applyInterferencesIfAny(addLocationUpdate(basePostState, transition));
	}

	@Override
	public IPredicate postReturn(final IPredicate inputBeforeCall, final IPredicate inputBeforeReturn,
			final IIcfgReturnTransition<IcfgLocation, IIcfgCallTransition<IcfgLocation>> returnTransition) {
		final IPredicate basePostState = super.postReturn(inputBeforeCall, inputBeforeReturn, returnTransition);
		return applyInterferencesIfAny(addLocationUpdate(basePostState, returnTransition));
	}

	public IPredicate postNoOpTransition(final IPredicate input, final IIcfgTransition<IcfgLocation> transition) {
		return applyInterferencesIfAny(addLocationUpdate(input, transition));
	}

	private IPredicate applyInterferencesIfAny(final IPredicate state) {
		if (mInterferences == null || mCurrentThreadId == null) {
			return state;
		}
		return mInterferences.applyToState(state, mCurrentThreadId, mDomain);
	}

	// TODO: handle fork mechanics with thread counters
	private IPredicate addLocationUpdate(final IPredicate postState, final IIcfgTransition<IcfgLocation> transition) {
		if (!mSettings.useGhostLocations() || mCurrentThreadId == null) {
			return postState;
		}

		final TermVariable currentLocTv = mGhostVariables.getLocationTermVar(mCurrentThreadId);
		if (currentLocTv == null) {
			return postState;
		}

		// Project away old location value, then assert the new one
		final Term projected = RelationalPredicateUtils.existentiallyProject(postState.getFormula(),
				Set.of(currentLocTv), mServices, getManagedScript());
		final Term combined = SmtUtils.and(getScript(), projected,
				mGhostVariables.createLocationConstraint(mCurrentThreadId, transition.getTarget()));
		return predicate(combined);
	}

	public IPredicate getInitialStatePredicate(final String threadId) {
		if (threadId.equals(MAIN_THREAD)) {
			return applyInterferencesIfAny(getMainThreadInitialState());
		}
		// Thread starts from the state at its fork point(s); unreachable if never forked
		final Set<IPredicate> forkStates = collectForkStates(threadId);
		if (forkStates.isEmpty()) {
			return bottom();
		}
		IPredicate result = null;
		for (final IPredicate pred : forkStates) {
			result = result == null ? pred : mDomain.join(result, pred);
		}
		return applyInterferencesIfAny(result);
	}

	private IPredicate getMainThreadInitialState() {
		if (!mSettings.useGhostLocations()) {
			return top();
		}
		return predicate(mGhostVariables.createAllLocationsAtEntry());
	}

	private Set<IPredicate> collectForkStates(final String threadId) {
		final Set<IPredicate> states = new HashSet<>();
		if (mLocationPredicates == null) {
			return states;
		}
		final ConcurrencyInformation concInfo = mIcfg.getCfgSmtToolkit().getConcurrencyInformation();
		for (final IIcfgForkTransitionThreadCurrent<IcfgLocation> fork : concInfo.getThreadInstanceMap().keySet()) {
			if (!fork.getNameOfForkedProcedure().equals(threadId)) {
				continue;
			}
			final IPredicate forkState = mLocationPredicates.get(fork.getSource());
			if (forkState != null) {
				if (mSettings.useGhostLocations()) {
					final String forkingTid = fork.getSource().getProcedure();
					states.add(overrideLoc(forkState, forkingTid, fork.getTarget()));
				} else {
					states.add(forkState);
				}
			}
		}
		return states;
	}
	
	// Replace the forking thread's ghost location with the fork target location.
	// Data state from pre-fork is preserved; only the location variable changes.
	private IPredicate overrideLoc(final IPredicate state, final String threadId, final IcfgLocation newLoc) {
		final TermVariable locTv = mGhostVariables.getLocationTermVar(threadId);
		final Term projected = RelationalPredicateUtils.existentiallyProject(
				state.getFormula(), Set.of(locTv), mServices, getManagedScript());
		final Term combined = SmtUtils.and(getScript(), projected,
				mGhostVariables.createLocationConstraint(threadId, newLoc));
		return predicate(combined);
	}
}
