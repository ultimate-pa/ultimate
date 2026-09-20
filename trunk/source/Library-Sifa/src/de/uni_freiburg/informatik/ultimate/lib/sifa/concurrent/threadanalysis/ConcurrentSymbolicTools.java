/*
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.threadanalysis;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.cfgpreprocessing.LocationMarkerTransition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.domain.IThreadLocalDomainContext;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ghostvariables.GhostLocationStateUpdater;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ghostvariables.GhostVariableManager;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceSet;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.lockset.MustLocksetAnalysis;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.lockset.publish.PublishOnAcquire;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations.PrimedDefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.InitialStateFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.ThreadModularSifaSettings;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.threadactivity.ThreadActivityPreanalysis;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;

public class ConcurrentSymbolicTools extends SymbolicTools {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final SifaStats mStats;
	private final PrimedDefaultIcfgSymbolTable mSymbolTable;
	private final ThreadModularSifaSettings mSettings;
	private final InitialStateFactory mInitialStateFactory;
	private final JoinHandler mJoinHandler;
	private GhostVariableManager mGhostVariables;
	private MustLocksetAnalysis mLocksetInfo = MustLocksetAnalysis.disabled();
	private PublishOnAcquire mPublication = PublishOnAcquire.disabled();
	private ThreadActivityPreanalysis mThreadActivityPreanalysis;
	private GhostLocationStateUpdater mLocationStateUpdater;
	private ThreadAnalysisContext mThreadContext;
	private ObservedThreadStateRecorder mObservedStateRecorder;

	public ConcurrentSymbolicTools(final IUltimateServiceProvider services, final SifaStats stats,
			final IIcfg<IcfgLocation> icfg, final SimplificationTechnique simplification,
			final PrimedDefaultIcfgSymbolTable symbolTable, final ThreadModularSifaSettings settings) {
		super(services, stats, icfg, simplification, symbolTable);
		mLogger = services.getLoggingService().getLogger(ConcurrentSymbolicTools.class);
		mServices = services;
		mStats = stats;
		mSymbolTable = symbolTable;
		mSettings = settings;
		mInitialStateFactory = new InitialStateFactory(this, icfg);
		mJoinHandler = new JoinHandler(this, services, icfg);
	}

	public ThreadModularSifaSettings getSettings() {
		return mSettings;
	}

	public IUltimateServiceProvider getServices() {
		return mServices;
	}

	public PrimedDefaultIcfgSymbolTable getSymbolTable() {
		return mSymbolTable;
	}

	public ThreadActivityPreanalysis getThreadActivityPreanalysis() {
		return mThreadActivityPreanalysis;
	}

	public void rememberThreadLocationState(final IcfgLocation location, final IPredicate state) {
		mObservedStateRecorder.recordObservedState(location, state);
	}

	public Map<IcfgLocation, IPredicate> getObservedThreadLocationStates() {
		return mObservedStateRecorder.getObservedStates();
	}

	public void setPublication(final PublishOnAcquire publication) {
		mPublication = publication;
	}

	public void initializeStaticAnalysis(final GhostVariableManager ghostVariables,
			final ThreadActivityPreanalysis activityPreanalysis, final MustLocksetAnalysis locksetInfo) {
		mGhostVariables = ghostVariables;
		mThreadActivityPreanalysis = activityPreanalysis;
		mLocksetInfo = locksetInfo;
		mLocationStateUpdater = new GhostLocationStateUpdater(mServices, getManagedScript(), getFactory(),
				ghostVariables);
		mInitialStateFactory.configureStaticAnalysis(ghostVariables, mLocationStateUpdater);
		mJoinHandler.configureStaticAnalysis(ghostVariables, mLocationStateUpdater);
	}

	public void configureForThread(final String threadId, final IInterferenceSet interference,
			final Map<IcfgLocation, IPredicate> locationPredicates, final IDomain domain) {
		IThreadLocalDomainContext.setIfApplicable(domain, threadId);
		final List<String> sortedInterferenceThreadIds = interference == null ? List.of()
				: interference.threadIds().stream().sorted().toList();
		final boolean includeSelfInterference = mThreadActivityPreanalysis.getMultiForkedThreads().contains(threadId);
		mThreadContext = new ThreadAnalysisContext(threadId, interference, domain, includeSelfInterference,
				sortedInterferenceThreadIds, locationPredicates, new HashMap<>());
		mObservedStateRecorder = new ObservedThreadStateRecorder(domain, mGhostVariables);
		mInitialStateFactory.configureForThread(locationPredicates, domain);
	}

	@Override
	public IPredicate post(final IPredicate input, final IIcfgTransition<IcfgLocation> transition) {
		mObservedStateRecorder.recordTransitionInputState(transition, input);
		final IPredicate spResult = super.post(input, transition);
		final IPredicate joinProjected = mJoinHandler.projectJoinAssignedVars(spResult, transition);
		return updateGhostvarsAndApplyInterferences(joinProjected, transition);
	}

	public IPredicate postWithoutInterference(final IPredicate input, final IIcfgTransition<IcfgLocation> transition) {
		return super.post(input, transition);
	}

	@Override
	public IPredicate postCall(final IPredicate input, final IIcfgCallTransition<IcfgLocation> transition) {
		mLogger.error("Thread-modular SIFA encountered a procedure call at %s. Procedure calls are not supported; "
				+ "enable procedure inlining in the ICFG builder settings.", transition.getSource());
		throw new UnsupportedOperationException("Thread-modular SIFA does not support procedure calls (found at "
				+ transition.getSource() + "). Enable procedure inlining or restrict to fork/join concurrency.");
	}

	@Override
	public IPredicate postReturn(final IPredicate inputBeforeCall, final IPredicate inputBeforeReturn,
			final IIcfgReturnTransition<IcfgLocation, IIcfgCallTransition<IcfgLocation>> returnTransition) {
		mLogger.error("Thread-modular SIFA encountered a return transition at %s. Procedure calls are not supported; "
				+ "enable procedure inlining in the ICFG builder settings.", returnTransition.getSource());
		throw new UnsupportedOperationException("Thread-modular SIFA does not support procedure calls (found return at "
				+ returnTransition.getSource() + "). Enable procedure inlining or restrict to fork/join concurrency.");
	}

	public IPredicate postNoOpTransition(final IPredicate input, final IIcfgTransition<IcfgLocation> transition) {
		if (transition instanceof LocationMarkerTransition) {
			mObservedStateRecorder.recordTransitionInputState(transition, input);
			return applyInterferences(input, transition.getTarget());
		}
		return post(input, transition);
	}

	public IPredicate applyInterferences(final IPredicate state, final IcfgLocation location) {
		if (interferenceCannotChangeState(state)) {
			return state;
		}
		final Set<String> activeThreadIds = mThreadContext.activeInterferenceThreadsAt(location,
				mThreadActivityPreanalysis);
		if (activeThreadIds.isEmpty()) {
			return state;
		}
		final Set<String> observerLockset = mLocksetInfo.mustLocksetAt(location);
		final Set<String> interferenceObserverLockset = mSettings.locksetAwareInterference() ? observerLockset
				: Set.of();
		final IPredicate afterInterference = mThreadContext.interference().applyUntilFixpoint(state,
				mThreadContext.threadId(), activeThreadIds, interferenceObserverLockset, mThreadContext.domain(),
				mSettings.innerWideningThreshold(), mStats);
		return mPublication.restoreProtectedVariables(state, afterInterference, observerLockset);
	}

	private boolean interferenceCannotChangeState(final IPredicate state) {
		final IInterferenceSet interference = mThreadContext.interference();
		return interference == null || interference.isEmpty() || SmtUtils.isTrueLiteral(state.getFormula())
				|| SmtUtils.isFalseLiteral(state.getFormula());
	}

	private IPredicate updateGhostvarsAndApplyInterferences(final IPredicate state,
			final IIcfgTransition<IcfgLocation> transition) {
		IPredicate updated = addLocationUpdate(state, transition);
		if (mLocationStateUpdater.isEnabled() && transition instanceof final IIcfgForkTransitionThreadCurrent<?> fork) {
			updated = mLocationStateUpdater.addLocationUpdate(updated, fork.getNameOfForkedProcedure(),
					mGhostVariables.getEntryLocation(fork.getNameOfForkedProcedure()));
		}
		updated = mJoinHandler.extractJoinedThreadGlobalExitStateAndIntersect(updated, transition, mThreadContext,
				mThreadActivityPreanalysis);
		if (isThreadLocalTransition(transition)) {
			return updated;
		}
		updated = mPublication.applyAtAcquire(updated, transition);
		return applyInterferences(updated, transition.getTarget());
	}

	private static boolean isThreadLocalTransition(final IIcfgTransition<IcfgLocation> transition) {
		if (transition instanceof IIcfgForkTransitionThreadCurrent<?>
				|| transition instanceof IIcfgJoinTransitionThreadCurrent<?>) {
			return false;
		}
		final var tf = transition.getTransformula();
		if (tf == null) {
			return true;
		}
		return tf.getInVars().keySet().stream().noneMatch(v -> v.isGlobal())
				&& tf.getOutVars().keySet().stream().noneMatch(v -> v.isGlobal());
	}

	private IPredicate addLocationUpdate(final IPredicate postState, final IIcfgTransition<IcfgLocation> transition) {
		return mLocationStateUpdater.addLocationUpdate(postState, mThreadContext.threadId(), transition.getTarget());
	}

	public IDomain getEffectiveDomain() {
		return mThreadContext != null ? mThreadContext.domain() : null;
	}

	public IPredicate getInitialStatePredicate(final String threadId) {
		return mInitialStateFactory.getInitialStatePredicate(threadId);
	}

}
