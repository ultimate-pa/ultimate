package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup;

import java.util.HashSet;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ConcurrencyInformation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ConcurrentSymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ghostvariables.GhostVariableManager;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

public final class InitialStateFactory {

	private static final String MAIN_THREAD = "ULTIMATE.start";

	private final ConcurrentSymbolicTools mTools;
	private final IIcfg<IcfgLocation> mIcfg;

	private GhostVariableManager mGhostVariables;
	private Map<IcfgLocation, IPredicate> mLocationPredicates;
	private IDomain mAnalysisDomain;

	public InitialStateFactory(final ConcurrentSymbolicTools tools, final IIcfg<IcfgLocation> icfg) {
		mTools = Objects.requireNonNull(tools);
		mIcfg = Objects.requireNonNull(icfg);
	}

	public void configureStaticAnalysis(final GhostVariableManager ghostVariables) {
		mGhostVariables = ghostVariables;
	}

	public void configureForThread(final Map<IcfgLocation, IPredicate> locationPredicates,
			final IDomain analysisDomain) {
		mLocationPredicates = Objects.requireNonNull(locationPredicates);
		mAnalysisDomain = Objects.requireNonNull(analysisDomain);
	}

	public IPredicate getInitialStatePredicate(final String threadId) {
		final IcfgLocation entryLocation = mIcfg.getProcedureEntryNodes().get(threadId);

		if (threadId.equals(MAIN_THREAD)) {
			final IPredicate mainState = getMainThreadInitialState();
			return mTools.applyInterferences(mainState, entryLocation);
		}

		final Set<IPredicate> forkStates = collectForkStates(threadId);
		if (forkStates.isEmpty()) {
			return mTools.bottom();
		}
		IPredicate result = null;
		for (final IPredicate pred : forkStates) {
			result = result == null ? pred : mAnalysisDomain.join(result, pred);
		}
		return mTools.applyInterferences(result, entryLocation);
	}

	private IPredicate getMainThreadInitialState() {
		if (mGhostVariables == null) {
			return mTools.top();
		}
		return mTools.predicate(mGhostVariables.createInitialLocationState(MAIN_THREAD));
	}

	/*
	 * We model the initial state of a non-main thread by joining the state of all locations of other threads where this
	 * thread is forked
	 */
	private Set<IPredicate> collectForkStates(final String threadId) {
		final Set<IPredicate> states = new HashSet<>();
		final ConcurrencyInformation concInfo = mIcfg.getCfgSmtToolkit().getConcurrencyInformation();
		for (final IIcfgForkTransitionThreadCurrent<IcfgLocation> fork : concInfo.getThreadInstanceMap().keySet()) {
			if (!fork.getNameOfForkedProcedure().equals(threadId)) {
				continue;
			}
			final IPredicate forkState = mLocationPredicates.get(fork.getSource());
			if (forkState == null) {
				continue;
			}
			states.add(applyForkEffects(forkState, fork));
		}
		return states;
	}

	/*
	 * The initial state should see a thread that forks it at the position after the fork. However if we just take the
	 * state of that position, that state will already be open to interferences, including from this thread. so we need
	 * to model the atomic update of being forked without any other interferences happening. this is achieved by just
	 * taking the source state of the fork transition and updating the fork threads location
	 */
	private IPredicate applyForkEffects(final IPredicate forkState,
			final IIcfgForkTransitionThreadCurrent<IcfgLocation> fork) {
		if (mGhostVariables == null) {
			return forkState;
		}
		final String forkedThreadId = fork.getNameOfForkedProcedure();
		final String forkingTid = fork.getSource().getProcedure();
		final IcfgLocation forkedEntry = mGhostVariables.getEntryLocation(forkedThreadId);

		final IPredicate updated = mTools.addLocationUpdateForThread(forkState, forkingTid, fork.getTarget());
		return mTools.addLocationUpdateForThread(updated, forkedThreadId, forkedEntry);
	}
}
