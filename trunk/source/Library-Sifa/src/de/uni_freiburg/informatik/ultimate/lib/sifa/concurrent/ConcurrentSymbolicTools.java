package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ConcurrencyInformation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;

public class ConcurrentSymbolicTools extends SymbolicTools {

	private static final String MAIN_THREAD = "ULTIMATE.start";

	private final IIcfg<IcfgLocation> mIcfg;

	private String mCurrentThreadId;
	private IInterferenceAbstraction mInterferences;
	private Map<IcfgLocation, IPredicate> mLocationPredicates;
	private IDomain mDomain;

	// TODO: Setting ob wir locations und threadcounter wollen, dann als switch ob, nicht nur boolean, sondern welche
	// abstraction
	public ConcurrentSymbolicTools(final IUltimateServiceProvider services, final SifaStats stats,
			final IIcfg<IcfgLocation> icfg, final SimplificationTechnique simplification,
			final IIcfgSymbolTable symbolTable) {
		super(services, stats, icfg, simplification, symbolTable);
		mIcfg = icfg;
	}

	public void configureForThread(final String threadId, final IInterferenceAbstraction interferences,
			final Map<IcfgLocation, IPredicate> locationPredicates, final IDomain domain) {
		mCurrentThreadId = threadId;
		mInterferences = interferences;
		mLocationPredicates = locationPredicates;
		mDomain = domain;
	}

	// Main thread: top(). Forked threads: join of predicates at fork locations.
	@Override
	public IPredicate post(final IPredicate input, final IIcfgTransition<IcfgLocation> transition) {
		final IPredicate postState = super.post(input, transition);
		if (mInterferences != null && mCurrentThreadId != null) {
			// TODO: post: exists loc post(phi, st) AND loc = alpha(loc')
			return mInterferences.applyToState(postState, mCurrentThreadId, mDomain);
		}
		return postState;
	}

	public IPredicate getInitialStatePredicate(final String threadId) {
		if (threadId.equals(MAIN_THREAD)) {
			return top();
		}
		// TODO: could add precision by tracking fork order
		final Set<IPredicate> forkStates = collectForkStates(threadId);
		if (forkStates.isEmpty()) {
			return bottom();
		}
		IPredicate result = null;
		for (final IPredicate pred : forkStates) {
			result = result == null ? pred : mDomain.join(result, pred);
		}
		return result;
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
				states.add(forkState);
			}
		}
		return states;
	}
}
