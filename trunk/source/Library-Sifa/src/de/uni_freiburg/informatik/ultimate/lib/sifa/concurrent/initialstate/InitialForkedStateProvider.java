package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.initialstate;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ConcurrencyInformation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

// TODO: could add precision by tracking fork order
public class InitialForkedStateProvider {

	private final IIcfg<IcfgLocation> mIcfg;
	private final String mMainThread;
	private final Map<IcfgLocation, IPredicate> mLocationPredicates;
	private final IDomain mDomain;
	private final SymbolicTools mTools;

	public InitialForkedStateProvider(final IIcfg<IcfgLocation> icfg, final String mainThread,
			final Map<IcfgLocation, IPredicate> locationPredicates, final IDomain domain, final SymbolicTools tools) {
		mIcfg = icfg;
		mMainThread = mainThread;
		mLocationPredicates = locationPredicates;
		mDomain = domain;
		mTools = tools;
	}

	public IPredicate getInitialState(final String threadId) {
		if (threadId.equals(mMainThread)) {
			return mTools.top();
		}

		final Set<IPredicate> forkStates = collectForkStates(threadId);
		if (forkStates.isEmpty()) {
			return mTools.bottom();
		}

		return joinAll(forkStates);
	}

	private Set<IPredicate> collectForkStates(final String threadId) {
		final Set<IPredicate> states = new HashSet<>();
		final ConcurrencyInformation concInfo = mIcfg.getCfgSmtToolkit().getConcurrencyInformation();

		for (final IIcfgForkTransitionThreadCurrent<IcfgLocation> fork : concInfo.getThreadInstanceMap().keySet()) {
			if (!fork.getNameOfForkedProcedure().equals(threadId)) {
				continue;
			}
			final IcfgLocation forkLocation = fork.getSource();
			final IPredicate forkState = mLocationPredicates.get(forkLocation);
			if (forkState != null) {
				states.add(forkState);
			}
		}
		return states;
	}

	private IPredicate joinAll(final Set<IPredicate> predicates) {
		IPredicate result = null;
		for (final IPredicate pred : predicates) {
			result = result == null ? pred : mDomain.join(result, pred);
		}
		return result;
	}
}
