package de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.vpdomain;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.datastructures.CongruenceClosure;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.IPartialComparator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.PartialOrderCache;

public class WeqCcManager<NODE extends IEqNodeIdentifier<NODE>> {

	private final CCManager<NODE> mCcManager;

	public WeqCcManager(final IPartialComparator<CongruenceClosure<NODE>> ccComparator) {
		mCcManager = new CCManager<>(ccComparator);
	}

	WeqCongruenceClosure<NODE> getWeqMeet(final CongruenceClosure<NODE> cc1,
			final WeqCongruenceClosure<NODE> cc2, final CongruenceClosure<NODE>.RemoveElement remInfo) {

		final WeqCongruenceClosure<NODE> result;
		if (remInfo == null) {
			result = cc2.meetRec(cc1);
		} else {
			assert false : "do we need this case?";
			result = null;
		}
		if (result.isInconsistent()) {
			return result;
		}
		return result;
	}

	public WeqCongruenceClosure<NODE> getWeqMeet(final CongruenceClosure<NODE> cc1,
			final WeqCongruenceClosure<NODE> cc2) {
		return getWeqMeet(cc1, cc2, null);
	}

	public Set<CongruenceClosure<NODE>> filterRedundantCcs(final Set<CongruenceClosure<NODE>> ccs) {
		return mCcManager.filterRedundantCcs(ccs);
	}

	public IPartialComparator<CongruenceClosure<NODE>> getCcComparator() {
		return mCcManager.getCcComparator();
	}

	public CongruenceClosure<NODE> getMeet(final CongruenceClosure<NODE> cc1, final CongruenceClosure<NODE> cc2,
			final CongruenceClosure<NODE>.RemoveElement elementCurrentlyBeingRemoved) {
		return mCcManager.getMeet(cc1, cc2, elementCurrentlyBeingRemoved);
	}

	public Set<CongruenceClosure<NODE>> filterRedundantCcs(final Set<CongruenceClosure<NODE>> ccs,
			final PartialOrderCache<CongruenceClosure<NODE>> ccPoCache) {
		return mCcManager.filterRedundantCcs(ccs, ccPoCache);
	}
}
