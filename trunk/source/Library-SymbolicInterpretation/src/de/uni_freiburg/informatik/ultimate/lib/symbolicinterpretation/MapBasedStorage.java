package de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

/**
 * Stores predicates for locations of interest.
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
public class MapBasedStorage implements ILoiPredicateStorage {

	private final IDomain mDomain;
	private final SymbolicTools mTools;
	private final ILogger mLogger;
	private final Map<IcfgLocation, IPredicate> mPredicatesForLoi = new HashMap<>();

	public MapBasedStorage(final Collection<IcfgLocation> locationsOfInterest,
			final IDomain domain, final SymbolicTools tools, final ILogger logger) {
		mDomain = domain;
		mTools = tools;
		mLogger = logger;
		initPredicates(locationsOfInterest);
	}

	private void initPredicates(final Collection<IcfgLocation> locationsOfInterest) {
		final IPredicate bottom = mTools.bottom();
		locationsOfInterest.forEach(loi -> mPredicatesForLoi.put(loi, bottom));
	}

	@Override
	public void storePredicateIfLoi(final IcfgLocation location, final IPredicate addPred) {
		mPredicatesForLoi.computeIfPresent(location,
				(loi, oldPred) -> joinLoiPredicate(loi, oldPred, addPred));
	}

	private IPredicate joinLoiPredicate(final IcfgLocation loi, final IPredicate oldPred, final IPredicate addPred) {
		logBeforeRegisterLoi(loi, addPred);
		final IPredicate newPred = mDomain.join(oldPred, addPred);
		logAfterRegisterLoi(loi, addPred, newPred);
		return newPred;
	}

	// TODO change logging so that we can use this class even when
	// LOIs from this class are different from the user's LOIs, for instance in a ICallSummarizer

	private void logBeforeRegisterLoi(final IcfgLocation loi, final IPredicate addPred) {
		mLogger.debug("LOI %s received the predicate %s", loi, addPred);
	}

	private void logAfterRegisterLoi(final IcfgLocation loi, final IPredicate addedPred, final IPredicate newPred) {
		if (addedPred == newPred) {
			mLogger.debug("Updated predicate for LOI %s is identical", loi);
		} else {
			mLogger.debug("Updated predicate for LOI %s is %s", loi, newPred);
		}
	}

	public Map<IcfgLocation, IPredicate> getMap() {
		return mPredicatesForLoi;
	}
}
