package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterference;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

record ThreadAnalysisContext(String threadId, IInterference interference, IDomain domain,
		RelationalPredicatePostcondition postcondition, boolean includeSelfInterference,
		List<String> sortedInterferenceThreadIds, Map<IcfgLocation, IPredicate> locationPredicates,
		Map<IcfgLocation, Set<String>> activeThreadIdsByLocation) {
}
