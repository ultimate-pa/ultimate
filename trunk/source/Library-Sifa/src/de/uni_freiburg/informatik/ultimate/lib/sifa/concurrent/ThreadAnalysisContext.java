package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterference;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceCollection;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

record ThreadAnalysisContext(String threadId, InterferenceCollection interferences, IDomain interferenceDomain,
		RelationalPredicatePostcondition postcondition, boolean includeSelfInterference,
		List<String> sortedInterferenceThreadIds, Map<IcfgLocation, IPredicate> locationPredicates,
		Map<IcfgLocation, List<IInterference>> applicableInterferencesByLocation) {
}
