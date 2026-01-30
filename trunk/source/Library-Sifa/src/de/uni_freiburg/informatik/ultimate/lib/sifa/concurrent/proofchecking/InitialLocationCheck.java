package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.proofchecking;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;

/**
 * Checks that initial locations have predicate "true".
 */
public class InitialLocationCheck {

	public static ProofCheckResult check(final IIcfg<IcfgLocation> icfg,
			final Map<IcfgLocation, IPredicate> locationPredicates) {
		final List<String> violations = new ArrayList<>();

		for (final IcfgLocation initLoc : icfg.getInitialNodes()) {
			final IPredicate predicate = locationPredicates.get(initLoc);
			if (predicate == null || !SmtUtils.isTrueLiteral(predicate.getFormula())) {
				violations.add("Initial location " + initLoc + " is not true");
			}
		}

		return violations.isEmpty() ? ProofCheckResult.valid() : ProofCheckResult.invalid(violations);
	}
}
