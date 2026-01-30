package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.proofchecking;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

/**
 * Checks stability under interferences: SP(P, I) ⊆ P for all predicates P and interferences I.
 */
public class InterferenceFreedomCheck {

	private final RelationalPredicatePostcondition mPostcondition;
	private final IDomain mDomain;

	public InterferenceFreedomCheck(final RelationalPredicatePostcondition postcondition, final IDomain domain) {
		mPostcondition = postcondition;
		mDomain = domain;
	}

	public ProofCheckResult check(final Map<IcfgLocation, IPredicate> locationPredicates,
			final IInterferenceAbstraction interferences, final String threadId) {
		final Set<IPredicate> otherInterferences = interferences.getInterferencesForOtherThreads(threadId);

		if (otherInterferences.isEmpty()) {
			return ProofCheckResult.valid();
		}

		final List<String> violations = new ArrayList<>();

		for (final Map.Entry<IcfgLocation, IPredicate> entry : locationPredicates.entrySet()) {
			final IcfgLocation location = entry.getKey();
			final IPredicate predicate = entry.getValue();

			for (final IPredicate interference : otherInterferences) {
				final IPredicate postState = mPostcondition.strongestPostcondition(predicate, interference);

				if (!mDomain.isSubsetEq(postState, predicate).isTrueForAbstraction()) {
					violations.add(String.format("Location %s not stable: P=%s, I=%s", location,
							predicate.getFormula(), interference.getFormula()));
				}
			}
		}

		return violations.isEmpty() ? ProofCheckResult.valid() : ProofCheckResult.invalid(violations);
	}

	public ProofCheckResult checkAllThreads(final Map<String, Map<IcfgLocation, IPredicate>> allLocationPredicates,
			final IInterferenceAbstraction interferences) {
		final List<String> allViolations = new ArrayList<>();

		for (final Map.Entry<String, Map<IcfgLocation, IPredicate>> entry : allLocationPredicates.entrySet()) {
			final ProofCheckResult result = check(entry.getValue(), interferences, entry.getKey());
			if (!result.isValid()) {
				allViolations.addAll(result.getViolations());
			}
		}

		return allViolations.isEmpty() ? ProofCheckResult.valid() : ProofCheckResult.invalid(allViolations);
	}
}
