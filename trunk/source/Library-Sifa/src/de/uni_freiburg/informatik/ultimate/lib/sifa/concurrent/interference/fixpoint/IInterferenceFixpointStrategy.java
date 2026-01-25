package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.fixpoint;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

/**
 * Computes fixpoint when applying interferences to a state.
 */
public interface IInterferenceFixpointStrategy {

	IPredicate computeFixpoint(IPredicate state, Set<IPredicate> interferences, IDomain domain,
			RelationalPredicatePostcondition postcondition);
}
