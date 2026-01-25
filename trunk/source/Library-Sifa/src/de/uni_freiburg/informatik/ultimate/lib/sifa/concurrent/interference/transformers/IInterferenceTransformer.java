package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.transformers;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceAbstraction;

/**
 * Transforms interference predicates (e.g., remove pre-state constraints, simplify).
 */
public interface IInterferenceTransformer {

	IPredicate transformPredicate(IPredicate interference);

	default InterferenceAbstraction transform(final InterferenceAbstraction interferences) {
		final Map<String, Set<IPredicate>> result = new HashMap<>();
		for (final String threadId : interferences.getThreadIds()) {
			final Set<IPredicate> transformed = interferences.getInterferencesProducedBy(threadId).stream()
					.map(this::transformPredicate).collect(Collectors.toSet());
			result.put(threadId, transformed);
		}
		return InterferenceAbstraction.of(result);
	}

	static IInterferenceTransformer identity() {
		return interference -> interference;
	}
}
