package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition.PreparedRelation;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats.Key;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;

final class InterferenceUtils {

	private InterferenceUtils() {
	}

	static List<PreparedRelation> prepareNonFalseRelations(final Collection<IPredicate> relations,
			final RelationalPredicatePostcondition postcondition) {
		final List<PreparedRelation> prepared = new ArrayList<>();
		for (final IPredicate relation : relations) {
			if (!SmtUtils.isFalseLiteral(relation.getFormula())) {
				prepared.add(postcondition.prepareRelation(relation));
			}
		}
		return prepared;
	}

	static IPredicate applyUntilFixpoint(final IPredicate state, final List<PreparedRelation> preparedRelations,
			final IDomain domain, final RelationalPredicatePostcondition postcondition, final int wideningThreshold,
			final SifaStats stats) {
		if (preparedRelations.isEmpty() || SmtUtils.isTrueLiteral(state.getFormula())
				|| SmtUtils.isFalseLiteral(state.getFormula())) {
			return state;
		}

		IPredicate current = state;
		IPredicate frontier = state;
		for (int iteration = 1;; iteration++) {
			boolean hasGenerated = false;
			IPredicate generated = current;
			for (final PreparedRelation prepared : preparedRelations) {
				final IPredicate post = postcondition.strongestPostcondition(frontier, prepared);
				if (SmtUtils.isFalseLiteral(post.getFormula())) {
					continue;
				}
				if (!hasGenerated) {
					generated = post;
					hasGenerated = true;
				} else {
					generated = domain.join(generated, post);
				}
			}
			if (!hasGenerated || domain.isSubsetEq(generated, current).isTrueForAbstraction()) {
				return current;
			}

			final IPredicate expanded = domain.join(current, generated);
			final IPredicate next;
			if (iteration > wideningThreshold) {
				next = domain.widen(current, expanded);
				stats.increment(Key.INTERFERENCE_INNER_WIDENINGS);
			} else {
				next = expanded;
			}
			if (domain.isSubsetEq(next, current).isTrueForAbstraction()) {
				return current;
			}
			current = next;
			frontier = generated;
		}
	}

	static <K> Map<K, IPredicate> widenBuckets(final Map<K, IPredicate> left, final Map<K, IPredicate> right,
			final IDomain domain) {
		final Map<K, IPredicate> widened = new HashMap<>();
		for (final K key : left.keySet()) {
			final IPredicate thisPred = left.get(key);
			final IPredicate otherPred = right.get(key);
			widened.put(key, otherPred == null ? thisPred : domain.widen(thisPred, otherPred));
		}
		for (final K key : right.keySet()) {
			widened.putIfAbsent(key, right.get(key));
		}
		return widened;
	}
}
