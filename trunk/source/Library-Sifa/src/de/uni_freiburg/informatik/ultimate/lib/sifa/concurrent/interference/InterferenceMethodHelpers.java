package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.function.BiFunction;
import java.util.function.BiPredicate;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public final class InterferenceMethodHelpers {

	private InterferenceMethodHelpers() {
	}

	public static IPredicate falsePredicate(final BasicPredicateFactory predicateFactory,
			final ManagedScript managedScript) {
		return predicateFactory.newPredicate(managedScript.getScript().term("false"));
	}

	public static boolean shouldSkipTrivialPredicate(final IPredicate predicate) {
		return SmtUtils.isTrueLiteral(predicate.getFormula()) || SmtUtils.isFalseLiteral(predicate.getFormula());
	}

	public static IPredicate combine(final IPredicate left, final IPredicate right, final ManagedScript managedScript,
			final BasicPredicateFactory predicateFactory) {
		final Term combined = SmtUtils.andWithExtendedLocalSimplification(managedScript.getScript(),
				left.getFormula(), right.getFormula());
		return predicateFactory.newPredicate(combined);
	}

	public static IPredicate or(final IPredicate left, final IPredicate right, final ManagedScript managedScript,
			final BasicPredicateFactory predicateFactory) {
		return predicateFactory.newPredicate(
				SmtUtils.or(managedScript.getScript(), left.getFormula(), right.getFormula()));
	}

	public static <K, V> boolean isSubsumed(final Map<K, V> left, final Map<K, V> right,
			final BiPredicate<V, V> groupSubsumer) {
		for (final Entry<K, V> entry : left.entrySet()) {
			final V otherGroup = right.get(entry.getKey());
			if (otherGroup == null || !groupSubsumer.test(entry.getValue(), otherGroup)) {
				return false;
			}
		}
		return true;
	}

	public static <K, V> Map<K, V> widen(final Map<K, V> left, final Map<K, V> right,
			final BiFunction<V, V, V> widener) {
		final Map<K, V> widened = new LinkedHashMap<>();
		for (final Entry<K, V> entry : left.entrySet()) {
			final V otherGroup = right.get(entry.getKey());
			widened.put(entry.getKey(),
					otherGroup == null ? entry.getValue() : widener.apply(entry.getValue(), otherGroup));
		}
		for (final Entry<K, V> entry : right.entrySet()) {
			widened.putIfAbsent(entry.getKey(), entry.getValue());
		}
		return widened;
	}

	public static <T> IPredicate applyGroup(final Collection<T> groupValues, final Function<T, IPredicate> applicator,
			final IDomain domain,
			final IPredicate falsePredicate) {
		boolean hasResult = false;
		IPredicate result = falsePredicate;
		for (final T item : groupValues) {
			final IPredicate post = applicator.apply(item);
			if (de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.isFalseLiteral(post.getFormula())) {
				continue;
			}
			if (!hasResult) {
				result = post;
				hasResult = true;
			} else {
				result = domain.join(result, post);
			}
		}
		return hasResult ? result : falsePredicate;
	}
}
