/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.function.UnaryOperator;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.CachedIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.CachedIndependenceRelation.IIndependenceCache;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.ConditionTransformingIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.DefaultIndependenceCache;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.DisjunctiveConditionalIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.ProtectedIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.UnionIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.abstraction.IAbstraction;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.abstraction.IndependenceRelationWithAbstraction;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.TransferrerWithVariableCache;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.DebugPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierUtils;

/**
 * Provides fluent API to create independence relations for software analysis. Usage of this API usually follows 3
 * steps:
 * <ol>
 * <li>Use a static method to create a new builder with a base independence relation.</li>
 * <li>Chain calls to instance methods to build a hierarchy of wrapper relations.</li>
 * <li>Call {@link IndependenceBuilder.ActionIndependenceBuilder#build()} to retrieve the constructed relation.</li>
 * </ol>
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters for the independence relation
 * @param <S>
 *            The type of conditions for the independence relation
 * @param <B>
 *            (Implementation detail used to provide fluent API, not relevant to callers)
 */
public class IndependenceBuilder<L, S, B extends IndependenceBuilder<L, S, B>> {
	private static final String UNCONDITIONAL_ERROR = "Condition transformation for unconditional relation is useless";

	protected final IIndependenceRelation<S, L> mRelation;
	protected final Function<IIndependenceRelation<S, L>, B> mCreator;

	private IndependenceBuilder(final IIndependenceRelation<S, L> relation,
			final Function<IIndependenceRelation<S, L>, B> creator) {
		mRelation = relation;
		mCreator = creator;
	}

	/**
	 * Constructs an independence relation as declared in the builder's fluent API.
	 *
	 * @return the newly constructed independence relation
	 */
	public IIndependenceRelation<S, L> build() {
		return mRelation;
	}

	/**
	 * Create a new instance, with a semantic independence relation as base. See
	 * {@link SemanticIndependenceRelation::new} for details.
	 */
	public static <L extends IAction> PredicateActionIndependenceBuilder.Impl<L> semantic(
			final IUltimateServiceProvider services, final ManagedScript mgdScript, final boolean conditional,
			final boolean symmetric) {
		return semantic(services, mgdScript, conditional, symmetric, null);
	}

	/**
	 * Create a new instance, with a semantic independence relation as base. See
	 * {@link SemanticIndependenceRelation::new} for details.
	 *
	 * @param mgdScript
	 *            This script is used for SMT checks
	 * @param transferrer
	 *            TransFormulas of input actions and the formulae of input conditions are assumed to not be created by
	 *            the given {@code mgdScript}, this is used to transfer them.
	 */
	public static <L extends IAction> PredicateActionIndependenceBuilder.Impl<L> semantic(
			final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final TransferrerWithVariableCache transferrer, final boolean conditional, final boolean symmetric) {
		return semantic(services, mgdScript, conditional, symmetric, transferrer);
	}

	/**
	 * Create a new instance, with a semantic independence relation as base. See
	 * {@link SemanticIndependenceRelation::new} for details.
	 */
	public static <L extends IAction> PredicateActionIndependenceBuilder.Impl<L> semantic(
			final IUltimateServiceProvider services, final ManagedScript mgdScript, final boolean conditional,
			final boolean symmetric, final TransferrerWithVariableCache transferrer) {
		return new PredicateActionIndependenceBuilder.Impl<>(
				new SemanticIndependenceRelation<>(services, mgdScript, conditional, symmetric, transferrer));
	}

	/**
	 * Create a new instance, with a syntactic independence relation as base.
	 */
	public static <L extends IAction, S> ActionIndependenceBuilder.Impl<L, S> syntactic() {
		return new ActionIndependenceBuilder.Impl<>(new SyntacticIndependenceRelation<>());
	}

	/**
	 * Create a new instance, with the given independence relation as base.
	 *
	 * @see IndependenceBuilder.ActionIndependenceBuilder#fromActionIndependence(IIndependenceRelation)
	 * @see IndependenceBuilder.PredicateActionIndependenceBuilder#fromPredicateActionIndependence(IIndependenceRelation)
	 */
	public static <L, S> Impl<L, S> fromIndependence(final IIndependenceRelation<S, L> relation) {
		return new Impl<>(relation);
	}

	/**
	 * Creates a new builder based on a given independence relation between {@link IAction}s, where the conditions are
	 * given as {@link IPredicate}s.
	 *
	 * @see IndependenceBuilder#fromIndependence(IIndependenceRelation)
	 * @see IndependenceBuilder.ActionIndependenceBuilder#fromActionIndependence(IIndependenceRelation)
	 */
	public static <L extends IAction> PredicateActionIndependenceBuilder.Impl<L>
			fromPredicateActionIndependence(final IIndependenceRelation<IPredicate, L> relation) {
		return new PredicateActionIndependenceBuilder.Impl<>(relation);
	}

	/**
	 * Creates a new builder based on a given independence relation between {@link IAction}s.
	 *
	 * @see IndependenceBuilder#fromIndependence(IIndependenceRelation)
	 * @see IndependenceBuilder.PredicateActionIndependenceBuilder#fromPredicateActionIndependence(IIndependenceRelation)
	 */
	public static <L extends IAction, S> ActionIndependenceBuilder.Impl<L, S>
			fromActionIndependence(final IIndependenceRelation<S, L> relation) {
		return new ActionIndependenceBuilder.Impl<>(relation);
	}

	/**
	 * Conditionally apply a builder transformation.
	 *
	 * @param condition
	 *            A condition to evaluate
	 * @param then
	 *            If the condition holds, apply this step. Otherwise do nothing.
	 */
	public B ifThen(final boolean condition, final Function<? super B, ? extends B> then) {
		return ifThenElse(condition, then, Function.identity());
	}

	/**
	 * Conditionally pick one of two builder transformations.
	 *
	 * @param condition
	 *            A condition to evaluate
	 * @param then
	 *            If the condition holds, apply this step
	 * @param otherwise
	 *            If the condition does not hold, apply this step
	 */
	public <C extends IndependenceBuilder<L, S, C>> C ifThenElse(final boolean condition,
			final Function<? super B, ? extends C> then, final Function<? super B, ? extends C> otherwise) {
		if (condition) {
			return then.apply(mCreator.apply(mRelation));
		}
		return otherwise.apply(mCreator.apply(mRelation));
	}

	/**
	 * Union the current independence relation with the given relation (the given relation is queried first).
	 */
	public B unionLeft(final IIndependenceRelation<S, L> relation) {
		return unionLeft(List.of(relation));
	}

	/**
	 * Union the current independence relation with the given relations (the given relations are queried in the given
	 * order, before the current relation).
	 */
	public B unionLeft(final List<IIndependenceRelation<S, L>> relations) {
		return union(relations, List.of());
	}

	/**
	 * Union the current independence relation with the given relation (the given relation is queried last).
	 */
	public B unionRight(final IIndependenceRelation<S, L> relation) {
		return unionRight(List.of(relation));
	}

	/**
	 * Union the current independence relation with the given relations (the given relations are queried in the given
	 * order, but after the current relation).
	 */
	public B unionRight(final List<IIndependenceRelation<S, L>> relations) {
		return union(List.of(), relations);
	}

	/**
	 * Union the current independence relation with the given relations.
	 *
	 * @see ActionIndependenceBuilder#withSyntacticCheck() for a common special case.
	 *
	 * @param left
	 *            A list of independence relations used as operands in the union. These relations are queried in the
	 *            given order, before the current relation is queried.
	 * @param right
	 *            A list of independence relations used as operands in the union. These relations are queried in the
	 *            given order, after the current relation is queried.
	 */
	public B union(final List<IIndependenceRelation<S, L>> left, final List<IIndependenceRelation<S, L>> right) {
		final ArrayList<IIndependenceRelation<S, L>> relations = new ArrayList<>(left.size() + 1 + right.size());
		relations.addAll(left);
		relations.add(mRelation);
		relations.addAll(right);

		return mCreator.apply(new UnionIndependenceRelation<>(relations));
	}

	/**
	 * Ensures the current relation is unconditional. If it already is, no change is made.
	 *
	 * @see IndependenceBuilder.Impl#unconditional()
	 * @see IndependenceBuilder.ActionIndependenceBuilder.Impl#unconditional()
	 * @see IndependenceBuilder.PredicateActionIndependenceBuilder.Impl#unconditional()
	 */
	public B ensureUnconditional() {
		if (mRelation.isConditional()) {
			return mCreator.apply(ConditionTransformingIndependenceRelation.<S, L> unconditional(mRelation));
		}
		return mCreator.apply(mRelation);
	}

	/**
	 * Wrap the current relation in a caching layer.
	 */
	public B cached() {
		return cached(new DefaultIndependenceCache<>());
	}

	/**
	 * Wrap the current relation in a caching layer that uses the given cache.
	 */
	public B cached(final IIndependenceCache<S, L> cache) {
		return mCreator.apply(new CachedIndependenceRelation<>(mRelation, cache));
	}

	/**
	 * Filters the conditions passed to the relation. Conditions not matching the filter criterion are replaced by
	 * {@code null}, i.e., unconditional independence checks.
	 *
	 * @param filter
	 *            The filter criterion applied to conditions.
	 */
	public B withFilteredConditions(final Predicate<S> filter) {
		if (mRelation.isConditional()) {
			return mCreator
					.apply(new ConditionTransformingIndependenceRelation<>(mRelation, x -> filter.test(x) ? x : null));
		}
		return mCreator.apply(mRelation);
	}

	/**
	 * Sub-class needed for the fluent API. Callers typically do not refer to this type explicitly, but may call its
	 * methods.
	 */
	public static final class Impl<L, S> extends IndependenceBuilder<L, S, Impl<L, S>> {
		private Impl(final IIndependenceRelation<S, L> relation) {
			super(relation, Impl::new);
		}

		/**
		 * Wraps the current relation in a layer that ensures it is unconditional. This also allows changing the type of
		 * conditions.
		 *
		 * @see IndependenceBuilder#ensureUnconditional()
		 * @see IndependenceBuilder.ActionIndependenceBuilder.Impl#unconditional()
		 * @see IndependenceBuilder.PredicateActionIndependenceBuilder.Impl#unconditional()
		 */
		public <T> Impl<L, T> unconditional() {
			return new Impl<>(ConditionTransformingIndependenceRelation.unconditional(mRelation));
		}

		/**
		 * Wraps the current relation in a layer that transforms conditions. Must only be called for conditional
		 * relations.
		 *
		 * @see IndependenceBuilder.ActionIndependenceBuilder.Impl#withTransformedConditions(Function)
		 * @see IndependenceBuilder.PredicateActionIndependenceBuilder.Impl#withTransformedConditions(Function)
		 * @see IndependenceBuilder.PredicateActionIndependenceBuilder.Impl#withTransformedPredicates(Function)
		 */
		public <T> Impl<L, T> withTransformedConditions(final Function<T, S> transformer) {
			assert mRelation.isConditional() : UNCONDITIONAL_ERROR;
			return new Impl<>(new ConditionTransformingIndependenceRelation<>(mRelation, transformer));
		}
	}

	/**
	 * Sub-class needed for the fluent API. Callers typically do not refer to this type explicitly, but may call its
	 * methods.
	 */
	public abstract static class ActionIndependenceBuilder<L extends IAction, S, B extends ActionIndependenceBuilder<L, S, B>>
			extends IndependenceBuilder<L, S, B> {
		protected ActionIndependenceBuilder(final IIndependenceRelation<S, L> relation,
				final Function<IIndependenceRelation<S, L>, B> creator) {
			super(relation, creator);
		}

		/**
		 * Combines the current relation with a syntactic independence relation. This is typically done for semantic
		 * independence relations, as the syntactic check provides a cheap sufficient condition for semantic
		 * independence.
		 */
		public B withSyntacticCheck() {
			return unionLeft(new SyntacticIndependenceRelation<>());
		}

		/**
		 * Ensures only actions of different threads are considered independent.
		 */
		public B threadSeparated() {
			return mCreator.apply(new ThreadSeparatingIndependenceRelation<>(mRelation));
		}

		public <H> B withAbstraction(final IAbstraction<H, L> abstraction, final H level) {
			if (abstraction == null) {
				return mCreator.apply(mRelation);
			}
			return mCreator.apply(new IndependenceRelationWithAbstraction<>(mRelation, abstraction, level));
		}

		/**
		 * Ensures only actions with quantifier-free transition formulas are queried for independence. IF an action
		 * contains quantifiers, {@code UNKNOWN} is returned instead.
		 */
		public B protectAgainstQuantifiers() {
			return mCreator.apply(new ProtectedIndependenceRelation<>(mRelation,
					a -> QuantifierUtils.isQuantifierFree(a.getTransformula().getFormula())));
		}

		/**
		 * Sub-class needed for the fluent API. Callers typically do not refer to this type explicitly, but may call its
		 * methods.
		 */
		public static final class Impl<L extends IAction, S> extends ActionIndependenceBuilder<L, S, Impl<L, S>> {
			private Impl(final IIndependenceRelation<S, L> relation) {
				super(relation, Impl::new);
			}

			/**
			 * Wraps the current relation in a layer that ensures it is unconditional. This also allows changing the
			 * type of conditions.
			 *
			 * @see IndependenceBuilder#ensureUnconditional()
			 * @see IndependenceBuilder.Impl#unconditional()
			 * @see IndependenceBuilder.PredicateActionIndependenceBuilder.Impl#unconditional()
			 */
			public <T> Impl<L, T> unconditional() {
				return new Impl<>(ConditionTransformingIndependenceRelation.unconditional(mRelation));
			}

			/**
			 * Wraps the current relation in a layer that transforms conditions. Must only be called for conditional
			 * relations.
			 *
			 * @see IndependenceBuilder.Impl#withTransformedConditions(Function)
			 * @see IndependenceBuilder.PredicateActionIndependenceBuilder.Impl#withTransformedConditions(Function)
			 * @see IndependenceBuilder.PredicateActionIndependenceBuilder.Impl#withTransformedPredicates(Function)
			 */
			public <T> Impl<L, T> withTransformedConditions(final Function<T, S> transformer) {
				assert mRelation.isConditional() : UNCONDITIONAL_ERROR;
				return new Impl<>(new ConditionTransformingIndependenceRelation<>(mRelation, transformer));
			}
		}
	}

	/**
	 * Sub-class needed for the fluent API. Callers typically do not refer to this type explicitly, but may call its
	 * methods.
	 */
	public static abstract class PredicateActionIndependenceBuilder<L extends IAction, B extends PredicateActionIndependenceBuilder<L, B>>
			extends ActionIndependenceBuilder<L, IPredicate, B> {

		protected PredicateActionIndependenceBuilder(final IIndependenceRelation<IPredicate, L> relation,
				final Function<IIndependenceRelation<IPredicate, L>, B> creator) {
			super(relation, creator);
		}

		/**
		 * Adds a condition elimination layer to the current independence relation, if it is conditional. Does nothing
		 * if the current relation is unconditional.
		 *
		 * @param isInconsistent
		 *            An efficient check for inconsistency.
		 */
		public B withConditionElimination(final Predicate<IPredicate> isInconsistent) {
			if (mRelation.isConditional()) {
				return mCreator.apply(new SemanticConditionEliminator<>(mRelation, isInconsistent));
			}
			return mCreator.apply(mRelation);
		}

		/**
		 * Sub-class needed for the fluent API. Callers typically do not refer to this type explicitly, but may call its
		 * methods.
		 */
		public static final class Impl<L extends IAction> extends PredicateActionIndependenceBuilder<L, Impl<L>> {
			private Impl(final IIndependenceRelation<IPredicate, L> relation) {
				super(relation, Impl::new);
			}

			/**
			 * Wraps the current relation in a layer that ensures it is unconditional. This also allows changing the
			 * type of conditions.
			 *
			 * @see IndependenceBuilder#ensureUnconditional()
			 * @see IndependenceBuilder.Impl#unconditional()
			 * @see IndependenceBuilder.ActionIndependenceBuilder.Impl#unconditional()
			 */
			public <T> ActionIndependenceBuilder.Impl<L, T> unconditional() {
				return new ActionIndependenceBuilder.Impl<>(
						ConditionTransformingIndependenceRelation.unconditional(mRelation));
			}

			/**
			 * Wraps the current relation in a layer that transforms conditions. Must only be called for conditional
			 * relations.
			 *
			 * @see IndependenceBuilder.Impl#withTransformedConditions(Function)
			 * @see IndependenceBuilder.ActionIndependenceBuilder.Impl#withTransformedConditions(Function)
			 * @see IndependenceBuilder.PredicateActionIndependenceBuilder.Impl#withTransformedPredicates(Function)
			 */
			public <T> ActionIndependenceBuilder.Impl<L, T>
					withTransformedConditions(final Function<T, IPredicate> transformer) {
				assert mRelation.isConditional() : UNCONDITIONAL_ERROR;
				return new ActionIndependenceBuilder.Impl<>(
						new ConditionTransformingIndependenceRelation<>(mRelation, transformer));
			}

			/**
			 * Wraps the current relation in a layer that transforms the condition predicates. Must only be called for
			 * conditional relations.
			 *
			 * @see IndependenceBuilder.Impl#withTransformedConditions(Function)
			 * @see IndependenceBuilder.ActionIndependenceBuilder.Impl#withTransformedConditions(Function)
			 * @see IndependenceBuilder.PredicateActionIndependenceBuilder.Impl#withTransformedConditions(Function)
			 */
			public Impl<L> withTransformedPredicates(final UnaryOperator<IPredicate> transformer) {
				assert mRelation.isConditional() : UNCONDITIONAL_ERROR;
				return new Impl<>(new ConditionTransformingIndependenceRelation<>(mRelation, transformer));
			}

			/**
			 * Wraps the current relation in a layer that ensures that instances of {@link DebugPredicate} are not used
			 * as conditions (i.e., they are replaced by the condition null).
			 */
			public Impl<L> ignoreDebugPredicates() {
				if (mRelation.isConditional()) {
					return withFilteredConditions(DebugPredicate.class::isInstance);
				}
				return this;
			}

			/**
			 * Splits a condition into multiple parts ("disjuncts"), and checks independence for each disjunct
			 * separately. If any disjunct induces independence, then the original condition is considered to induce
			 * independence.
			 */
			public <C extends Collection<IPredicate>> Impl<L>
					withDisjunctivePredicates(final Function<IPredicate, C> getDisjuncts) {
				if (mRelation.isConditional()) {
					return new Impl<>(new ConditionTransformingIndependenceRelation<>(
							new DisjunctiveConditionalIndependenceRelation<>(mRelation), getDisjuncts));
				}
				return this;
			}
		}
	}
}
