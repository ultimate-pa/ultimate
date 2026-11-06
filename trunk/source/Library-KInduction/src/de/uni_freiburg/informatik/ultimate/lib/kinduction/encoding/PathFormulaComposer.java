/*
 * Copyright (C) 2026 University of Freiburg
 * Copyright (C) 2026 LMU Munich
 * Copyright (C) 2026 Max Barth (Max.Barth@lmu.de)
 *
 * This file is part of the ULTIMATE KInduction Library.
 *
 * The ULTIMATE KInduction Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE KInduction Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE KInduction Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE KInduction Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE KInduction Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.GenericLabeledGraph;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.PathExpressionComputer;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Concatenation;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.EmptySet;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Epsilon;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.IRegex;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.IRegexVisitor;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Literal;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Regex;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Star;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Union;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Composes all paths between two nodes of an acyclic graph, whose edges are transition formulas, into one transition
 * formula. {@link ProcedureSummaries} needs this for the summary of a procedure, and {@link PcTransitionSystem} for a
 * step without any variables of its own.
 *
 * @author Max Barth (max.barth@lmu.de)
 * @param <N>
 *            node type
 */
final class PathFormulaComposer<N> {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final ManagedScript mMgdScript;
	private final PathExpressionComputer<N, UnmodifiableTransFormula> mPathExpressions;
	private final RegexToTransFormula mEvaluator = new RegexToTransFormula();

	/**
	 * Creates a composer for one graph.
	 *
	 * @param edges
	 *            every node with its outgoing edges, each node before its successors. The script must not be locked
	 *            while this composes, since composing declares constants for auxiliary variables and takes the lock
	 *            itself.
	 */
	PathFormulaComposer(final IUltimateServiceProvider services, final ILogger logger, final ManagedScript mgdScript,
			final Map<N, List<Pair<UnmodifiableTransFormula, N>>> edges) {
		mServices = services;
		mLogger = logger;
		mMgdScript = mgdScript;
		// Linked sets and topological order: PathExpressionComputer numbers the nodes in the order of getNodes(), and
		// with a topological numbering its elimination has nothing to do and solve() is one forward pass in which
		// P(u,w) is just the union of the edges u -> w. That is the shape RegexToTransFormula factors completely.
		final GenericLabeledGraph<N, UnmodifiableTransFormula> graph =
				new GenericLabeledGraph<>(new LinkedHashSet<>(), new LinkedHashSet<>()) {
				};
		for (final N node : edges.keySet()) {
			graph.addNode(node);
		}
		for (final Map.Entry<N, List<Pair<UnmodifiableTransFormula, N>>> entry : edges.entrySet()) {
			for (final Pair<UnmodifiableTransFormula, N> edge : entry.getValue()) {
				graph.addEdge(entry.getKey(), edge.getFirst(), edge.getSecond());
			}
		}
		mPathExpressions = new PathExpressionComputer<>(graph);
	}

	/**
	 * The formula of all paths from {@code from} to {@code to}, {@code null} if there is none.
	 */
	UnmodifiableTransFormula pathsBetween(final N from, final N to) {
		return mEvaluator.evaluate(mPathExpressions.exprBetween(from, to));
	}

	/**
	 * Throws if the progress monitor says stop, e.g. because the toolchain's deadline has passed. Polled before every
	 * composition of formulas, since evaluating a path expression is still exponential in the worst case (see
	 * {@link RegexToTransFormula}). A pathological graph must not run past the deadline uninterrupted.
	 */
	private void checkCanceled(final String task) {
		if (!mServices.getProgressMonitorService().continueProcessing()) {
			throw new ToolchainCanceledException(PathFormulaComposer.class, task);
		}
	}

	/**
	 * One composition for a whole sequence rather than one per step: every composed formula declares a constant per
	 * auxiliary variable in the solver, so the intermediate results would cost a solver round trip each.
	 */
	private UnmodifiableTransFormula sequential(final List<UnmodifiableTransFormula> sequence) {
		if (sequence.size() == 1) {
			return sequence.get(0);
		}
		checkCanceled("composing the transition formulas of a path");
		return TransFormulaUtils.sequentialComposition(mLogger, mServices, mMgdScript, false, false, false,
				SimplificationTechnique.NONE, sequence);
	}

	/**
	 * Evaluates a path expression into one relational {@link UnmodifiableTransFormula}, or {@code null} if it describes
	 * no path ({@code null} is the algebraic zero). The cut graphs are acyclic, so {@link Star} cannot occur.
	 * <p>
	 * {@link PathExpressionComputer} builds its expressions with shared sub-objects: it extends the expression of every
	 * predecessor u of a node w by the edges u -> w, {@code F(w) = F(u1)·e1 ∪ F(u2)·e2}. Behind an if-then-else both
	 * alternatives start with the same object F(fork), so evaluating the expression as a tree composes F(fork) once per
	 * branch, and the work and the size of the formula double with every if-then-else in sequence. This visitor
	 * therefore never evaluates a union or a concatenation as a tree. It flattens a union into its alternatives and
	 * each alternative into its sequence of factors, and merges the alternatives into a {@link PrefixTrie} on their
	 * factors. Each common prefix is then evaluated once, followed by the union of what comes after it:
	 * {@code X·A ∪ X·B = X·(A ∪ B)}, which holds for the relational composition of transition formulas. The prefixes
	 * are spliced into one sequential composition rather than composed level by level, see
	 * {@link #appendSequence(PrefixTrie, List)}. For the series-parallel control flow of structured code this is
	 * linear. Sharing that is not a common prefix (e.g. a {@code goto} into a branch) is still evaluated once per path
	 * through it.
	 * <p>
	 * Do <b>not</b> memoize results on the regex object: the constructor of {@link UnmodifiableTransFormula} declares a
	 * constant per auxiliary variable, so handing the same composed formula to two compositions makes the second one
	 * declare those constants again and the solver rejects it ("Function c_aux_... is already defined").
	 */
	private final class RegexToTransFormula
			implements IRegexVisitor<UnmodifiableTransFormula, UnmodifiableTransFormula, Void> {

		private final Map<Union<UnmodifiableTransFormula>, List<IRegex<UnmodifiableTransFormula>>> mHeadExpansions =
				new IdentityHashMap<>();

		UnmodifiableTransFormula evaluate(final IRegex<UnmodifiableTransFormula> regex) {
			final List<UnmodifiableTransFormula> sequence = new ArrayList<>();
			if (!appendSequence(regex, sequence)) {
				return null;
			}
			return compose(sequence);
		}

		/**
		 * Appends formulas whose sequential composition is {@code regex}. A union or a concatenation is factored into a
		 * {@link PrefixTrie} first.
		 *
		 * @return {@code false} if {@code regex} describes no path; {@code sequence} is then incomplete
		 */
		private boolean appendSequence(final IRegex<UnmodifiableTransFormula> regex,
				final List<UnmodifiableTransFormula> sequence) {
			checkCanceled("evaluating a path expression");
			if (regex instanceof Union || regex instanceof Concatenation) {
				return appendSequence(trie(regex), sequence);
			}
			if (regex instanceof EmptySet) {
				return false;
			}
			if (!(regex instanceof Epsilon)) {
				sequence.add(regex.accept(this));
			}
			return true;
		}

		/**
		 * Appends the formulas of a trie. The common prefix is spliced into {@code sequence}, recursively, so a union
		 * that starts with the union of the preceding if-then-else does not compose that one again: a whole chain of
		 * if-then-elses becomes one sequential composition of its statements and its small branch unions. Composing the
		 * chain level by level instead would rename and declare the auxiliary variables of everything before a level
		 * again at every level, which is quadratic in the length of the chain.
		 *
		 * @return {@code false} if the trie describes no path; {@code sequence} is then incomplete
		 */
		private boolean appendSequence(final PrefixTrie node, final List<UnmodifiableTransFormula> sequence) {
			PrefixTrie current = node;
			while (!current.mEndsHere && current.mChildren.size() == 1) {
				final Pair<IRegex<UnmodifiableTransFormula>, PrefixTrie> only = current.mChildren.get(0);
				if (!appendSequence(only.getFirst(), sequence)) {
					return false;
				}
				current = only.getSecond();
			}
			if (current.mChildren.isEmpty()) {
				// Either every alternative ends here, or there was none at all.
				return current.mEndsHere;
			}
			final List<UnmodifiableTransFormula> alternatives = new ArrayList<>();
			if (current.mEndsHere) {
				alternatives.add(TransFormulaBuilder.getTrivialTransFormula(mMgdScript));
			}
			for (final Pair<IRegex<UnmodifiableTransFormula>, PrefixTrie> child : current.mChildren) {
				final List<UnmodifiableTransFormula> alternative = new ArrayList<>();
				if (appendSequence(child.getFirst(), alternative) && appendSequence(child.getSecond(), alternative)) {
					alternatives.add(compose(alternative));
				}
			}
			if (alternatives.isEmpty()) {
				return false;
			}
			checkCanceled("evaluating a path expression");
			sequence.add(LoopTreeFormulaBuilder.combineAlternatives(mLogger, mServices, mMgdScript, alternatives));
			return true;
		}

		private UnmodifiableTransFormula compose(final List<UnmodifiableTransFormula> sequence) {
			if (sequence.isEmpty()) {
				return TransFormulaBuilder.getTrivialTransFormula(mMgdScript);
			}
			return sequential(sequence);
		}

		/**
		 * Returns the alternatives of nested unions, in order, without the empty ones.
		 *
		 * @return the alternatives of nested unions, in order, without the empty ones
		 */
		private List<IRegex<UnmodifiableTransFormula>> alternatives(final IRegex<UnmodifiableTransFormula> regex) {
			final List<IRegex<UnmodifiableTransFormula>> result = new ArrayList<>();
			final Deque<IRegex<UnmodifiableTransFormula>> worklist = new ArrayDeque<>();
			worklist.push(regex);
			while (!worklist.isEmpty()) {
				final IRegex<UnmodifiableTransFormula> current = worklist.pop();
				if (current instanceof Union) {
					final Union<UnmodifiableTransFormula> union = (Union<UnmodifiableTransFormula>) current;
					worklist.push(union.getSecond());
					worklist.push(union.getFirst());
				} else if (!(current instanceof EmptySet)) {
					result.add(current);
				}
			}
			return result;
		}

		private PrefixTrie trie(final IRegex<UnmodifiableTransFormula> regex) {
			final PrefixTrie root = new PrefixTrie();
			for (final IRegex<UnmodifiableTransFormula> alternative : alternatives(regex)) {
				root.insert(factors(alternative));
			}
			return root;
		}

		/**
		 * Returns the factors of nested concatenations, in order, without the epsilons, and with a leading union
		 * replaced by its {@link #headExpansion}.
		 *
		 * @return the factors of nested concatenations, in order, without the epsilons, and with a leading union
		 *         replaced by its {@link #headExpansion}
		 */
		private List<IRegex<UnmodifiableTransFormula>> factors(final IRegex<UnmodifiableTransFormula> regex) {
			final List<IRegex<UnmodifiableTransFormula>> result = new ArrayList<>();
			final Deque<IRegex<UnmodifiableTransFormula>> worklist = new ArrayDeque<>();
			worklist.push(regex);
			while (!worklist.isEmpty()) {
				final IRegex<UnmodifiableTransFormula> current = worklist.pop();
				if (current instanceof Concatenation) {
					final Concatenation<UnmodifiableTransFormula> concatenation =
							(Concatenation<UnmodifiableTransFormula>) current;
					worklist.push(concatenation.getSecond());
					worklist.push(concatenation.getFirst());
				} else if (!(current instanceof Epsilon)) {
					result.add(current);
				}
			}
			if (!result.isEmpty() && result.get(0) instanceof Union) {
				final List<IRegex<UnmodifiableTransFormula>> expanded =
						new ArrayList<>(headExpansion((Union<UnmodifiableTransFormula>) result.get(0)));
				expanded.addAll(result.subList(1, result.size()));
				return expanded;
			}
			return result;
		}

		/**
		 * A union that does not start with the same factors as its sibling alternatives can still share a prefix with
		 * them: behind {@code if (a && b) X else Y}, Y is reached both from the test of a and from the test of b, so
		 * the expression of Y is a union whose alternatives start with the prefix P before the {@code if}, while the
		 * expression of X is a concatenation that starts with P as well. As a single factor, the union hides P, and P
		 * would be evaluated twice, once more for every such condition in sequence. So a leading union is replaced by
		 * the common prefix of its alternatives followed by one union of the rest. The expansion is cached per union
		 * object, so all alternatives that start with the same union start with the same factors.
		 *
		 * @return factors whose concatenation is {@code union}
		 */
		private List<IRegex<UnmodifiableTransFormula>> headExpansion(final Union<UnmodifiableTransFormula> union) {
			final List<IRegex<UnmodifiableTransFormula>> cached = mHeadExpansions.get(union);
			if (cached != null) {
				return cached;
			}
			PrefixTrie current = trie(union);
			final List<IRegex<UnmodifiableTransFormula>> result = new ArrayList<>();
			while (!current.mEndsHere && current.mChildren.size() == 1) {
				result.add(current.mChildren.get(0).getFirst());
				current = current.mChildren.get(0).getSecond();
			}
			if (result.isEmpty()) {
				// No common prefix: the union itself keeps its identity, so it can still be shared.
				result.add(union);
			} else if (!current.mChildren.isEmpty()) {
				result.add(toRegex(current));
			}
			mHeadExpansions.put(union, result);
			return result;
		}

		/**
		 * Returns the union of the alternatives below {@code node}.
		 *
		 * @return the union of the alternatives below {@code node}
		 */
		private IRegex<UnmodifiableTransFormula> toRegex(final PrefixTrie node) {
			IRegex<UnmodifiableTransFormula> result = node.mEndsHere ? Regex.epsilon() : null;
			for (final Pair<IRegex<UnmodifiableTransFormula>, PrefixTrie> child : node.mChildren) {
				final PrefixTrie rest = child.getSecond();
				final IRegex<UnmodifiableTransFormula> alternative =
						rest.mChildren.isEmpty() ? child.getFirst() : Regex.concat(child.getFirst(), toRegex(rest));
				result = result == null ? alternative : Regex.union(result, alternative);
			}
			return result;
		}

		@Override
		public UnmodifiableTransFormula visit(final Union<UnmodifiableTransFormula> union, final Void argument) {
			return evaluate(union);
		}

		@Override
		public UnmodifiableTransFormula visit(final Concatenation<UnmodifiableTransFormula> concatenation,
				final Void argument) {
			return evaluate(concatenation);
		}

		@Override
		public UnmodifiableTransFormula visit(final Star<UnmodifiableTransFormula> star, final Void argument) {
			throw new AssertionError("Unexpected cycle in the cut graph of a scope");
		}

		@Override
		public UnmodifiableTransFormula visit(final Literal<UnmodifiableTransFormula> literal, final Void argument) {
			return literal.getLetter();
		}

		@Override
		public UnmodifiableTransFormula visit(final Epsilon<UnmodifiableTransFormula> epsilon, final Void argument) {
			return TransFormulaBuilder.getTrivialTransFormula(mMgdScript);
		}

		@Override
		public UnmodifiableTransFormula visit(final EmptySet<UnmodifiableTransFormula> emptySet, final Void argument) {
			return null;
		}
	}

	/**
	 * The alternatives of a union, merged on their common prefixes; see {@link RegexToTransFormula}.
	 */
	private final class PrefixTrie {
		// Factors are compared by identity: the shared sub-objects are what makes prefixes common, and equals and
		// hashCode of the regex classes recurse through the whole expression, which costs as much as the tree
		// evaluation this avoids.
		private final Map<IRegex<UnmodifiableTransFormula>, PrefixTrie> mChildByFactor = new IdentityHashMap<>();
		// The same children in insertion order, so the formulas are composed in a deterministic order.
		private final List<Pair<IRegex<UnmodifiableTransFormula>, PrefixTrie>> mChildren = new ArrayList<>();
		// Whether an alternative ends at this node, i.e. the empty continuation belongs to the union.
		private boolean mEndsHere;

		void insert(final List<IRegex<UnmodifiableTransFormula>> factors) {
			PrefixTrie node = this;
			for (final IRegex<UnmodifiableTransFormula> factor : factors) {
				PrefixTrie child = node.mChildByFactor.get(factor);
				if (child == null) {
					child = new PrefixTrie();
					node.mChildByFactor.put(factor, child);
					node.mChildren.add(new Pair<>(factor, child));
				}
				node = child;
			}
			node.mEndsHere = true;
		}
	}
}
