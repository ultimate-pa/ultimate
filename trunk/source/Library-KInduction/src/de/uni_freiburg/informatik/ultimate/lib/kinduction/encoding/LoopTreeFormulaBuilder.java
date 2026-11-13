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
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Given a graph whose edges are transition formulas, cuts it into the graphs {@link PcTransitionSystem} needs, for
 * programs with no loop, any number of sequential loops, and arbitrarily <b>nested</b> loops.
 * <p>
 * The result is a tree of {@link Scope}s. The root scope is the whole program, every other scope is one loop. A scope's
 * <em>cut graph</em> is acyclic and holds all loop-free paths between the places a step through the scope can start and
 * end: the program's start in the root and the scope's own heads in a loop, the heads of its directly nested loops, the
 * error/accepting states, and every state the scope can leave to (e.g. by a {@code break} out of a loop). The root
 * scope of a program without a loop has only paths from the start to an error. The parts before and after a loop are
 * paths to and from its heads in the scope around it, and the body of a loop is the cut graph of its own scope. The
 * paths are not composed: {@link PcTransitionSystem} encodes the graph as it is, so its size is what a step costs.
 * <p>
 * Loops are found structurally (strongly connected components, recursively with the heads removed), so no annotation is
 * required. Several entry and exit transitions per head are supported.
 *
 * <h2>Loops with several heads</h2>
 *
 * The heads of a loop are <b>all</b> the states it is entered at from outside it. A reducible loop has one; irreducible
 * control flow (a {@code goto} into the middle of a loop, or an abstraction in which one loop head location has split
 * into several states) has more, and is supported rather than rejected. An iteration can start at every head and come
 * back round to every head, so a scope with the heads {@code h1, h2} has steps from {@code h1} to {@code h1}, from
 * {@code h1} to {@code h2}, from {@code h2} to {@code h1} and from {@code h2} to {@code h2}.
 * <p>
 * The cross steps are not an extra. An iteration from {@code h1} to {@code h2} has no other representation, because in
 * the enclosing scope both heads are sealed (they are nodes with no outgoing edges) and everything between them is an
 * interior state that is not a node there at all. Taking every entry state as a head is also what keeps the recursion
 * correct, see invariant (I1) at {@code findHeads}.
 * <p>
 * <h2>Procedure calls</h2>
 *
 * The graph has no call and no return transition, since it has no stack. A call's transition formula is only the
 * parameter assignment and a return's only the assignment of the result, so using them as ordinary edges would get the
 * scoping of oldvars, modifiable globals and the callee's locals wrong, and it would admit paths that leave through one
 * call site and come back at another, splicing away everything in between. {@link ProcedureSummaries} resolves every
 * call site before this class sees the graph: into an edge for the whole call-to-return span, or, for a callee that
 * contains a loop, into a copy of the callee per call site with an edge for the call and one for the return. The copies
 * are distinct nodes, so the splicing cannot happen, and the callee's loop is found by the ordinary SCC search as a
 * nested loop of the caller's scope.
 *
 * <h2>How to use</h2>
 *
 * Construct the builder, call {@link #build()} once, and read the graphs off the resulting tree of {@link Scope}s, or,
 * for a graph without a loop, call {@link #buildLoopFreeFormula()} for the formula of all its paths. All formulas live
 * in the {@link ManagedScript} passed to the constructor. That script must <b>not</b> be locked while
 * {@link #buildLoopFreeFormula()} runs: composing transition formulas declares constants for their aux vars and
 * therefore acquires the lock itself. Lock the script afterwards, once all formulas exist, to use them in a solver.
 *
 * @param <STATE>
 *            node type of the graph
 */
public class LoopTreeFormulaBuilder<STATE> {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final ManagedScript mMgdScript;
	private final Map<STATE, Map<STATE, UnmodifiableTransFormula>> mEdges;
	private final Set<STATE> mInitStates;
	private final Collection<STATE> mFinalStates;

	private final Map<STATE, Set<STATE>> mPredecessors = new HashMap<>();

	/**
	 * @param edges
	 *            every node with an outgoing edge, with its successors and the formula of the edge to each
	 * @param initStates
	 *            the nodes a run starts at
	 * @param finalStates
	 *            the accepting nodes
	 */
	public LoopTreeFormulaBuilder(final IUltimateServiceProvider services, final ILogger logger,
			final ManagedScript mgdScript, final Map<STATE, Map<STATE, UnmodifiableTransFormula>> edges,
			final Set<STATE> initStates, final Collection<STATE> finalStates) {
		mServices = services;
		mLogger = logger;
		mMgdScript = mgdScript;
		mEdges = edges;
		mInitStates = initStates;
		mFinalStates = finalStates;
	}

	/**
	 * Builds the loop tree. All formulas are native to the {@link ManagedScript} passed to the constructor.
	 *
	 * @return the root scope, with all loops as nested scopes
	 */
	public Scope<STATE> build() {
		final Set<STATE> reachable = computeReachable();
		for (final STATE state : reachable) {
			for (final STATE successor : successors(state).keySet()) {
				mPredecessors.computeIfAbsent(successor, k -> new LinkedHashSet<>()).add(state);
			}
		}
		final Scope<STATE> root = buildScope(Collections.emptySet(), reachable);
		mLogger.info("LoopTree: built tree with %d loop(s), maximal nesting depth %d", root.loops().size(),
				root.nestingDepth());
		return root;
	}

	// ------------------------------------------------------------------------------------------------------------
	// Flat graph
	// ------------------------------------------------------------------------------------------------------------

	private Set<STATE> computeReachable() {
		final Set<STATE> visited = new LinkedHashSet<>();
		final Deque<STATE> worklist = new ArrayDeque<>();
		for (final STATE init : mInitStates) {
			if (visited.add(init)) {
				worklist.add(init);
			}
		}
		while (!worklist.isEmpty()) {
			for (final STATE successor : successors(worklist.poll()).keySet()) {
				if (visited.add(successor)) {
					worklist.add(successor);
				}
			}
		}
		return visited;
	}

	private Map<STATE, UnmodifiableTransFormula> successors(final STATE state) {
		return mEdges.getOrDefault(state, Collections.emptyMap());
	}

	private List<STATE> neighbors(final STATE state, final Set<STATE> within) {
		final List<STATE> result = new ArrayList<>();
		for (final STATE successor : successors(state).keySet()) {
			if (within.contains(successor)) {
				result.add(successor);
			}
		}
		return result;
	}

	// ------------------------------------------------------------------------------------------------------------
	// Loop structure
	// ------------------------------------------------------------------------------------------------------------

	/**
	 * Non-trivial strongly connected components (more than one state, or a self loop) of the subgraph induced by
	 * {@code nodes}. Iterative Tarjan, so deep programs cannot overflow the stack.
	 */
	private List<Set<STATE>> nontrivialSccs(final Set<STATE> nodes) {
		final List<Set<STATE>> result = new ArrayList<>();
		final Map<STATE, Integer> index = new HashMap<>();
		final Map<STATE, Integer> lowLink = new HashMap<>();
		final Deque<STATE> sccStack = new ArrayDeque<>();
		final Set<STATE> onStack = new HashSet<>();
		int counter = 0;
		for (final STATE start : nodes) {
			if (index.containsKey(start)) {
				continue;
			}
			final Deque<STATE> dfsNodes = new ArrayDeque<>();
			final Deque<Iterator<STATE>> dfsIterators = new ArrayDeque<>();
			index.put(start, counter);
			lowLink.put(start, counter);
			counter++;
			sccStack.push(start);
			onStack.add(start);
			dfsNodes.push(start);
			dfsIterators.push(neighbors(start, nodes).iterator());
			while (!dfsNodes.isEmpty()) {
				final STATE node = dfsNodes.peek();
				final Iterator<STATE> it = dfsIterators.peek();
				if (it.hasNext()) {
					final STATE next = it.next();
					if (!index.containsKey(next)) {
						index.put(next, counter);
						lowLink.put(next, counter);
						counter++;
						sccStack.push(next);
						onStack.add(next);
						dfsNodes.push(next);
						dfsIterators.push(neighbors(next, nodes).iterator());
					} else if (onStack.contains(next)) {
						lowLink.put(node, Math.min(lowLink.get(node), index.get(next)));
					}
					continue;
				}
				dfsNodes.pop();
				dfsIterators.pop();
				if (!dfsNodes.isEmpty()) {
					final STATE parent = dfsNodes.peek();
					lowLink.put(parent, Math.min(lowLink.get(parent), lowLink.get(node)));
				}
				if (lowLink.get(node).equals(index.get(node))) {
					final Set<STATE> scc = new LinkedHashSet<>();
					STATE member;
					do {
						member = sccStack.pop();
						onStack.remove(member);
						scc.add(member);
					} while (!member.equals(node));
					if (scc.size() > 1 || neighbors(node, nodes).contains(node)) {
						result.add(scc);
					}
				}
			}
		}
		return result;
	}

	/**
	 * The heads of the loop {@code loop} (a strongly connected component inside {@code enclosing}): <b>every</b> state
	 * that is entered from outside the loop. A loop with more than one head is irreducible control flow, which is
	 * supported: each head has a pc value of its own, so an iteration that enters the loop at one head and comes back
	 * round to another is a step from {@code h1} to {@code h2}.
	 * <p>
	 * Returning <em>all</em> entry states, rather than picking one, is what keeps the rest of the construction correct.
	 * It establishes the invariant
	 * <ul>
	 * <li><b>(I1)</b> every state of a region that has a predecessor outside the region, or that is an initial state,
	 * is a head of that region.
	 * </ul>
	 * (I1) is why the "entered from outside the enclosing loop" case below cannot happen, why the initial-state test
	 * only has to look at the root (deeper down, an initial state is already a head of every enclosing region, so it
	 * never reaches an inner strongly connected component), and why a path that leaves a region can only come back into
	 * it through a head - which that scope's own steps from {@code h} describe.
	 */
	private Set<STATE> findHeads(final Set<STATE> loop, final Set<STATE> enclosing, final boolean enclosingIsRoot) {
		final Set<STATE> entries = new LinkedHashSet<>();
		for (final STATE state : loop) {
			boolean isEntry = enclosingIsRoot && mInitStates.contains(state);
			for (final STATE pred : mPredecessors.getOrDefault(state, Collections.emptySet())) {
				if (loop.contains(pred)) {
					continue;
				}
				if (!enclosing.contains(pred)) {
					throw new UnsupportedOperationException("Loop state " + state + " is entered from " + pred
							+ ", which is outside the enclosing loop. Invariant (I1) of findHeads is broken, see "
							+ "its documentation.");
				}
				isEntry = true;
			}
			if (isEntry) {
				entries.add(state);
			}
		}
		if (entries.isEmpty()) {
			// buildScope recurses on the region without its heads, so an empty head set would not make progress.
			throw new UnsupportedOperationException(
					"Loop with " + loop.size() + " state(s) has no entry state, so it cannot be reachable: " + loop);
		}
		if (entries.size() > 1) {
			mLogger.info("LoopTree: irreducible loop with %d state(s) is entered at %d states: %s", loop.size(),
					entries.size(), entries);
		}
		return entries;
	}

	// ------------------------------------------------------------------------------------------------------------
	// Scopes
	// ------------------------------------------------------------------------------------------------------------

	/**
	 * Builds the scope of the loop with heads {@code heads} and states {@code region}, or the root scope if
	 * {@code heads} is empty. Inner loops are built first (bottom-up), and a step through this scope can start and end
	 * at every head of an inner loop.
	 */
	private Scope<STATE> buildScope(final Set<STATE> heads, final Set<STATE> region) {
		final boolean isRoot = heads.isEmpty();
		final Set<STATE> inner = new LinkedHashSet<>(region);
		inner.removeAll(heads);

		// inner loops
		final List<Scope<STATE>> children = new ArrayList<>();
		final Set<STATE> interiors = new HashSet<>();
		for (final Set<STATE> loop : nontrivialSccs(inner)) {
			final Set<STATE> loopHeads = findHeads(loop, region, isRoot);
			children.add(buildScope(loopHeads, loop));
			interiors.addAll(loop);
			interiors.removeAll(loopHeads);
		}
		final Set<STATE> childHeads = new LinkedHashSet<>();
		for (final Scope<STATE> child : children) {
			childHeads.addAll(child.heads());
		}

		// states this scope can leave to
		final Set<STATE> escapes = new LinkedHashSet<>();
		if (!isRoot) {
			for (final STATE state : region) {
				if (heads.contains(state)) {
					continue;
				}
				for (final STATE successor : successors(state).keySet()) {
					if (!region.contains(successor)) {
						escapes.add(successor);
					}
				}
			}
		}

		// cut graph: no interiors of inner loops, no outgoing edges of inner heads or of the own heads, so it is
		// acyclic
		final Set<STATE> nodes = new LinkedHashSet<>();
		for (final STATE state : region) {
			if (!interiors.contains(state)) {
				nodes.add(state);
			}
		}
		nodes.addAll(escapes);
		final Map<STATE, List<Pair<UnmodifiableTransFormula, STATE>>> cutEdges = new LinkedHashMap<>();
		for (final STATE node : nodes) {
			final List<Pair<UnmodifiableTransFormula, STATE>> out = new ArrayList<>();
			if (!escapes.contains(node) && !heads.contains(node) && !childHeads.contains(node)) {
				for (final Pair<UnmodifiableTransFormula, STATE> edge : edgesFrom(node)) {
					if (nodes.contains(edge.getSecond())) {
						out.add(edge);
					}
				}
			}
			cutEdges.put(node, out);
		}
		final List<STATE> finals = new ArrayList<>();
		for (final STATE state : mFinalStates) {
			if (nodes.contains(state)) {
				finals.add(state);
			}
		}
		// An escape to an error state ends a step in that error, so only the others have a pc value of their own.
		final Set<STATE> otherEscapes = new LinkedHashSet<>(escapes);
		otherEscapes.removeAll(finals);

		// Where a step through this scope starts: what it takes first, if anything, and the node of the cut graph that
		// leads to. In the root that is the initial states. In a loop a step from a head of the scope takes one of that
		// head's entry transitions, and a step from an inner loop head one of its exit transitions.
		final Set<STATE> programStarts = new LinkedHashSet<>();
		final Map<STATE, List<Pair<UnmodifiableTransFormula, STATE>>> sources = new LinkedHashMap<>();
		if (isRoot) {
			for (final STATE init : mInitStates) {
				if (nodes.contains(init)) {
					programStarts.add(init);
				}
			}
		} else {
			for (final STATE head : heads) {
				final List<Pair<UnmodifiableTransFormula, STATE>> entries = new ArrayList<>();
				for (final Pair<UnmodifiableTransFormula, STATE> edge : edgesFrom(head)) {
					if (region.contains(edge.getSecond())) {
						entries.add(edge);
					}
				}
				sources.put(head, entries);
			}
		}
		for (final Scope<STATE> child : children) {
			for (final STATE childHead : child.heads()) {
				final List<Pair<UnmodifiableTransFormula, STATE>> exits = new ArrayList<>();
				for (final Pair<UnmodifiableTransFormula, STATE> edge : edgesFrom(childHead)) {
					if (!child.region().contains(edge.getSecond())) {
						exits.add(edge);
					}
				}
				sources.put(childHead, exits);
			}
		}
		// A plain state of this scope that an inner loop can jump to (e.g. by break) is a "waypoint". The inner loop's
		// scope only knows how to get to it, the way on from there starts here. A jump out of several loops is an
		// escape of every loop it leaves, so the scope that holds the state is the one that makes it a waypoint.
		for (final Scope<STATE> child : children) {
			for (final STATE w : child.escapes()) {
				if (nodes.contains(w) && !childHeads.contains(w) && !heads.contains(w) && !escapes.contains(w)
						&& !finals.contains(w)) {
					sources.put(w, List.of(new Pair<>(null, w)));
				}
			}
		}

		mLogger.info("LoopTree: scope %s built: %d inner loop(s), %d state(s), %d node(s)",
				isRoot ? "ROOT" : "loop " + heads, children.size(), region.size(), nodes.size());
		return new Scope<>(heads, region, children, inTopologicalOrder(cutEdges), programStarts, sources, finals,
				otherEscapes);
	}

	private List<Pair<UnmodifiableTransFormula, STATE>> edgesFrom(final STATE state) {
		final List<Pair<UnmodifiableTransFormula, STATE>> result = new ArrayList<>();
		for (final Map.Entry<STATE, UnmodifiableTransFormula> edge : successors(state).entrySet()) {
			result.add(new Pair<>(edge.getValue(), edge.getKey()));
		}
		return result;
	}

	/** A graph without a loop, every node before its successors. */
	private Map<STATE, List<Pair<UnmodifiableTransFormula, STATE>>>
			inTopologicalOrder(final Map<STATE, List<Pair<UnmodifiableTransFormula, STATE>>> edges) {
		final Map<STATE, List<Pair<UnmodifiableTransFormula, STATE>>> result = new LinkedHashMap<>();
		for (final STATE node : topologicalOrder(edges)) {
			result.put(node, edges.get(node));
		}
		return result;
	}

	/**
	 * The formula of every path of a graph without a loop, from the initial to the final states, or {@code null} if
	 * there is none. All formulas are native to the {@link ManagedScript} passed to the constructor.
	 *
	 * @throws IllegalStateException
	 *             if the part of the graph reachable from the initial states has a loop
	 */
	public UnmodifiableTransFormula buildLoopFreeFormula() {
		final Set<STATE> nodes = computeReachable();
		if (!nontrivialSccs(nodes).isEmpty()) {
			throw new IllegalStateException("The graph has a loop, so it has no single formula: " + nodes);
		}
		final Map<STATE, List<Pair<UnmodifiableTransFormula, STATE>>> edges = new LinkedHashMap<>();
		for (final STATE node : nodes) {
			edges.put(node, edgesFrom(node));
		}
		final PathFormulaComposer<STATE> composer =
				new PathFormulaComposer<>(mServices, mLogger, mMgdScript, inTopologicalOrder(edges));
		final List<UnmodifiableTransFormula> alternatives = new ArrayList<>();
		for (final STATE init : mInitStates) {
			if (!nodes.contains(init)) {
				continue;
			}
			for (final STATE target : mFinalStates) {
				if (nodes.contains(target)) {
					final UnmodifiableTransFormula path = composer.pathsBetween(init, target);
					if (path != null) {
						alternatives.add(path);
					}
				}
			}
		}
		checkCanceled("composing the transition formulas of a graph without a loop");
		return combineAlternatives(mLogger, mServices, mMgdScript, alternatives);
	}

	/**
	 * Throws if the progress monitor of k-induction says stop, e.g. because the toolchain's deadline has passed. Polled
	 * before a composition of formulas, since evaluating a path expression is still exponential in the worst case (see
	 * {@link PathFormulaComposer}). A pathological abstraction must not run past the deadline uninterrupted.
	 */
	private void checkCanceled(final String task) {
		if (!mServices.getProgressMonitorService().continueProcessing()) {
			throw new ToolchainCanceledException(LoopTreeFormulaBuilder.class, task);
		}
	}

	/**
	 * Kahn's algorithm over a cut graph, ties broken by the order of {@code edges}, so the result is deterministic.
	 *
	 * @param edges
	 *            every node of the cut graph with its outgoing edges, which stay inside the graph
	 * @return the nodes, each before all of its successors
	 */
	private List<STATE> topologicalOrder(final Map<STATE, List<Pair<UnmodifiableTransFormula, STATE>>> edges) {
		final Map<STATE, Integer> inDegree = new HashMap<>();
		for (final STATE node : edges.keySet()) {
			inDegree.putIfAbsent(node, 0);
			for (final Pair<UnmodifiableTransFormula, STATE> t : edges.get(node)) {
				inDegree.merge(t.getSecond(), 1, Integer::sum);
			}
		}
		final Deque<STATE> ready = new ArrayDeque<>();
		for (final STATE node : edges.keySet()) {
			if (inDegree.get(node) == 0) {
				ready.add(node);
			}
		}
		final List<STATE> result = new ArrayList<>(edges.size());
		while (!ready.isEmpty()) {
			final STATE node = ready.poll();
			result.add(node);
			for (final Pair<UnmodifiableTransFormula, STATE> t : edges.get(node)) {
				if (inDegree.merge(t.getSecond(), -1, Integer::sum) == 0) {
					ready.add(t.getSecond());
				}
			}
		}
		if (result.size() != edges.size()) {
			throw new AssertionError("Unexpected cycle in the cut graph of a scope");
		}
		return result;
	}

	/**
	 * Disjunction of alternatives, {@code null} if there is none (a legitimately absent edge, not an error).
	 */
	public static UnmodifiableTransFormula combineAlternatives(final ILogger logger,
			final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final List<UnmodifiableTransFormula> alternatives) {
		if (alternatives.isEmpty()) {
			return null;
		}
		if (alternatives.size() == 1) {
			return alternatives.get(0);
		}
		return TransFormulaUtils.parallelComposition(logger, services, mgdScript, null, false, true,
				alternatives.toArray(new UnmodifiableTransFormula[0]));
	}

	/**
	 * The program (no heads) or one loop: its cut graph, and where a step through it can start and end. A step can
	 * start at {@code programStarts} and {@code sources}, and end at the heads of this scope and of its children, at
	 * {@code finals} and at {@code escapes}.
	 *
	 * @param heads
	 *            the heads of this loop: every state it is entered from outside at. Empty for the root, a single state
	 *            for a reducible loop, several for irreducible control flow.
	 * @param region
	 *            the states of this scope, those of its inner loops included
	 * @param children
	 *            the loops directly nested in this scope
	 * @param cutGraph
	 *            the acyclic graph of this scope, every node before its successors: no interiors of inner loops, and
	 *            the heads of the scope and of its inner loops have no outgoing edges
	 * @param programStarts
	 *            the initial states inside this scope, empty for a loop
	 * @param sources
	 *            the other states a step can start from, with its ways into the cut graph: a formula to take first,
	 *            {@code null} for none, and the node it leads to
	 * @param finals
	 *            the accepting states inside this scope
	 * @param escapes
	 *            the states a run inside this loop can jump to, other than accepting ones. A jump out of several loops
	 *            is one of each of them, since it counts as an escape of a loop wherever inside the loop it starts. The
	 *            scope that holds the state makes it a waypoint, see {@link LoopTreeFormulaBuilder#buildScope}.
	 */
	public record Scope<STATE>(Set<STATE> heads, Set<STATE> region, List<Scope<STATE>> children,
			Map<STATE, List<Pair<UnmodifiableTransFormula, STATE>>> cutGraph, Set<STATE> programStarts,
			Map<STATE, List<Pair<UnmodifiableTransFormula, STATE>>> sources, List<STATE> finals, Set<STATE> escapes) {

		public boolean isRoot() {
			return heads.isEmpty();
		}

		/** All loops below this scope, outer loops before the loops nested in them. */
		public List<Scope<STATE>> loops() {
			final List<Scope<STATE>> result = new ArrayList<>();
			for (final Scope<STATE> child : children) {
				result.add(child);
				result.addAll(child.loops());
			}
			return result;
		}

		/** How many levels of loops are below this scope. */
		int nestingDepth() {
			int result = 0;
			for (final Scope<STATE> child : children) {
				result = Math.max(result, child.nestingDepth() + 1);
			}
			return result;
		}
	}
}
