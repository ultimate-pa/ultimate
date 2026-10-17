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
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
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
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Star;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Union;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Given a nested word automaton, builds every {@link UnmodifiableTransFormula} that k-induction needs, for
 * programs with no loop, any number of sequential loops, and arbitrarily <b>nested</b> loops.
 * <p>
 * The result is a {@link LoopTree}: a tree of {@link Scope}s. The root scope is the whole program, every other scope
 * is one loop. Inside a scope, the nodes are <em>checkpoints</em> (see {@link Checkpoint}): the scope's start
 * ({@code INIT}, one per head of the scope), the heads of its directly nested loops, its end ({@code END(h)}, one of
 * the scope's own heads reached again after one iteration), the error/accepting states ({@code FINAL}) and every
 * state the scope can leave to ({@code ESCAPE}, e.g. a {@code break} out of a loop). The edges are formulas
 * summarizing <b>all</b> loop-free paths between two checkpoints, so the requested parts are:
 * <ul>
 * <li>part before / after a loop: the root scope's edges {@code INIT -> loopHead} and {@code loopHead -> FINAL} (for
 * a nested loop: the same edges in its enclosing loop's scope),
 * <li>loop entry: {@link Scope#getEntry}, the union of the transitions that go from a head into the loop,
 * <li>loop exit: {@link Scope#getExit}, the union of the transitions that leave the loop from a head,
 * <li>loop body: {@link Scope#getBody()} for a loop with one head and without inner loops (one iteration, head back
 * to head, including the entry transition). Any other loop has no single loop-free body formula; its body is the
 * checkpoint graph of its scope ({@link Scope#getEdge}), where each head of each inner loop is a checkpoint,
 * <li>no loop at all: the root scope's edge {@code INIT -> FINAL} is the whole program.
 * </ul>
 * <p>
 * Loops are found structurally (strongly connected components, recursively with the heads removed), so no annotation
 * is required. Several entry and exit transitions per head are supported.
 *
 * <h2>Loops with several heads</h2>
 *
 * The heads of a loop are <b>all</b> the states it is entered at from outside it. A reducible loop has one;
 * irreducible control flow (a {@code goto} into the middle of a loop, or an abstraction in which one loop head
 * location has split into several states) has more, and is supported rather than rejected. Every head gets its own
 * {@code INIT(h)} and {@code END(h)} checkpoint, so a scope with the heads {@code h1, h2} has the edges
 * {@code INIT(h1) -> END(h1)}, {@code INIT(h1) -> END(h2)}, {@code INIT(h2) -> END(h1)} and
 * {@code INIT(h2) -> END(h2)}: the traversals of one iteration, by where it started and where it came back round to.
 * <p>
 * The cross edges are not an extra. An iteration from {@code h1} to {@code h2} has no other representation, because
 * in the enclosing scope both heads are sealed (they are nodes with no outgoing edges) and everything between them
 * is an interior state that is not a node there at all. Taking every entry state as a head is also what keeps the
 * recursion correct, see invariant (I1) at {@code findHeads}.
 * <p>
 * <h2>Procedure calls</h2>
 *
 * Call and return transitions are <b>not</b> edges of this graph. A call's transition formula is only the
 * parameter assignment and a return's only the assignment of the result, so using them as ordinary edges gets the
 * scoping of oldvars, modifiable globals and the callee's locals wrong, and - because the graph has no stack - it
 * also admits paths that leave through one call site and come back at another, splicing away everything in
 * between. Both of those are silent unsoundness, so a call or a return that would end up as an edge here is
 * <b>refused</b> (see {@code rejectUnresolvedCallsAndReturns}).
 * <p>
 * Instead, a caller resolves every call site into a "virtual" call edge before building: one formula for a whole
 * call-to-return span, passed to the scoped constructor. {@link ProcedureSummaries} builds those for k-induction
 * with {@link ProcedureCallGraph#computeVirtualEdge}. A call or a return whose target lies outside the scope is then
 * simply not an edge of this scope's graph, which is the point: the callee is described by the virtual edge.
 * <p>
 * A callee that contains a loop has no such formula. For it, {@link ProcedureSummaries} instead <em>unfolds</em> a
 * copy of the callee per call site into the graph, with a virtual edge for the call and one for the return, and
 * hands this builder an {@link ICallResolvedGraph} whose nodes are {@link CallNode}s rather than plain states. The
 * copies are distinct nodes, so the splicing above cannot happen, and the callee's loop is found by the ordinary
 * SCC search as a nested loop of the caller's scope. Nothing below cares which of the two resolutions produced a
 * node: this class only ever sees a graph with no call and no return transition left.
 *
 * <h2>How to use</h2>
 *
 * Construct the builder, call {@link #build()} once, and read the formulas off the scopes of the resulting
 * {@link LoopTree}. All formulas live in the {@link ManagedScript} passed to the constructor. That script must
 * <b>not</b> be locked while {@link #build()} runs: composing transition formulas declares constants for their aux
 * vars and therefore acquires the lock itself. Lock the script afterwards, once all formulas exist, to use them in a
 * solver. Every {@code getEdge} returns {@code null} if there is no such path, which is normal and not an error.
 *
 * <pre>{@code
 * final LoopTreeFormulaBuilder<LETTER, STATE> builder =
 * 		new LoopTreeFormulaBuilder<>(services, logger, mgdScript, nwa);
 * final LoopTree<STATE> tree = builder.build();
 * final Scope<STATE> root = tree.getRoot();
 * }</pre>
 *
 * <b>No loop.</b> The whole program is one formula:
 *
 * <pre>{@code
 * final UnmodifiableTransFormula program = root.getEdge(Checkpoint.init(), Checkpoint.fin());
 * }</pre>
 *
 * <b>Sequential loops.</b> The parts before and after each loop are edges of the root scope, the loop itself is a
 * child scope. The part between two loops {@code a} and {@code b} is
 * {@code root.getEdge(Checkpoint.loopHead(a), Checkpoint.loopHead(b))}, and {@code root.enumeratePaths()} lists all
 * checkpoint sequences from the program start to an error state, e.g. {@code [INIT, loopHead(a), loopHead(b), FINAL]}.
 *
 * <pre>{@code
 * for (final STATE head : root.getLoopHeads()) {
 * 	final Scope<STATE> loop = root.getChild(head);
 * 	final Checkpoint<STATE> headCp = Checkpoint.loopHead(head);
 * 	final UnmodifiableTransFormula before = root.getEdge(Checkpoint.init(), headCp);
 * 	final UnmodifiableTransFormula after = root.getEdge(headCp, Checkpoint.fin());
 * 	final UnmodifiableTransFormula entry = loop.getEntry(head); // head into the loop
 * 	final UnmodifiableTransFormula exit = loop.getExit(head); // head out of the loop
 * 	final UnmodifiableTransFormula body = loop.getBody(); // one iteration; single-head loops only
 * }
 * }</pre>
 *
 * The edges leaving {@code Checkpoint.init(head)} inside a loop scope include the entry transition, so
 * {@code getBody()} already contains the loop condition; {@code getEntry(head)} gives the entry transition on its
 * own.
 * <p>
 * <b>Nested loops.</b> {@code tree.getLoops()} lists all loops, outer loops before the loops nested in them. A loop
 * with one head and without inner loops (see {@link Scope#isLeaf()}) has a single body formula. For any other loop
 * {@code getBody()} throws an {@link UnsupportedOperationException}; use the checkpoint graph of its scope instead,
 * in which every head of every inner loop is a checkpoint:
 *
 * <pre>{@code
 * for (final Scope<STATE> loop : tree.getLoops()) {
 * 	if (loop.isLeaf() && loop.getHeads().size() == 1) {
 * 		final UnmodifiableTransFormula body = loop.getBody();
 * 	} else {
 * 		final STATE head = loop.getHeads().iterator().next();
 * 		final Checkpoint<STATE> inner = Checkpoint.loopHead(loop.getLoopHeads().iterator().next());
 * 		loop.getEdge(Checkpoint.init(head), inner); // start of this loop's body to the inner loop head
 * 		loop.getEdge(inner, Checkpoint.end(head)); // inner loop head back to this loop's head
 * 		loop.getEdge(inner, Checkpoint.fin()); // inner loop head to an error state
 * 		loop.getEdge(inner, Checkpoint.escape(state)); // inner loop head to a state outside this loop (break)
 * 	}
 * }
 * }</pre>
 *
 * To restrict the builder to a single procedure, use the second constructor with explicit scope, initial and final
 * states.
 *
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            node type of the flat graph. The abstraction's own state type when the graph is the automaton (see
 *            {@link AutomatonGraph}), a {@link CallNode} when a callee is unfolded into it (see
 *            {@link UnfoldedGraph}).
 */
public class LoopTreeFormulaBuilder<LETTER extends IAction, STATE> {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final ManagedScript mMgdScript;
	private final ICallResolvedGraph<LETTER, STATE> mGraph;
	private final Set<STATE> mScopeStates;
	private final Set<STATE> mInitStates;
	private final Collection<STATE> mFinalStates;
	private final Map<STATE, Map<STATE, UnmodifiableTransFormula>> mVirtualCallEdges;
	private final Set<STATE> mSealedStates;
	private final Map<LETTER, UnmodifiableTransFormula> mLetterCache = new HashMap<>();

	private final Map<STATE, List<Pair<Edge<LETTER>, STATE>>> mSuccessors = new HashMap<>();
	private final Map<STATE, Set<STATE>> mPredecessors = new HashMap<>();

	/**
	 * Whole-automaton constructor: no scoping, no virtual call edges. Every state is in the scope, so every call
	 * and every return transition of the abstraction would be an edge of the flat graph; {@link #build()}
	 * therefore refuses an abstraction that has one. Use the scoped constructor with virtual call edges for a
	 * program whose procedures are not inlined.
	 */
	public LoopTreeFormulaBuilder(final IUltimateServiceProvider services, final ILogger logger,
			final ManagedScript mgdScript, final INestedWordAutomaton<LETTER, STATE> abstraction) {
		this(services, logger, mgdScript, abstraction, abstraction.getStates(), abstraction.getInitialStates(),
				abstraction.getFinalStates(), Collections.emptyMap());
	}

	/**
	 * Scoped constructor, e.g. for a single procedure's body. Only states in {@code scopeStates} are considered;
	 * {@code virtualCallEdges} adds one precomputed edge per call site (call state, post-return state, formula).
	 */
	public LoopTreeFormulaBuilder(final IUltimateServiceProvider services, final ILogger logger,
			final ManagedScript mgdScript, final INestedWordAutomaton<LETTER, STATE> abstraction,
			final Set<STATE> scopeStates, final Set<STATE> initStates, final Collection<STATE> finalStates,
			final Map<STATE, Map<STATE, UnmodifiableTransFormula>> virtualCallEdges) {
		this(services, logger, mgdScript, abstraction, scopeStates, initStates, finalStates, virtualCallEdges,
				Collections.emptySet());
	}

	/**
	 * Scoped constructor with sealed states: states of {@code scopeStates} that are dead ends here, i.e. whose own
	 * outgoing transitions are not edges of this graph. That is what a state which is only ever reached through a
	 * virtual call edge needs - an error state inside a callee, say, which belongs to the callee and whose own
	 * successors are described nowhere in this scope. Left unsealed, such a state's outgoing return transition
	 * would become a real edge back into this scope, which is exactly the unscoped call/return treatment this
	 * class refuses everywhere else.
	 */
	public LoopTreeFormulaBuilder(final IUltimateServiceProvider services, final ILogger logger,
			final ManagedScript mgdScript, final INestedWordAutomaton<LETTER, STATE> abstraction,
			final Set<STATE> scopeStates, final Set<STATE> initStates, final Collection<STATE> finalStates,
			final Map<STATE, Map<STATE, UnmodifiableTransFormula>> virtualCallEdges,
			final Set<STATE> sealedStates) {
		this(services, logger, mgdScript, new AutomatonGraph<>(abstraction), scopeStates, initStates, finalStates,
				virtualCallEdges, sealedStates);
	}

	/**
	 * Scoped constructor over an arbitrary {@link ICallResolvedGraph} rather than the automaton itself. This is
	 * what k-induction uses: its nodes are {@link CallNode}s, so that a callee with a loop can be unfolded into
	 * one copy per call site instead of being summarized (see {@link ProcedureSummaries}).
	 */
	public LoopTreeFormulaBuilder(final IUltimateServiceProvider services, final ILogger logger,
			final ManagedScript mgdScript, final ICallResolvedGraph<LETTER, STATE> graph,
			final Set<STATE> scopeStates, final Set<STATE> initStates, final Collection<STATE> finalStates,
			final Map<STATE, Map<STATE, UnmodifiableTransFormula>> virtualCallEdges,
			final Set<STATE> sealedStates) {
		mServices = services;
		mLogger = logger;
		mMgdScript = mgdScript;
		mGraph = graph;
		mScopeStates = scopeStates;
		mInitStates = initStates;
		mFinalStates = finalStates;
		mVirtualCallEdges = virtualCallEdges;
		mSealedStates = sealedStates;
	}

	/**
	 * Builds the loop tree. All formulas are native to the {@link ManagedScript} passed to the constructor.
	 */
	public LoopTree<STATE> build() {
		rejectRecursion();
		rejectUnresolvedCallsAndReturns();
		final Set<STATE> reachable = computeReachable();
		for (final STATE state : reachable) {
			for (final Pair<Edge<LETTER>, STATE> t : successors(state)) {
				mPredecessors.computeIfAbsent(t.getSecond(), k -> new LinkedHashSet<>()).add(state);
			}
		}
		final Scope<STATE> root = buildScope(Collections.emptySet(), reachable, 0);
		final LoopTree<STATE> tree = new LoopTree<>(root);
		mLogger.info("LoopTree: built tree with %d loop(s), maximal nesting depth %d", tree.getLoops().size(),
				tree.getMaxDepth());
		return tree;
	}

	// ------------------------------------------------------------------------------------------------------------
	// Flat graph
	// ------------------------------------------------------------------------------------------------------------

	/**
	 * A virtual call edge needs its callee's summary to already exist as a finished formula, which is undefined
	 * for a cycle in the call graph. Throws {@link UnsupportedOperationException} if some procedure can call
	 * itself.
	 */
	private void rejectRecursion() {
		final Map<String, Set<String>> calls = new LinkedHashMap<>();
		for (final STATE state : mScopeStates) {
			for (final OutgoingCallTransition<LETTER, STATE> t : mGraph.callSuccessors(state)) {
				calls.computeIfAbsent(t.getLetter().getPrecedingProcedure(), k -> new LinkedHashSet<>())
						.add(t.getLetter().getSucceedingProcedure());
			}
		}
		final Set<String> done = new HashSet<>();
		for (final String procedure : calls.keySet()) {
			findCycle(procedure, calls, done, new ArrayList<>());
		}
	}

	private static void findCycle(final String procedure, final Map<String, Set<String>> calls,
			final Set<String> done, final List<String> path) {
		if (path.contains(procedure)) {
			throw new UnsupportedOperationException("Recursion is not supported (procedures must be inlinable), call cycle: "
					+ path.subList(path.indexOf(procedure), path.size()) + " -> " + procedure);
		}
		if (!done.add(procedure)) {
			return;
		}
		path.add(procedure);
		for (final String callee : calls.getOrDefault(procedure, Collections.emptySet())) {
			findCycle(callee, calls, done, path);
		}
		path.remove(path.size() - 1);
	}

	/**
	 * Refuses every call and return transition that would become an edge of this scope's graph, i.e. whose target
	 * is in the scope, since treating it as a plain edge is unsound (see the class javadoc). A call or return that
	 * leaves the scope is not refused: it is what a virtual call edge stands for.
	 * <p>
	 * A sealed state has no edges at all here, so its transitions cannot become one either.
	 */
	private void rejectUnresolvedCallsAndReturns() {
		final List<STATE> callSites = new ArrayList<>();
		for (final STATE state : mScopeStates) {
			if (mGraph.callSuccessors(state).iterator().hasNext()) {
				callSites.add(state);
			}
		}
		for (final STATE state : mScopeStates) {
			if (mSealedStates.contains(state)) {
				continue;
			}
			for (final OutgoingCallTransition<LETTER, STATE> t : mGraph.callSuccessors(state)) {
				rejectUnresolved(state, t.getLetter(), t.getSucc(), "call");
			}
			for (final STATE hier : callSites) {
				for (final OutgoingReturnTransition<LETTER, STATE> t : mGraph.returnSuccessorsGivenHier(state,
						hier)) {
					rejectUnresolved(state, t.getLetter(), t.getSucc(), "return");
				}
			}
		}
	}

	private void rejectUnresolved(final STATE source, final LETTER letter, final STATE target, final String kind) {
		if (!mScopeStates.contains(target)) {
			return;
		}
		throw new UnsupportedOperationException("The " + kind + " transition " + source + " -" + letter + "-> "
				+ target + " is inside the scope of this loop tree, so it would become an ordinary edge of the flat "
				+ "graph. That is unsound: the graph has no call stack, and a " + kind + "'s transition formula "
				+ "describes only the parameter resp. result assignment. Resolve the call site into a virtual call "
				+ "edge (see ProcedureSummaries) or hand this builder a scope that the " + kind + " leaves.");
	}

	private Set<STATE> computeReachable() {
		final Set<STATE> visited = new LinkedHashSet<>();
		final Deque<STATE> worklist = new ArrayDeque<>();
		for (final STATE init : mInitStates) {
			if (mScopeStates.contains(init) && visited.add(init)) {
				worklist.add(init);
			}
		}
		while (!worklist.isEmpty()) {
			final STATE state = worklist.poll();
			for (final Pair<Edge<LETTER>, STATE> t : successors(state)) {
				if (visited.add(t.getSecond())) {
					worklist.add(t.getSecond());
				}
			}
		}
		return visited;
	}

	/**
	 * Every way to leave {@code state} inside the scope: its internal transitions plus the precomputed virtual call
	 * edges that start here. Call and return transitions are none of them, see the class javadoc. A sealed state
	 * has no outgoing edge at all. Memoized.
	 */
	private List<Pair<Edge<LETTER>, STATE>> successors(final STATE state) {
		final List<Pair<Edge<LETTER>, STATE>> cached = mSuccessors.get(state);
		if (cached != null) {
			return cached;
		}
		if (mSealedStates.contains(state)) {
			mSuccessors.put(state, Collections.emptyList());
			return Collections.emptyList();
		}
		final List<Pair<Edge<LETTER>, STATE>> result = new ArrayList<>();
		final Set<Pair<LETTER, STATE>> seen = new HashSet<>();
		for (final OutgoingInternalTransition<LETTER, STATE> t : mGraph.internalSuccessors(state)) {
			addReal(result, seen, t.getLetter(), t.getSucc());
		}
		final Map<STATE, UnmodifiableTransFormula> virtualFromHere = mVirtualCallEdges.get(state);
		if (virtualFromHere != null) {
			for (final Map.Entry<STATE, UnmodifiableTransFormula> entry : virtualFromHere.entrySet()) {
				result.add(new Pair<>(Edge.virtual(entry.getValue()), entry.getKey()));
			}
		}
		mSuccessors.put(state, result);
		return result;
	}

	private void addReal(final List<Pair<Edge<LETTER>, STATE>> result, final Set<Pair<LETTER, STATE>> seen,
			final LETTER letter, final STATE succ) {
		if (mScopeStates.contains(succ) && seen.add(new Pair<>(letter, succ))) {
			result.add(new Pair<>(Edge.real(letter), succ));
		}
	}

	private List<STATE> neighbors(final STATE state, final Set<STATE> within) {
		final List<STATE> result = new ArrayList<>();
		for (final Pair<Edge<LETTER>, STATE> t : successors(state)) {
			if (within.contains(t.getSecond()) && !result.contains(t.getSecond())) {
				result.add(t.getSecond());
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
	 * The heads of the loop {@code loop} (a strongly connected component inside {@code enclosing}): <b>every</b>
	 * state that is entered from outside the loop. A loop with more than one head is irreducible control flow,
	 * which is supported: each head becomes a checkpoint of its own, so an iteration that enters the loop at one
	 * head and comes back round to another is the scope edge {@code INIT(h1) -> END(h2)}.
	 * <p>
	 * Returning <em>all</em> entry states, rather than picking one, is what keeps the rest of the construction
	 * correct. It establishes the invariant
	 * <ul>
	 * <li><b>(I1)</b> every state of a region that has a predecessor outside the region, or that is an initial
	 * state, is a head of that region.
	 * </ul>
	 * (I1) is why the "entered from outside the enclosing loop" case below cannot happen, why the initial-state
	 * test only has to look at the root (deeper down, an initial state is already a head of every enclosing
	 * region, so it never reaches an inner strongly connected component), and why a path that leaves a region can
	 * only come back into it through a head - which that scope's own {@code INIT(h)} edges describe.
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
			throw new UnsupportedOperationException("Loop with " + loop.size()
					+ " state(s) has no entry state, so it cannot be reachable: " + loop);
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
	 * {@code heads} is empty. Inner loops are built first (bottom-up), and every head of an inner loop shows up
	 * here as a checkpoint.
	 */
	private Scope<STATE> buildScope(final Set<STATE> heads, final Set<STATE> region, final int depth) {
		final boolean isRoot = heads.isEmpty();
		final Set<STATE> inner = new LinkedHashSet<>(region);
		inner.removeAll(heads);

		// inner loops
		final List<Scope<STATE>> children = new ArrayList<>();
		final Set<STATE> interiors = new HashSet<>();
		for (final Set<STATE> loop : nontrivialSccs(inner)) {
			final Set<STATE> loopHeads = findHeads(loop, region, isRoot);
			children.add(buildScope(loopHeads, loop, depth + 1));
			interiors.addAll(loop);
			interiors.removeAll(loopHeads);
		}
		final Set<STATE> childHeads = new LinkedHashSet<>();
		for (final Scope<STATE> child : children) {
			childHeads.addAll(child.getHeads());
		}

		// states this scope can leave to
		final Set<STATE> escapes = new LinkedHashSet<>();
		if (!isRoot) {
			for (final STATE state : region) {
				if (heads.contains(state)) {
					continue;
				}
				for (final Pair<Edge<LETTER>, STATE> t : successors(state)) {
					if (!region.contains(t.getSecond())) {
						escapes.add(t.getSecond());
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
		final GenericLabeledGraph<STATE, Edge<LETTER>> graph = new GenericLabeledGraph<>();
		for (final STATE node : nodes) {
			graph.addNode(node);
		}
		for (final STATE node : nodes) {
			if (escapes.contains(node) || heads.contains(node) || childHeads.contains(node)) {
				continue;
			}
			for (final Pair<Edge<LETTER>, STATE> t : successors(node)) {
				if (nodes.contains(t.getSecond())) {
					graph.addEdge(node, t.getFirst(), t.getSecond());
				}
			}
		}
		final PathExpressionComputer<STATE, Edge<LETTER>> pathExprComputer = new PathExpressionComputer<>(graph);
		final RegexToTransFormula evaluator = new RegexToTransFormula();

		// checkpoints and the states each stands for
		final Map<Checkpoint<STATE>, Collection<STATE>> targets = new LinkedHashMap<>();
		for (final STATE childHead : childHeads) {
			targets.put(Checkpoint.loopHead(childHead), Collections.singleton(childHead));
		}
		for (final STATE head : heads) {
			targets.put(Checkpoint.end(head), Collections.singleton(head));
		}
		final List<STATE> finals = new ArrayList<>();
		for (final STATE state : mFinalStates) {
			if (nodes.contains(state)) {
				finals.add(state);
			}
		}
		if (!finals.isEmpty()) {
			targets.put(Checkpoint.fin(), finals);
		}
		for (final STATE escape : escapes) {
			if (!finals.contains(escape)) {
				targets.put(Checkpoint.escape(escape), Collections.singleton(escape));
			}
		}

		final Map<Checkpoint<STATE>, Map<Checkpoint<STATE>, UnmodifiableTransFormula>> edges = new LinkedHashMap<>();

		// Where a path through this scope starts: in the root the initial states, once; in a loop the head of the
		// INIT(h) it starts from, having taken one of that head's entry transitions first. A source is a (prefix
		// formula or null, first state) pair.
		final List<Pair<UnmodifiableTransFormula, STATE>> rootSources = new ArrayList<>();
		final Map<STATE, List<Pair<UnmodifiableTransFormula, STATE>>> sourcesPerHead = new LinkedHashMap<>();
		final Map<STATE, UnmodifiableTransFormula> entryPerHead = new LinkedHashMap<>();
		final Map<STATE, UnmodifiableTransFormula> exitPerHead = new LinkedHashMap<>();
		if (isRoot) {
			for (final STATE init : mInitStates) {
				if (nodes.contains(init)) {
					rootSources.add(new Pair<>(null, init));
				}
			}
		} else {
			for (final STATE head : heads) {
				final List<Pair<UnmodifiableTransFormula, STATE>> sources = new ArrayList<>();
				final List<UnmodifiableTransFormula> entries = new ArrayList<>();
				final List<UnmodifiableTransFormula> exits = new ArrayList<>();
				for (final Pair<Edge<LETTER>, STATE> t : successors(head)) {
					final UnmodifiableTransFormula tf = evaluator.letterFormula(t.getFirst());
					if (region.contains(t.getSecond())) {
						entries.add(tf);
						sources.add(new Pair<>(tf, t.getSecond()));
					} else {
						exits.add(tf);
					}
				}
				sourcesPerHead.put(head, sources);
				entryPerHead.put(head, combineAlternatives(mLogger, mServices, mMgdScript, entries));
				exitPerHead.put(head, combineAlternatives(mLogger, mServices, mMgdScript, exits));
			}
		}

		// edges out of the start: one INIT in the root, one INIT(h) per head otherwise. The edges INIT(h1) ->
		// END(h2) between two different heads are not an extra: an iteration that enters at h1 and comes back
		// round to h2 has no other representation, because in the enclosing scope both heads are sealed and
		// everything between them is an interior and not even a node there.
		final Collection<STATE> startHeads = isRoot ? Collections.<STATE> singletonList(null) : heads;
		for (final STATE head : startHeads) {
			final List<Pair<UnmodifiableTransFormula, STATE>> sources =
					isRoot ? rootSources : sourcesPerHead.get(head);
			for (final Map.Entry<Checkpoint<STATE>, Collection<STATE>> target : targets.entrySet()) {
				final List<UnmodifiableTransFormula> alternatives = new ArrayList<>();
				for (final Pair<UnmodifiableTransFormula, STATE> source : sources) {
					for (final STATE rep : target.getValue()) {
						final UnmodifiableTransFormula path =
								evaluator.evaluate(pathExprComputer.exprBetween(source.getSecond(), rep));
						if (path == null) {
							continue;
						}
						alternatives.add(source.getFirst() == null ? path : sequential(source.getFirst(), path));
					}
				}
				addEdge(edges, Checkpoint.init(head), target.getKey(), alternatives);
			}
		}

		// edges out of inner loop heads: leave via an exit transition, or (mid-body) leave from inside the body
		for (final Scope<STATE> child : children) {
			for (final STATE childHead : child.getHeads()) {
				final Checkpoint<STATE> from = Checkpoint.loopHead(childHead);
				for (final Map.Entry<Checkpoint<STATE>, Collection<STATE>> target : targets.entrySet()) {
					if (target.getKey().equals(from)) {
						continue;
					}
					final List<UnmodifiableTransFormula> alternatives = new ArrayList<>();
					for (final Pair<Edge<LETTER>, STATE> t : successors(childHead)) {
						if (child.getRegion().contains(t.getSecond())) {
							continue;
						}
						final UnmodifiableTransFormula exitTf = evaluator.letterFormula(t.getFirst());
						for (final STATE rep : target.getValue()) {
							final UnmodifiableTransFormula tail =
									evaluator.evaluate(pathExprComputer.exprBetween(t.getSecond(), rep));
							if (tail != null) {
								alternatives.add(sequential(exitTf, tail));
							}
						}
					}
					for (final Checkpoint<STATE> leave : child.getLeaveCheckpoints(childHead)) {
						final UnmodifiableTransFormula body = child.getEdge(Checkpoint.init(childHead), leave);
						if (body == null) {
							continue;
						}
						if (leave.isFinal()) {
							if (target.getKey().isFinal()) {
								alternatives.add(body);
							}
							continue;
						}
						final STATE escapeState = leave.getEscapeState();
						if (!nodes.contains(escapeState)) {
							continue;
						}
						for (final STATE rep : target.getValue()) {
							final UnmodifiableTransFormula tail =
									evaluator.evaluate(pathExprComputer.exprBetween(escapeState, rep));
							if (tail != null) {
								alternatives.add(sequential(body, tail));
							}
						}
					}
					addEdge(edges, from, target.getKey(), alternatives);
				}
			}
		}

		// edges out of "waypoints": a plain state of this scope that an inner loop can jump to (e.g. by break). The
		// inner loop's scope only knows how to get to the waypoint, the way on from there is described here.
		final Set<STATE> waypoints = new LinkedHashSet<>();
		for (final Scope<STATE> child : children) {
			for (final Checkpoint<STATE> escape : child.getEscapeTargets()) {
				final STATE w = escape.getEscapeState();
				if (nodes.contains(w) && !childHeads.contains(w) && !heads.contains(w) && !escapes.contains(w)
						&& !finals.contains(w)) {
					waypoints.add(w);
				}
			}
		}
		for (final STATE waypoint : waypoints) {
			for (final Map.Entry<Checkpoint<STATE>, Collection<STATE>> target : targets.entrySet()) {
				final List<UnmodifiableTransFormula> alternatives = new ArrayList<>();
				for (final STATE rep : target.getValue()) {
					final UnmodifiableTransFormula path =
							evaluator.evaluate(pathExprComputer.exprBetween(waypoint, rep));
					if (path != null) {
						alternatives.add(path);
					}
				}
				addEdge(edges, Checkpoint.escape(waypoint), target.getKey(), alternatives);
			}
		}

		// The automaton states behind each checkpoint. Built here, from the maps above, rather than re-derived
		// by a consumer: a re-derivation could drift from what the formulas were actually built from.
		final Map<Checkpoint<STATE>, Collection<STATE>> checkpointStates = new LinkedHashMap<>(targets);
		// A waypoint is only ever an edge *source* in this scope - the inner loop it is escaped to from is what
		// has it as a target - so it is not in "targets" and would otherwise stand for no state at all. A consumer
		// that asks which states an edge may start in (KInductionCounterexampleBuilder does, to reconstruct the
		// letters of a pc step) would get the empty set and conclude that the step cannot start anywhere.
		for (final STATE waypoint : waypoints) {
			checkpointStates.putIfAbsent(Checkpoint.escape(waypoint), Collections.singleton(waypoint));
		}
		if (isRoot) {
			final Set<STATE> starts = new LinkedHashSet<>();
			for (final Pair<UnmodifiableTransFormula, STATE> source : rootSources) {
				starts.add(source.getSecond());
			}
			checkpointStates.put(Checkpoint.init(), starts);
		} else {
			// In a loop scope an edge out of INIT(h) starts AT h and takes an entry transition first.
			for (final STATE head : heads) {
				checkpointStates.put(Checkpoint.init(head), Collections.singleton(head));
			}
		}

		final Scope<STATE> scope = new Scope<>(heads, region, children, entryPerHead, exitPerHead, edges, depth,
				checkpointStates, nodes);
		mLogger.info("LoopTree: scope %s built: %d inner loop(s), %d state(s), %d checkpoint edge(s)",
				isRoot ? "ROOT" : "loop " + heads, children.size(), region.size(), scope.getNumEdges());
		return scope;
	}

	/**
	 * Throws if the toolchain's deadline has passed, or k-induction's memory budget is exceeded. Polled before every
	 * composition of formulas: a scope with several heads builds an edge for every (head, checkpoint) pair, so the
	 * work is quadratic in the number of heads, and evaluating a path expression is exponential in the worst case
	 * (see {@link RegexToTransFormula}). A pathological abstraction must not run past either limit uninterrupted.
	 */
	private void checkCanceled(final String task) {
		if (!mServices.getProgressMonitorService().continueProcessing()) {
			throw new ToolchainCanceledException(LoopTreeFormulaBuilder.class, task);
		}
	}

	/**
	 * Stores one checkpoint edge.
	 */
	private void addEdge(final Map<Checkpoint<STATE>, Map<Checkpoint<STATE>, UnmodifiableTransFormula>> edges,
			final Checkpoint<STATE> from, final Checkpoint<STATE> to,
			final List<UnmodifiableTransFormula> alternatives) {
		checkCanceled("building the checkpoint edge " + from + " -> " + to);
		final UnmodifiableTransFormula tf = combineAlternatives(mLogger, mServices, mMgdScript, alternatives);
		if (tf != null) {
			edges.computeIfAbsent(from, k -> new LinkedHashMap<>()).put(to, tf);
		}
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

	private UnmodifiableTransFormula sequential(final UnmodifiableTransFormula first,
			final UnmodifiableTransFormula second) {
		checkCanceled("composing the transition formulas of a path in the loop tree");
		return TransFormulaUtils.sequentialComposition(mLogger, mServices, mMgdScript, false, false, false,
				SimplificationTechnique.NONE, List.of(first, second));
	}

	/**
	 * Evaluates a path expression into one relational {@link UnmodifiableTransFormula}, or {@code null} if it
	 * describes no path ({@code null} is the algebraic zero). The cut graphs are acyclic, so {@link Star} cannot
	 * occur.
	 */
	private final class RegexToTransFormula implements IRegexVisitor<Edge<LETTER>, UnmodifiableTransFormula, Void> {

		/**
		 * {@link PathExpressionComputer} builds its expressions with shared sub-objects, so what it returns is a
		 * DAG and a shared subexpression is evaluated once per path through it. Do <b>not</b> memoize this on the
		 * regex object to avoid that: the constructor of {@link UnmodifiableTransFormula} declares a constant per
		 * auxiliary variable, so handing the same composed formula to two compositions makes the second one
		 * declare those constants again and the solver rejects it ("Function c_aux_... is already defined"). Every
		 * result therefore has to be composed afresh, with its own auxiliary variables.
		 */
		UnmodifiableTransFormula evaluate(final IRegex<Edge<LETTER>> regex) {
			checkCanceled("evaluating a path expression of the loop tree");
			return regex.accept(this);
		}

		UnmodifiableTransFormula letterFormula(final Edge<LETTER> edge) {
			if (edge.isVirtual()) {
				return edge.getVirtualFormula();
			}
			final LETTER letter = edge.getRealLetter();
			return mLetterCache.computeIfAbsent(letter, IAction::getTransformula);
		}

		@Override
		public UnmodifiableTransFormula visit(final Union<Edge<LETTER>> union, final Void argument) {
			final UnmodifiableTransFormula first = evaluate(union.getFirst());
			final UnmodifiableTransFormula second = evaluate(union.getSecond());
			if (first == null) {
				return second;
			}
			if (second == null) {
				return first;
			}
			return TransFormulaUtils.parallelComposition(mLogger, mServices, mMgdScript, null, false, true, first,
					second);
		}

		@Override
		public UnmodifiableTransFormula visit(final Concatenation<Edge<LETTER>> concatenation, final Void argument) {
			final UnmodifiableTransFormula first = evaluate(concatenation.getFirst());
			if (first == null) {
				return null;
			}
			final UnmodifiableTransFormula second = evaluate(concatenation.getSecond());
			if (second == null) {
				return null;
			}
			return sequential(first, second);
		}

		@Override
		public UnmodifiableTransFormula visit(final Star<Edge<LETTER>> star, final Void argument) {
			throw new AssertionError("Unexpected cycle in the cut graph of a scope");
		}

		@Override
		public UnmodifiableTransFormula visit(final Literal<Edge<LETTER>> literal, final Void argument) {
			return letterFormula(literal.getLetter());
		}

		@Override
		public UnmodifiableTransFormula visit(final Epsilon<Edge<LETTER>> epsilon, final Void argument) {
			return TransFormulaBuilder.getTrivialTransFormula(mMgdScript);
		}

		@Override
		public UnmodifiableTransFormula visit(final EmptySet<Edge<LETTER>> emptySet, final Void argument) {
			return null;
		}
	}

	/**
	 * One edge of a cut graph: a real automaton letter, or a precomputed virtual edge for a whole call-to-return
	 * span.
	 */
	static final class Edge<LETTER> {
		private final LETTER mRealLetter;
		private final UnmodifiableTransFormula mVirtualFormula;

		private Edge(final LETTER realLetter, final UnmodifiableTransFormula virtualFormula) {
			mRealLetter = realLetter;
			mVirtualFormula = virtualFormula;
		}

		static <L> Edge<L> real(final L letter) {
			return new Edge<>(letter, null);
		}

		static <L> Edge<L> virtual(final UnmodifiableTransFormula formula) {
			return new Edge<>(null, formula);
		}

		boolean isVirtual() {
			return mRealLetter == null;
		}

		LETTER getRealLetter() {
			return mRealLetter;
		}

		UnmodifiableTransFormula getVirtualFormula() {
			return mVirtualFormula;
		}

		@Override
		public String toString() {
			return isVirtual() ? "virtual(call)" : String.valueOf(mRealLetter);
		}
	}

	/**
	 * A node of a scope's checkpoint graph.
	 * <ul>
	 * <li>INIT(h): the start of the scope; the program entry for the root (which has no head), otherwise the head
	 * {@code h} the iteration starts at, with its entry transition still to be taken,
	 * <li>LOOP_HEAD(c): a head of a loop directly nested in the scope,
	 * <li>END(h): a loop scope only, the scope's own head {@code h} reached again after one iteration,
	 * <li>FINAL: the accepting/error states,
	 * <li>ESCAPE: a state outside the loop that its body can jump to (e.g. by {@code break}).
	 * </ul>
	 */
	public static final class Checkpoint<STATE> {
		private enum Kind {
			INIT, LOOP_HEAD, END, FINAL, ESCAPE
		}

		private final Kind mKind;
		private final STATE mState;

		private Checkpoint(final Kind kind, final STATE state) {
			mKind = kind;
			mState = state;
		}

		/** The start of the root scope, which has no head. */
		public static <STATE> Checkpoint<STATE> init() {
			return new Checkpoint<>(Kind.INIT, null);
		}

		/**
		 * The start of a loop scope at the head {@code head}: an edge out of it starts at {@code head} and takes
		 * one of that head's entry transitions first. {@code null} gives the root scope's {@link #init()}.
		 */
		public static <STATE> Checkpoint<STATE> init(final STATE head) {
			return new Checkpoint<>(Kind.INIT, head);
		}

		/** The head {@code head} of this loop scope, reached again after one iteration. */
		public static <STATE> Checkpoint<STATE> end(final STATE head) {
			return new Checkpoint<>(Kind.END, Objects.requireNonNull(head));
		}

		public static <STATE> Checkpoint<STATE> fin() {
			return new Checkpoint<>(Kind.FINAL, null);
		}

		public static <STATE> Checkpoint<STATE> loopHead(final STATE loopHead) {
			return new Checkpoint<>(Kind.LOOP_HEAD, loopHead);
		}

		public static <STATE> Checkpoint<STATE> escape(final STATE state) {
			return new Checkpoint<>(Kind.ESCAPE, state);
		}

		public boolean isInit() {
			return mKind == Kind.INIT;
		}

		public boolean isEnd() {
			return mKind == Kind.END;
		}

		public boolean isFinal() {
			return mKind == Kind.FINAL;
		}

		public boolean isLoopHead() {
			return mKind == Kind.LOOP_HEAD;
		}

		public boolean isEscape() {
			return mKind == Kind.ESCAPE;
		}

		public STATE getLoopHead() {
			if (mKind != Kind.LOOP_HEAD) {
				throw new IllegalStateException("Not a loop-head checkpoint: " + this);
			}
			return mState;
		}

		public STATE getEscapeState() {
			if (mKind != Kind.ESCAPE) {
				throw new IllegalStateException("Not an escape checkpoint: " + this);
			}
			return mState;
		}

		/**
		 * The head an INIT or END checkpoint belongs to, {@code null} only for the root scope's {@link #init()}.
		 * A loop scope has one INIT and one END per head, see {@link Scope#getHeads()}.
		 */
		public STATE getScopeHead() {
			if (mKind != Kind.INIT && mKind != Kind.END) {
				throw new IllegalStateException("Not an init or end checkpoint: " + this);
			}
			return mState;
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (!(obj instanceof Checkpoint)) {
				return false;
			}
			final Checkpoint<?> other = (Checkpoint<?>) obj;
			return mKind == other.mKind && Objects.equals(mState, other.mState);
		}

		@Override
		public int hashCode() {
			return Objects.hash(mKind, mState);
		}

		@Override
		public String toString() {
			return mState == null ? mKind.toString() : mKind + "(" + mState + ")";
		}
	}

	/**
	 * The result: the root scope (whole program) with all loops as nested scopes.
	 */
	public static final class LoopTree<STATE> {
		private final Scope<STATE> mRoot;

		LoopTree(final Scope<STATE> root) {
			mRoot = root;
		}

		public Scope<STATE> getRoot() {
			return mRoot;
		}

		/** All loops, outer loops before the loops nested in them. */
		public List<Scope<STATE>> getLoops() {
			final List<Scope<STATE>> result = new ArrayList<>();
			collect(mRoot, result);
			return result;
		}

		private void collect(final Scope<STATE> scope, final List<Scope<STATE>> result) {
			for (final Scope<STATE> child : scope.getChildren()) {
				result.add(child);
				collect(child, result);
			}
		}

		/** The scope of the loop one of whose heads is {@code head}, or {@code null}. */
		public Scope<STATE> getLoop(final STATE head) {
			for (final Scope<STATE> loop : getLoops()) {
				if (loop.getHeads().contains(head)) {
					return loop;
				}
			}
			return null;
		}

		public int getMaxDepth() {
			int result = 0;
			for (final Scope<STATE> loop : getLoops()) {
				result = Math.max(result, loop.getDepth());
			}
			return result;
		}
	}

	/**
	 * The program (root, {@code getHead() == null}) or one loop, with all formulas between its {@link Checkpoint}s.
	 * Edges are {@code null} if there is no such path.
	 */
	public static final class Scope<STATE> {
		private final Set<STATE> mHeads;
		private final Set<STATE> mRegion;
		private final List<Scope<STATE>> mChildren;
		private final Map<STATE, UnmodifiableTransFormula> mEntry;
		private final Map<STATE, UnmodifiableTransFormula> mExit;
		private final Map<Checkpoint<STATE>, Map<Checkpoint<STATE>, UnmodifiableTransFormula>> mEdges;
		private final int mDepth;
		private final Map<Checkpoint<STATE>, Collection<STATE>> mCheckpointStates;
		private final Set<STATE> mCutGraphNodes;

		Scope(final Set<STATE> heads, final Set<STATE> region, final List<Scope<STATE>> children,
				final Map<STATE, UnmodifiableTransFormula> entry, final Map<STATE, UnmodifiableTransFormula> exit,
				final Map<Checkpoint<STATE>, Map<Checkpoint<STATE>, UnmodifiableTransFormula>> edges,
				final int depth, final Map<Checkpoint<STATE>, Collection<STATE>> checkpointStates,
				final Set<STATE> cutGraphNodes) {
			mHeads = heads;
			mRegion = region;
			mChildren = children;
			mEntry = entry;
			mExit = exit;
			mEdges = edges;
			mDepth = depth;
			mCheckpointStates = checkpointStates;
			mCutGraphNodes = cutGraphNodes;
		}

		/**
		 * The automaton states a checkpoint stands for, both as the source and as the target of this scope's
		 * edges: INIT in the root are the initial states inside this scope, INIT(h) in a loop is {@code h} (an
		 * edge out of it starts there and takes an entry transition first), END(h) is {@code h}, LOOP_HEAD(c) is
		 * {@code c}, FINAL are the accepting states inside this scope, ESCAPE(s) is {@code s}.
		 *
		 * @return the states, empty if the checkpoint does not occur in this scope.
		 */
		public Collection<STATE> getCheckpointStates(final Checkpoint<STATE> checkpoint) {
			final Collection<STATE> result = mCheckpointStates.get(checkpoint);
			return result == null ? Collections.emptyList() : Collections.unmodifiableCollection(result);
		}

		/** The nodes of this scope's cut graph: the region without the interiors of inner loops, plus the escapes. */
		public Set<STATE> getCutGraphNodes() {
			return Collections.unmodifiableSet(mCutGraphNodes);
		}

		public boolean isRoot() {
			return mHeads.isEmpty();
		}

		/**
		 * The heads of this loop: every state it is entered from outside at. Empty for the root, a single state
		 * for a reducible loop, several for irreducible control flow. The scope has one {@link Checkpoint#init}
		 * and one {@link Checkpoint#end} per head.
		 */
		public Set<STATE> getHeads() {
			return Collections.unmodifiableSet(mHeads);
		}

		/** Nesting depth: 0 for the root, 1 for an outermost loop, ... */
		public int getDepth() {
			return mDepth;
		}

		public Set<STATE> getRegion() {
			return mRegion;
		}

		/** The loops directly nested in this scope. */
		public List<Scope<STATE>> getChildren() {
			return mChildren;
		}

		/**
		 * Heads of the loops directly nested in this scope. A child with irreducible control flow contributes
		 * several, so this is not in bijection with {@link #getChildren()}.
		 */
		public Set<STATE> getLoopHeads() {
			final Set<STATE> result = new LinkedHashSet<>();
			for (final Scope<STATE> child : mChildren) {
				result.addAll(child.getHeads());
			}
			return result;
		}

		public boolean isLeaf() {
			return mChildren.isEmpty();
		}

		/** The directly nested loop one of whose heads is {@code head}, or {@code null}. */
		public Scope<STATE> getChild(final STATE head) {
			for (final Scope<STATE> child : mChildren) {
				if (child.getHeads().contains(head)) {
					return child;
				}
			}
			return null;
		}

		/** Loop entry: union of the transitions from {@code head} into the loop. */
		public UnmodifiableTransFormula getEntry(final STATE head) {
			requireHead(head);
			return mEntry.get(head);
		}

		/** Loop exit: union of the transitions from {@code head} out of the loop. */
		public UnmodifiableTransFormula getExit(final STATE head) {
			requireHead(head);
			return mExit.get(head);
		}

		/**
		 * One iteration of this loop (head back to head, including the entry transition). Only for a loop
		 * without inner loops and with a single head, otherwise use {@link #getEdge} on this scope's
		 * checkpoints.
		 * <p>
		 * A loop with several heads deliberately has no body formula, not even
		 * {@code getEdge(init(h), end(h))}: that is a <em>proper subset</em> of one iteration, because an
		 * iteration may enter at one head and come back round to another. Unrolling it would under-approximate
		 * the loop and could prove a program safe that is not.
		 */
		public UnmodifiableTransFormula getBody() {
			if (isRoot() || !isLeaf() || mHeads.size() != 1) {
				throw new UnsupportedOperationException("No single loop-free body formula for " + this
						+ ": it is the root, has inner loops, or is entered at several heads; use the checkpoint "
						+ "graph (getEdge) instead");
			}
			final STATE head = mHeads.iterator().next();
			return getEdge(Checkpoint.init(head), Checkpoint.end(head));
		}

		/** The body formula of the directly nested loop with head {@code head}, see {@link #getBody()}. */
		public UnmodifiableTransFormula getLoopBody(final STATE head) {
			final Scope<STATE> child = getChild(head);
			if (child == null) {
				throw new IllegalArgumentException(head + " is not the head of a loop nested directly in " + this);
			}
			return child.getBody();
		}

		private void requireHead(final STATE head) {
			if (!mHeads.contains(head)) {
				throw new IllegalArgumentException(head + " is not a head of " + this + ", whose heads are "
						+ mHeads);
			}
		}

		/** Every loop-free way of getting from checkpoint {@code from} to {@code to}, or {@code null}. */
		public UnmodifiableTransFormula getEdge(final Checkpoint<STATE> from, final Checkpoint<STATE> to) {
			requireCheckpointOfThisScope(from);
			requireCheckpointOfThisScope(to);
			final Map<Checkpoint<STATE>, UnmodifiableTransFormula> outgoing = mEdges.get(from);
			return outgoing == null ? null : outgoing.get(to);
		}

		/**
		 * An INIT or END checkpoint names the head it belongs to, so one built for another scope - or the
		 * headless {@link Checkpoint#init()} used on a loop scope - matches no key here. Left alone that would
		 * return {@code null}, which every caller reads as "there is no such path", and the missing edge would
		 * silently shrink the transition system instead of failing.
		 */
		private void requireCheckpointOfThisScope(final Checkpoint<STATE> checkpoint) {
			if (!checkpoint.isInit() && !checkpoint.isEnd()) {
				return;
			}
			final STATE head = checkpoint.getScopeHead();
			if (head == null) {
				if (!checkpoint.isInit() || !isRoot()) {
					throw new IllegalArgumentException(checkpoint + " names no head, but " + this
							+ " is a loop scope; use Checkpoint.init(head) / Checkpoint.end(head)");
				}
			} else if (!mHeads.contains(head)) {
				throw new IllegalArgumentException(
						checkpoint + " does not belong to " + this + ", whose heads are " + mHeads);
			}
		}

		/** The checkpoints (other than INIT) reachable from INIT. */
		public Set<Checkpoint<STATE>> getCheckpoints() {
			final Set<Checkpoint<STATE>> result = new LinkedHashSet<>();
			for (final Map<Checkpoint<STATE>, UnmodifiableTransFormula> outgoing : mEdges.values()) {
				result.addAll(outgoing.keySet());
			}
			return result;
		}

		/**
		 * All edges of this scope: source checkpoint, target checkpoint, formula. A source can be INIT, an inner
		 * loop head, or an ESCAPE checkpoint that stands for a "waypoint" state of this scope, i.e. a state inside
		 * this scope that an inner loop can jump to (the way on from there is described by these edges).
		 */
		public Map<Checkpoint<STATE>, Map<Checkpoint<STATE>, UnmodifiableTransFormula>> getEdges() {
			return Collections.unmodifiableMap(mEdges);
		}

		/** All ESCAPE checkpoints that occur as the target of an edge of this scope. */
		public Set<Checkpoint<STATE>> getEscapeTargets() {
			final Set<Checkpoint<STATE>> result = new LinkedHashSet<>();
			for (final Map<Checkpoint<STATE>, UnmodifiableTransFormula> outgoing : mEdges.values()) {
				for (final Checkpoint<STATE> target : outgoing.keySet()) {
					if (target.isEscape()) {
						result.add(target);
					}
				}
			}
			return result;
		}

		/**
		 * The FINAL and ESCAPE checkpoints INIT({@code head}) has an edge to, i.e. the ways a path that entered
		 * this loop at {@code head} can leave it.
		 */
		List<Checkpoint<STATE>> getLeaveCheckpoints(final STATE head) {
			requireHead(head);
			final List<Checkpoint<STATE>> result = new ArrayList<>();
			final Map<Checkpoint<STATE>, UnmodifiableTransFormula> outgoing = mEdges.get(Checkpoint.init(head));
			if (outgoing != null) {
				for (final Checkpoint<STATE> checkpoint : outgoing.keySet()) {
					if (checkpoint.isFinal() || checkpoint.isEscape()) {
						result.add(checkpoint);
					}
				}
			}
			return result;
		}

		int getNumEdges() {
			int result = 0;
			for (final Map<Checkpoint<STATE>, UnmodifiableTransFormula> outgoing : mEdges.values()) {
				result += outgoing.size();
			}
			return result;
		}

		/** All simple paths from INIT to FINAL, see {@link #enumeratePaths(Checkpoint)}. */
		public List<List<Checkpoint<STATE>>> enumeratePaths() {
			return enumeratePaths(Checkpoint.fin());
		}

		/**
		 * Every simple path from INIT to {@code target} through the present edges, as an ordered checkpoint list.
		 * An execution may visit only a subset of the inner loop heads, possibly several in sequence, so this is a
		 * genuine enumeration. There is no upper bound on the number of paths, which can be exponential in the
		 * number of loops.
		 */
		public List<List<Checkpoint<STATE>>> enumeratePaths(final Checkpoint<STATE> target) {
			if (!isRoot()) {
				throw new UnsupportedOperationException("Path enumeration starts at INIT, which only the root "
						+ "scope has; a loop scope starts at one INIT(head) per head, see getHeads()");
			}
			final List<List<Checkpoint<STATE>>> result = new ArrayList<>();
			final Deque<Checkpoint<STATE>> current = new ArrayDeque<>();
			final Checkpoint<STATE> init = Checkpoint.init();
			current.addLast(init);
			final Set<Checkpoint<STATE>> visited = new HashSet<>();
			visited.add(init);
			enumeratePaths(init, target, current, visited, result);
			return result;
		}

		private void enumeratePaths(final Checkpoint<STATE> node, final Checkpoint<STATE> target,
				final Deque<Checkpoint<STATE>> current, final Set<Checkpoint<STATE>> visited,
				final List<List<Checkpoint<STATE>>> result) {
			if (node.equals(target)) {
				result.add(new ArrayList<>(current));
				return;
			}
			final Map<Checkpoint<STATE>, UnmodifiableTransFormula> outgoing = mEdges.get(node);
			if (outgoing == null) {
				return;
			}
			for (final Checkpoint<STATE> next : outgoing.keySet()) {
				if (!visited.add(next)) {
					continue;
				}
				current.addLast(next);
				enumeratePaths(next, target, current, visited, result);
				current.removeLast();
				visited.remove(next);
			}
		}

		@Override
		public String toString() {
			return isRoot() ? "ROOT" : "loop" + mHeads;
		}
	}
}
