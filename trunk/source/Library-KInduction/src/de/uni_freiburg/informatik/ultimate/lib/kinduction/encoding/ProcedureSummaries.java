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
import java.util.Arrays;
import java.util.Collections;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.LoopTreeFormulaBuilder.Checkpoint;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.LoopTreeFormulaBuilder.LoopTree;

/**
 * Resolves every procedure call of a nested word automaton, so that the graph {@link LoopTreeFormulaBuilder} builds -
 * and therefore the {@link PcTransitionSystem} built from it - contains no call and no return transition.
 * <p>
 * Why this is needed rather than convenient: a flat graph has no call stack. Putting a call and a return into it
 * as ordinary edges makes a callee that is called from two sites look like a <em>loop</em> (site1 -&gt; entry,
 * exit -&gt; after-site1, ... -&gt; site2 -&gt; entry) and admits paths that enter at one call site and return to
 * another, splicing away everything in between. On top of that, a call's transition formula is only the parameter
 * assignment and a return's only the assignment of the result, so the scoping of oldvars, modifiable globals and
 * the callee's locals would be wrong as well.
 *
 * <h2>Summarizing or unfolding</h2>
 *
 * There are two ways to resolve a call site, and which one applies is decided per procedure:
 * <ul>
 * <li>A <b>summarizable</b> procedure - its own graph is loop-free and every procedure it calls is summarizable -
 * becomes a single <b>summary edge</b> per call transition and per exit state of the callee,
 * {@code callSite -> post-return state}, with the callee's entry-to-exit formula composed with the call and the
 * return by {@link ProcedureCallGraph#computeVirtualEdge}. No state of the callee enters the caller's graph.
 * <li>Any other procedure - one that contains a loop, or that calls such a procedure - has no single loop-free
 * entry-to-exit formula, so it is <b>unfolded</b> instead: its states are copied into the caller's graph, one copy
 * per call site (that is what a {@link CallNode}'s call site chain distinguishes), with a virtual edge into the
 * copy for the call and one out of it for the return. Its loops then are ordinary nested loops of the caller's
 * loop tree, which {@code LoopTreeFormulaBuilder} and {@code PcTransitionSystem} already support at any depth.
 * </ul>
 * Summarizing is kept for the procedures it fits because it is much cheaper: one formula instead of a copy of the
 * callee's whole graph, and no extra {@code pc} value per loop head per call site.
 *
 * <h2>Errors inside a callee</h2>
 *
 * An error state of a <b>summarized</b> callee becomes an <b>error edge</b> {@code callSite -> that error state},
 * built with {@link TransFormulaUtils#sequentialCompositionWithPendingCall}. The error state becomes a state (and a
 * final state) of the caller's graph, sealed so that its own transitions are not edges there, see
 * {@link LoopTreeFormulaBuilder}'s sealed-state constructor. Error states are carried up this way through any
 * number of levels. In an <b>unfolded</b> callee the error state is simply a node of the copy, and needs no edge of
 * its own. Either way the call stays pending, so such a node is reported by {@link #getPendingErrorTargets()} and
 * {@link KInductionCounterexampleBuilder} knows the counterexample ends with an unmatched call.
 * <p>
 * Every summary formula is built for <b>one</b> call transition and <b>one</b> exit resp. error state, never for
 * the union of all of them: the union would let a path that reaches one exit leave through another exit's return
 * transition, which the abstraction does not admit, and k-induction would answer UNSAFE on a path that no
 * counterexample can realise.
 *
 * <h2>What is not supported</h2>
 *
 * A procedure that reads an {@code old(g)} and calls a procedure that is unfolded or stack-encoded and may
 * overwrite that snapshot, see {@code rejectOldVarReadsAcrossStackFreeCalls}: neither an unfolded nor a stacked
 * activation gets its own copy of the oldvars, because {@link PcTransitionSystem} does not keep oldvars in the
 * state at all.
 * <p>
 * Recursion and an unfolding too big to build are <b>not</b> in this list any more. A procedure on a call cycle,
 * and any procedure whose unfolding would not fit into {@link #MAX_UNFOLDED_NODES}, is given an activation record
 * instead - see {@link CallStack} - so its states occur exactly once in the graph and its recursive call is an
 * ordinary loop of it.
 *
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public final class ProcedureSummaries<LETTER extends IAction, STATE> {

	/**
	 * How many nodes the unfolded graph may have. Unfolding is exponential in the depth of the call graph times
	 * the number of call sites per procedure, so a program can ask for arbitrarily many nodes; past this many the
	 * analysis is refused instead of being silently cut short. Like {@code KInduction.MAX_K} this is a constant
	 * rather than a preference so far.
	 */
	public static final int MAX_UNFOLDED_NODES = 50_000;

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final CfgSmtToolkit mCsToolkit;
	private final ManagedScript mMgdScript;
	private final INestedWordAutomaton<LETTER, STATE> mAbstraction;

	private final Map<String, Set<STATE>> mStatesByProcedure;
	private final Map<String, ScopeData> mScopeData = new LinkedHashMap<>();
	/** The procedures that are unfolded at their call sites rather than summarized, see the class javadoc. */
	private final Set<String> mUnfolded = new LinkedHashSet<>();
	/**
	 * The procedures whose activations are told apart by {@link CallStack} rather than by copies of their states:
	 * every procedure on a call cycle, plus any procedure whose unfolding would not fit into
	 * {@link #MAX_UNFOLDED_NODES}. Their states occur exactly once in the graph.
	 */
	private final Set<String> mStacked = new LinkedHashSet<>();
	/** Null exactly if {@link #mStacked} is empty, i.e. if no call needs an activation record. */
	private CallStack mCallStack;
	/** Hands out the id that tells a stacked return which call site it has to go back to. */
	private int mNextReturnSiteId;
	/** Per procedure, the states a call transition enters it at. Used to look for loops in its body. */
	private final Map<String, Set<STATE>> mEntryStates = new LinkedHashMap<>();

	private final Set<CallNode<STATE>> mRootScopeStates = new LinkedHashSet<>();
	private final Set<CallNode<STATE>> mRootInitStates = new LinkedHashSet<>();
	private final Set<CallNode<STATE>> mRootFinalStates = new LinkedHashSet<>();
	private final Set<CallNode<STATE>> mRootSealedStates = new LinkedHashSet<>();
	private final Set<CallNode<STATE>> mRootPendingErrors = new LinkedHashSet<>();
	private final Map<CallNode<STATE>, Map<CallNode<STATE>, UnmodifiableTransFormula>> mRootVirtualCallEdges =
			new LinkedHashMap<>();

	private int mNumBuilds;
	private int mNumUnfoldedCallSites;
	private int mNumSummarizedCallSites;
	private int mNumStackedCallSites;

	/**
	 * Where a resolved call site puts the nodes it creates. A procedure's own scope works in plain states, so both
	 * operations are the identity there; the unfolded root graph works in {@link CallNode}s, where they are
	 * "another state of this activation" and "a state of the activation the call enters".
	 *
	 * @param <N>
	 *            node type
	 */
	private interface INodeSpace<S, N> {
		N sibling(S state);

		N enter(S calleeState);
	}

	/** Everything one procedure's own checkpoint graph is built from, once its callees are done. */
	private final class ScopeData {
		private final String mProcedure;
		/** The procedure's own states plus the error states imported from its callees. */
		private final Set<STATE> mScopeStates = new LinkedHashSet<>();
		/** The imported error states: dead ends here, reached only through a virtual error edge. */
		private final Set<STATE> mSealed = new LinkedHashSet<>();
		/** This procedure's own accepting states plus the imported ones. */
		private final Set<STATE> mErrorStates = new LinkedHashSet<>();
		private final Map<STATE, Map<STATE, UnmodifiableTransFormula>> mVirtualEdges;

		private ScopeData(final String procedure, final Map<STATE, Map<STATE, UnmodifiableTransFormula>> edges,
				final Set<STATE> imported) {
			mProcedure = procedure;
			mVirtualEdges = edges;
			mScopeStates.addAll(ownStates(procedure));
			mScopeStates.addAll(imported);
			mSealed.addAll(imported);
			mErrorStates.addAll(ProcedureCallGraph.intersect(mAbstraction.getFinalStates(), ownStates(procedure)));
			mErrorStates.addAll(imported);
		}
	}

	public ProcedureSummaries(final IUltimateServiceProvider services, final ILogger logger,
			final CfgSmtToolkit csToolkit, final ManagedScript mgdScript,
			final INestedWordAutomaton<LETTER, STATE> abstraction) {
		mServices = services;
		mLogger = logger;
		mCsToolkit = csToolkit;
		mMgdScript = mgdScript;
		mAbstraction = abstraction;
		mStatesByProcedure = ProcedureCallGraph.groupStatesByProcedure(abstraction.getStates());
		collectEntryStates();

		final ProcedureCallGraph callGraph = new ProcedureCallGraph(logger, abstraction);
		final Set<String> entryProcedures = callGraph.getEntryProcedures();
		// Only what an entry procedure can reach: a call cycle among procedures that are never called says nothing
		// about this program, and encoding it would spend a stack on activations that never happen.
		final Set<String> reachable = callGraph.getReachableProcedures();
		for (final Set<String> cycle : callGraph.getRecursiveSccs(reachable)) {
			mStacked.addAll(cycle);
		}
		final List<String> order = new ArrayList<>();
		for (final Set<String> scc : callGraph.getSccsCalleeFirst(reachable)) {
			order.addAll(scc);
		}
		mLogger.info("KInduction: call graph ready, %d of %d procedure(s) reachable, processing order %s",
				order.size(), mStatesByProcedure.size(), order);

		for (final String procedure : order) {
			if (entryProcedures.contains(procedure) || mStacked.contains(procedure)) {
				// An entry procedure is never summarized (nothing calls it, its graph is the root graph itself), and
				// a procedure on a call cycle has no summary by definition.
				continue;
			}
			classify(callGraph, procedure);
		}
		stackUnfoldingsThatDoNotFit(order, entryProcedures);
		if (!mStacked.isEmpty()) {
			mCallStack = new CallStack(mMgdScript, localsOf(mStacked));
		}
		rejectOldVarReadsAcrossStackFreeCalls(entryProcedures, callGraph);
		unfold(entryProcedures);

		mLogger.info(
				"KInduction: resolved %d call site(s) by summary, %d by unfolding and %d by an activation record "
						+ "(%d checkpoint graph(s) built); entry scope has %d node(s), %d error node(s), of which %d "
						+ "with a pending call",
				mNumSummarizedCallSites, mNumUnfoldedCallSites, mNumStackedCallSites, mNumBuilds,
				mRootScopeStates.size(), mRootFinalStates.size(), mRootPendingErrors.size());
		if (!mUnfolded.isEmpty()) {
			mLogger.info("KInduction: unfolded procedure(s) %s, because they contain a loop or call one that does",
					mUnfolded);
		}
		if (mCallStack != null) {
			mLogger.info("KInduction: stack-encoded procedure(s) %s, using %d extra variable(s)", mStacked,
					mCallStack.getVariables().size());
		}
	}

	// ----------------------------------------------------------------------------------------------------------
	// Results, to be handed to LoopTreeFormulaBuilder's scoped constructor
	// ----------------------------------------------------------------------------------------------------------

	/** The flat graph the nodes below live in: the abstraction read through {@link CallNode}s. */
	public ICallResolvedGraph<LETTER, CallNode<STATE>> getGraph() {
		return new UnfoldedGraph<>(mAbstraction);
	}

	/** The entry procedures' nodes, the nodes of every unfolded callee copy, and every imported error node. */
	public Set<CallNode<STATE>> getScopeStates() {
		return Collections.unmodifiableSet(mRootScopeStates);
	}

	public Set<CallNode<STATE>> getInitStates() {
		return Collections.unmodifiableSet(mRootInitStates);
	}

	/** Every accepting node of the graph, wherever in the call tree the state it stands for lies. */
	public Set<CallNode<STATE>> getFinalStates() {
		return Collections.unmodifiableSet(mRootFinalStates);
	}

	public Map<CallNode<STATE>, Map<CallNode<STATE>, UnmodifiableTransFormula>> getVirtualCallEdges() {
		return Collections.unmodifiableMap(mRootVirtualCallEdges);
	}

	/**
	 * The procedures whose activations {@link CallStack} tells apart, so that their states occur exactly once in
	 * the graph however deep the recursion goes. A node inside one of them cannot say which activation it belongs
	 * to - see {@link CallNode} - which is what {@link KInductionCounterexampleBuilder} has to allow for.
	 */
	public Set<String> getStackedProcedures() {
		return Collections.unmodifiableSet(mStacked);
	}

	/**
	 * The variable that counts the activations {@link CallStack} keeps, or {@code null} if this program needed no
	 * activation record at all. How many calls are open at a node is exactly its chain of call sites plus how far
	 * this has moved since the start, which is what lets {@link KInductionCounterexampleBuilder} cut a run into pc
	 * steps again.
	 */
	public IProgramVar getStackPointer() {
		return mCallStack == null ? null : mCallStack.getStackPointer();
	}

	/**
	 * The nodes that are dead ends of this graph because their own transitions belong to a procedure that is not
	 * in it: the error states imported from a summarized callee. An unfolded callee's states are all in the graph,
	 * so none of them is sealed.
	 */
	public Set<CallNode<STATE>> getSealedStates() {
		return Collections.unmodifiableSet(mRootSealedStates);
	}

	/**
	 * The error nodes that lie inside a callee, i.e. that are reached with the call still pending. A
	 * counterexample that ends in one of them ends with an unmatched call, see
	 * {@link KInductionCounterexampleBuilder}. This is a superset of {@link #getSealedStates()}: an error inside an
	 * unfolded callee is reached with a pending call as well, but is not sealed.
	 */
	public Set<CallNode<STATE>> getPendingErrorTargets() {
		return Collections.unmodifiableSet(mRootPendingErrors);
	}

	// ----------------------------------------------------------------------------------------------------------
	// Deciding between a summary and an unfolding
	// ----------------------------------------------------------------------------------------------------------

	/**
	 * Decides whether {@code procedure} is summarized or unfolded, and, if it is summarized, builds the
	 * {@link ScopeData} its callers need. Called callee-first, so every callee has been classified already.
	 */
	private void classify(final ProcedureCallGraph callGraph, final String procedure) {
		for (final String callee : callGraph.getCallees(procedure)) {
			if (mUnfolded.contains(callee) || mStacked.contains(callee)) {
				// No summary for the callee means none for this procedure either: it has no loop-free formula. A
				// stacked callee also has to be resolved in the root graph, where its states live, so a caller of
				// one cannot be summarized into a scope of its own.
				mUnfolded.add(procedure);
				return;
			}
		}
		final Set<STATE> imported = new LinkedHashSet<>();
		final Map<STATE, Map<STATE, UnmodifiableTransFormula>> edges = buildVirtualEdges(procedure, imported);
		final ScopeData data = new ScopeData(procedure, edges, imported);
		if (hasCycleInScope(data, entryStates(procedure))) {
			mUnfolded.add(procedure);
			return;
		}
		mScopeData.put(procedure, data);
	}

	/**
	 * Refuses an unfolded procedure that reads an {@code old(g)} and calls another unfolded procedure.
	 * <p>
	 * {@code oldVarsAssignment} writes {@code old(g) := g}, and an {@link IProgramOldVar} belongs to the global
	 * variable, not to a procedure activation. In an unfolded graph the snapshot is therefore a single state
	 * variable that a nested unfolded call overwrites, so the caller would read the callee's snapshot after the
	 * call returned. A summarized call cannot do this:
	 * {@link TransFormulaUtils#sequentialCompositionWithCallAndReturn} removes the oldvars the callee may modify
	 * from the summary's interface, so the snapshot never escapes it. Giving every activation its own copy of the
	 * oldvars would mean minting fresh program variables, which is out of proportion here - C programs translated
	 * to Boogie do not read {@code old(...)} in a procedure body at all - so this is refused instead.
	 */
	private void rejectOldVarReadsAcrossStackFreeCalls(final Set<String> entryProcedures,
			final ProcedureCallGraph callGraph) {
		for (final String procedure : union(union(entryProcedures, mUnfolded), mStacked)) {
			final Set<String> unfoldedCallees = new LinkedHashSet<>();
			for (final String callee : callGraph.getCallees(procedure)) {
				if (mUnfolded.contains(callee) || mStacked.contains(callee)) {
					unfoldedCallees.add(callee);
				}
			}
			if (unfoldedCallees.isEmpty()) {
				continue;
			}
			for (final STATE state : ownStates(procedure)) {
				for (final OutgoingInternalTransition<LETTER, STATE> t : mAbstraction.internalSuccessors(state)) {
					final IProgramOldVar oldVar = someOldVar(t.getLetter().getTransformula());
					if (oldVar != null) {
						throw new UnsupportedOperationException("procedure " + procedure + " reads " + oldVar
								+ " and calls " + unfoldedCallees + ", which cannot be summarized and is therefore "
								+ "unfolded into " + procedure + "'s graph. The unfolded call reassigns " + oldVar
								+ ", so the snapshot " + procedure + " reads would be the callee's, not its own. "
								+ "k-induction does not give an unfolded activation its own copy of the oldvars; "
								+ "inline " + unfoldedCallees + ", or remove the old(...) read.");
					}
				}
			}
		}
	}

	private static IProgramOldVar someOldVar(final UnmodifiableTransFormula tf) {
		for (final IProgramVar var : tf.getInVars().keySet()) {
			if (var instanceof IProgramOldVar) {
				return (IProgramOldVar) var;
			}
		}
		for (final IProgramVar var : tf.getOutVars().keySet()) {
			if (var instanceof IProgramOldVar) {
				return (IProgramOldVar) var;
			}
		}
		return null;
	}

	// ----------------------------------------------------------------------------------------------------------
	// Building the unfolded root graph
	// ----------------------------------------------------------------------------------------------------------

	/**
	 * Walks the entry procedures from their initial states, resolving every call site on the way: by a summary
	 * edge if the callee is summarizable, by unfolding a fresh copy of the callee otherwise. Unfolded copies are
	 * walked as well, so a call inside a copy is resolved in that copy's own context.
	 */
	private void unfold(final Set<String> entryProcedures) {
		final Map<CallNode<STATE>, Map<CallNode<STATE>, List<UnmodifiableTransFormula>>> alternatives =
				new LinkedHashMap<>();
		final Deque<CallNode<STATE>> worklist = new ArrayDeque<>();
		for (final String entry : entryProcedures) {
			for (final STATE init : ProcedureCallGraph.intersect(mAbstraction.getInitialStates(),
					ownStates(entry))) {
				final CallNode<STATE> node = CallNode.root(init);
				mRootInitStates.add(node);
				if (mRootScopeStates.add(node)) {
					worklist.add(node);
				}
			}
		}
		while (!worklist.isEmpty()) {
			// Every node may resolve call sites, which composes formulas; the summaries poll in LoopTreeFormulaBuilder.
			if (!mServices.getProgressMonitorService().continueProcessing()) {
				throw new ToolchainCanceledException(ProcedureSummaries.class, String.format(
						"unfolding the call sites of the entry scope (%d node(s) so far)", mRootScopeStates.size()));
			}
			final CallNode<STATE> node = worklist.poll();
			final STATE state = node.getState();
			if (mAbstraction.getFinalStates().contains(state)) {
				mRootFinalStates.add(node);
				if (node.getDepth() > 0) {
					mRootPendingErrors.add(node);
				}
			}
			if (mRootSealedStates.contains(node)) {
				// An error imported from a summarized callee: reached only through its error edge, no successors.
				continue;
			}
			for (final OutgoingInternalTransition<LETTER, STATE> t : mAbstraction.internalSuccessors(state)) {
				enqueue(worklist, node.sibling(t.getSucc()));
			}
			for (final OutgoingCallTransition<LETTER, STATE> call : mAbstraction.callSuccessors(state)) {
				final String callee = call.getLetter().getSucceedingProcedure();
				if (mStacked.contains(callee)) {
					stackCallee(worklist, alternatives, node, call);
				} else if (mUnfolded.contains(callee)) {
					unfoldCallee(worklist, alternatives, node, call);
				} else {
					summarizeCallee(worklist, alternatives, node, call);
				}
			}
		}
		mRootVirtualCallEdges.putAll(combine(alternatives));
	}

	private void enqueue(final Deque<CallNode<STATE>> worklist, final CallNode<STATE> node) {
		if (mRootScopeStates.add(node)) {
			if (mRootScopeStates.size() > MAX_UNFOLDED_NODES) {
				// stackUnfoldingsThatDoNotFit() counted the copies of every procedure before any of this was built
				// and gave an activation record to whatever did not fit, so reaching this means that count was wrong.
				throw new AssertionError("the unfolded graph passed " + MAX_UNFOLDED_NODES + " nodes although the "
						+ "estimate said it would fit; unfolded " + mUnfolded + ", stacked " + mStacked);
			}
			worklist.add(node);
		}
	}

	/**
	 * Resolves one call site into a copy of the callee: a virtual edge carrying the call (see
	 * {@link #callEntryFormula}) into the copy's entry node, and one carrying the return out of each of its exit
	 * nodes. The copy's own states are reached from its entry node by the ordinary traversal, so its loops become
	 * nested loops of the graph being built.
	 */
	private void unfoldCallee(final Deque<CallNode<STATE>> worklist,
			final Map<CallNode<STATE>, Map<CallNode<STATE>, List<UnmodifiableTransFormula>>> alternatives,
			final CallNode<STATE> callSite, final OutgoingCallTransition<LETTER, STATE> call) {
		final ICallAction callAction = asCallAction(call.getLetter());
		final String callee = call.getLetter().getSucceedingProcedure();
		final CallNode<STATE> entryNode = callSite.enter(call.getSucc());
		addAlternative(alternatives, callSite, entryNode, callEntryFormula(callAction, callee, false));
		enqueue(worklist, entryNode);

		int returns = 0;
		for (final STATE exit : ProcedureCallGraph.computeExitStates(mAbstraction, ownStates(callee),
				Collections.singleton(callSite.getState()))) {
			for (final OutgoingReturnTransition<LETTER, STATE> ret : mAbstraction.returnSuccessorsGivenHier(exit,
					callSite.getState())) {
				final CallNode<STATE> afterReturn = callSite.sibling(ret.getSucc());
				addAlternative(alternatives, callSite.enter(exit), afterReturn,
						asReturnAction(ret.getLetter()).getAssignmentOfReturn());
				enqueue(worklist, afterReturn);
				returns++;
			}
		}
		if (returns == 0) {
			mLogger.info("KInduction: the unfolded call %s -> %s at %s never returns; only a violation inside the "
					+ "callee can be reached through it", ProcedureCallGraph.procedureOf(callSite.getState()),
					callee, callSite.getState());
		}
		mNumUnfoldedCallSites++;
	}

	/**
	 * Resolves one call site into an activation record: a virtual edge that pushes one and enters the callee's own
	 * entry node, and one that pops it again out of each of the callee's exit nodes.
	 * <p>
	 * Unlike {@link #unfoldCallee} this does <b>not</b> copy the callee: its states enter the graph as
	 * {@link CallNode#root} nodes, once, however many call sites reach them and however deep the recursion goes.
	 * Which activation the graph is in is a matter of {@code ki_sp}, not of which node it is at, and a recursive call
	 * is therefore an ordinary cycle of the graph that {@link LoopTreeFormulaBuilder} turns into an ordinary loop.
	 * <p>
	 * The return edges are what the id is for: every call site that can enter this callee reaches the same exit
	 * nodes, so the graph alone does not say where to go back to. The push records the id of <em>this</em> call site
	 * and the pop checks it, which makes the return deterministic without duplicating anything. The id is per call
	 * site <em>node</em>, not per call transition of the automaton, so a call from inside an unfolded copy returns
	 * into that copy rather than into one of its siblings.
	 */
	private void stackCallee(final Deque<CallNode<STATE>> worklist,
			final Map<CallNode<STATE>, Map<CallNode<STATE>, List<UnmodifiableTransFormula>>> alternatives,
			final CallNode<STATE> callSite, final OutgoingCallTransition<LETTER, STATE> call) {
		final ICallAction callAction = asCallAction(call.getLetter());
		final String callee = call.getLetter().getSucceedingProcedure();
		final String caller = ProcedureCallGraph.procedureOf(callSite.getState());
		final int returnSiteId = mNextReturnSiteId++;
		// Only a caller that can be re-entered while the callee runs needs a copy of its locals, and that is exactly
		// a caller that lies on a call cycle itself. A caller that cannot be re-entered still needs the return site
		// pushed, or the callee would not know where to go back to.
		final Collection<IProgramVar> toSave =
				mStacked.contains(caller) ? localsOf(Collections.singleton(caller)) : Collections.emptyList();

		final CallNode<STATE> entryNode = CallNode.root(call.getSucc());
		addAlternative(alternatives, callSite, entryNode, TransFormulaUtils.sequentialComposition(mLogger, mServices,
				mMgdScript, false, false, false, SimplificationTechnique.NONE,
				Arrays.asList(mCallStack.push(returnSiteId, toSave), callEntryFormula(callAction, callee, true))));
		enqueue(worklist, entryNode);

		int returns = 0;
		for (final STATE exit : ProcedureCallGraph.computeExitStates(mAbstraction, ownStates(callee),
				Collections.singleton(callSite.getState()))) {
			for (final OutgoingReturnTransition<LETTER, STATE> ret : mAbstraction.returnSuccessorsGivenHier(exit,
					callSite.getState())) {
				final UnmodifiableTransFormula returnTf = asReturnAction(ret.getLetter()).getAssignmentOfReturn();
				// The return assignment carries the result out of the activation that is being left, so it has to
				// read the callee's outparams before the pop overwrites them - in direct recursion they are the very
				// same variables as the caller's. Whatever it assigns must then not be restored on top of it.
				final Set<IProgramVar> toRestore = new LinkedHashSet<>(toSave);
				toRestore.removeAll(returnTf.getAssignedVars());
				addAlternative(alternatives, CallNode.root(exit), callSite.sibling(ret.getSucc()),
						TransFormulaUtils.sequentialComposition(mLogger, mServices, mMgdScript, false, false, false,
								SimplificationTechnique.NONE,
								Arrays.asList(returnTf, mCallStack.pop(returnSiteId, toRestore))));
				enqueue(worklist, callSite.sibling(ret.getSucc()));
				returns++;
			}
		}
		if (returns == 0) {
			mLogger.info("KInduction: the stacked call %s -> %s at %s never returns; only a violation inside the "
					+ "callee can be reached through it", caller, callee, callSite.getState());
		}
		mNumStackedCallSites++;
	}

	/** Every local variable, in- and outparams included, of each of {@code procedures}. */
	private Set<IProgramVar> localsOf(final Collection<String> procedures) {
		final Set<IProgramVar> result = new LinkedHashSet<>();
		for (final String procedure : procedures) {
			result.addAll(mCsToolkit.getSymbolTable().getLocals(procedure));
		}
		return result;
	}

	/**
	 * Moves unfolded procedures to {@link #mStacked} until the unfolding fits into {@link #MAX_UNFOLDED_NODES}.
	 * <p>
	 * Unfolding is exponential in the depth of the call graph times the number of call sites per procedure, so a
	 * program can ask for arbitrarily many nodes. How many it asks for does not have to be found out by unfolding
	 * until it is too late: a procedure gets one copy per copy of each of its callers, which is one pass over the
	 * call graph from the entry procedures downwards. A procedure that is stack-encoded instead contributes its
	 * states once, so stacking the worst offender and recomputing converges.
	 */
	private void stackUnfoldingsThatDoNotFit(final List<String> order, final Set<String> entryProcedures) {
		while (true) {
			final Map<String, Long> copies = estimateCopies(order, entryProcedures);
			long total = 0;
			String worst = null;
			long worstNodes = -1;
			for (final Map.Entry<String, Long> entry : copies.entrySet()) {
				final long nodes = entry.getValue() * ownStates(entry.getKey()).size();
				total += nodes;
				if (mUnfolded.contains(entry.getKey()) && nodes > worstNodes) {
					worst = entry.getKey();
					worstNodes = nodes;
				}
			}
			if (total <= MAX_UNFOLDED_NODES) {
				return;
			}
			if (worst == null) {
				// Nothing left to stack: the graph is this big because the procedures themselves are, not because
				// they are copied. Unfolding would not shrink it and neither would an activation record.
				throw new UnsupportedOperationException("the checkpoint graph of this program has about " + total
						+ " nodes, past the " + MAX_UNFOLDED_NODES + " k-induction is willing to build, and none of "
						+ "that is unfolding that could be replaced by an activation record");
			}
			mLogger.info("KInduction: unfolding %s would take about %d node(s) of an estimated %d; giving it an "
					+ "activation record instead", worst, worstNodes, total);
			mUnfolded.remove(worst);
			mStacked.add(worst);
		}
	}

	/**
	 * How many copies of each procedure the unfolded graph would hold. An entry procedure and a stack-encoded
	 * procedure occur once; an unfolded procedure occurs once per call site in each copy of each of its callers; a
	 * summarized procedure does not occur at all, its states stay in its own scope.
	 */
	private Map<String, Long> estimateCopies(final List<String> order, final Set<String> entryProcedures) {
		final Map<String, Long> copies = new LinkedHashMap<>();
		final List<String> callerFirst = new ArrayList<>(order);
		Collections.reverse(callerFirst);
		for (final String procedure : callerFirst) {
			final long own;
			if (entryProcedures.contains(procedure) || mStacked.contains(procedure)) {
				own = 1;
			} else if (mUnfolded.contains(procedure)) {
				own = copies.getOrDefault(procedure, 0L);
			} else {
				continue;
			}
			copies.put(procedure, own);
			if (own == 0) {
				continue;
			}
			for (final STATE state : ownStates(procedure)) {
				for (final OutgoingCallTransition<LETTER, STATE> call : mAbstraction.callSuccessors(state)) {
					final String callee = call.getLetter().getSucceedingProcedure();
					if (mUnfolded.contains(callee)) {
						copies.merge(callee, own, Long::sum);
					}
				}
			}
		}
		return copies;
	}

	/** Resolves one call site of the root graph into summary and error edges, as {@link #buildVirtualEdges} does. */
	private void summarizeCallee(final Deque<CallNode<STATE>> worklist,
			final Map<CallNode<STATE>, Map<CallNode<STATE>, List<UnmodifiableTransFormula>>> alternatives,
			final CallNode<STATE> callSite, final OutgoingCallTransition<LETTER, STATE> call) {
		final Set<CallNode<STATE>> imported = new LinkedHashSet<>();
		// A map of this call site's own edges, so that only the nodes it creates have to be enqueued.
		final Map<CallNode<STATE>, Map<CallNode<STATE>, List<UnmodifiableTransFormula>>> mine =
				new LinkedHashMap<>();
		resolveBySummary(ProcedureCallGraph.procedureOf(callSite.getState()), callSite.getState(), call,
				new INodeSpace<STATE, CallNode<STATE>>() {
					@Override
					public CallNode<STATE> sibling(final STATE state) {
						return callSite.sibling(state);
					}

					@Override
					public CallNode<STATE> enter(final STATE calleeState) {
						return callSite.enter(calleeState);
					}
				}, mine, imported);
		for (final CallNode<STATE> error : imported) {
			mRootSealedStates.add(error);
			mRootPendingErrors.add(error);
		}
		for (final Map.Entry<CallNode<STATE>, Map<CallNode<STATE>, List<UnmodifiableTransFormula>>> from : mine
				.entrySet()) {
			for (final Map.Entry<CallNode<STATE>, List<UnmodifiableTransFormula>> to : from.getValue().entrySet()) {
				for (final UnmodifiableTransFormula formula : to.getValue()) {
					addAlternative(alternatives, from.getKey(), to.getKey(), formula);
				}
				enqueue(worklist, to.getKey());
			}
		}
		mNumSummarizedCallSites++;
	}

	// ----------------------------------------------------------------------------------------------------------
	// Summary edges
	// ----------------------------------------------------------------------------------------------------------

	private static Set<String> callReachable(final ProcedureCallGraph callGraph, final Set<String> entries) {
		final Set<String> visited = new LinkedHashSet<>(entries);
		final Deque<String> worklist = new ArrayDeque<>(entries);
		while (!worklist.isEmpty()) {
			for (final String callee : callGraph.getCallees(worklist.poll())) {
				if (visited.add(callee)) {
					worklist.add(callee);
				}
			}
		}
		return visited;
	}

	private static Set<String> union(final Set<String> a, final Set<String> b) {
		final Set<String> result = new LinkedHashSet<>(a);
		result.addAll(b);
		return result;
	}

	private Set<STATE> ownStates(final String procedure) {
		final Set<STATE> result = mStatesByProcedure.get(procedure);
		if (result == null || result.isEmpty()) {
			throw new UnsupportedOperationException("procedure " + procedure + " is called but the abstraction has "
					+ "no state of it, so its body can neither be summarized nor unfolded");
		}
		return result;
	}

	/** The states a call transition enters {@code procedure} at, or its initial states if nothing calls it. */
	private Set<STATE> entryStates(final String procedure) {
		final Set<STATE> called = mEntryStates.get(procedure);
		if (called != null && !called.isEmpty()) {
			return called;
		}
		return ProcedureCallGraph.intersect(mAbstraction.getInitialStates(), ownStates(procedure));
	}

	private void collectEntryStates() {
		for (final STATE state : mAbstraction.getStates()) {
			for (final OutgoingCallTransition<LETTER, STATE> call : mAbstraction.callSuccessors(state)) {
				mEntryStates.computeIfAbsent(call.getLetter().getSucceedingProcedure(), k -> new LinkedHashSet<>())
						.add(call.getSucc());
			}
		}
	}

	/**
	 * Every virtual call edge of {@code caller}, in its own state space: one per (call transition, exit state of
	 * the callee) pair for the normal return, and one per (call transition, error state inside the callee) pair
	 * for a violation that never returns. Fills {@code imported} with the error states the edges point at. Only
	 * called for a summarizable procedure, so every callee has a summary.
	 */
	private Map<STATE, Map<STATE, UnmodifiableTransFormula>> buildVirtualEdges(final String caller,
			final Set<STATE> imported) {
		final Map<STATE, Map<STATE, List<UnmodifiableTransFormula>>> alternatives = new LinkedHashMap<>();
		final INodeSpace<STATE, STATE> identity = new INodeSpace<>() {
			@Override
			public STATE sibling(final STATE state) {
				return state;
			}

			@Override
			public STATE enter(final STATE calleeState) {
				return calleeState;
			}
		};
		for (final STATE callSite : ownStates(caller)) {
			for (final OutgoingCallTransition<LETTER, STATE> call : mAbstraction.callSuccessors(callSite)) {
				resolveBySummary(caller, callSite, call, identity, alternatives, imported);
			}
		}
		return combine(alternatives);
	}

	/**
	 * The summary and error edges of one call site, expressed in whatever node space {@code space} describes: the
	 * caller's own states when a procedure's scope is built, {@link CallNode}s when the root graph is.
	 */
	private <N> void resolveBySummary(final String caller, final STATE callSite,
			final OutgoingCallTransition<LETTER, STATE> call, final INodeSpace<STATE, N> space,
			final Map<N, Map<N, List<UnmodifiableTransFormula>>> alternatives, final Set<N> imported) {
		final ICallAction callAction = asCallAction(call.getLetter());
		final String callee = call.getLetter().getSucceedingProcedure();
		final ScopeData calleeData = mScopeData.get(callee);
		if (calleeData == null) {
			throw new AssertionError("callee " + callee + " of " + caller + " has no summary, although it was "
					+ "neither marked for unfolding nor left unprocessed by ProcedureCallGraph's ordering");
		}
		final Set<STATE> entry = Collections.singleton(call.getSucc());
		final Set<STATE> reachable = reachableInScope(calleeData, entry);

		int edges = 0;
		for (final STATE exit : ProcedureCallGraph.computeExitStates(mAbstraction, ownStates(callee),
				Collections.singleton(callSite))) {
			if (!reachable.contains(exit)) {
				continue;
			}
			final UnmodifiableTransFormula summary = formulaBetween(calleeData, entry, exit);
			if (summary == null) {
				continue;
			}
			for (final OutgoingReturnTransition<LETTER, STATE> ret : mAbstraction.returnSuccessorsGivenHier(exit,
					callSite)) {
				final UnmodifiableTransFormula edge = ProcedureCallGraph.computeVirtualEdge(mServices, mLogger,
						mCsToolkit, mMgdScript, callAction, callee, summary,
						asReturnAction(ret.getLetter()).getAssignmentOfReturn());
				addAlternative(alternatives, space.sibling(callSite), space.sibling(ret.getSucc()), edge);
				edges++;
			}
		}
		for (final STATE error : calleeData.mErrorStates) {
			if (!reachable.contains(error)) {
				continue;
			}
			final UnmodifiableTransFormula toError = formulaBetween(calleeData, entry, error);
			if (toError == null) {
				continue;
			}
			final N errorNode = space.enter(error);
			addAlternative(alternatives, space.sibling(callSite), errorNode,
					pendingCallToError(caller, callAction, callee, error, toError));
			imported.add(errorNode);
			edges++;
		}
		if (edges == 0) {
			// Legitimate: a call to a procedure that never returns (abort, exit) and contains no reachable
			// error is a dead end. Logged because it silently removes the call site from the graph.
			mLogger.info("KInduction: call %s -> %s at %s has no virtual edge: the callee neither returns "
					+ "nor reaches an error on any path from %s", caller, callee, callSite, call.getSucc());
		}
	}

	private <N> Map<N, Map<N, UnmodifiableTransFormula>> combine(
			final Map<N, Map<N, List<UnmodifiableTransFormula>>> alternatives) {
		final Map<N, Map<N, UnmodifiableTransFormula>> result = new LinkedHashMap<>();
		for (final Map.Entry<N, Map<N, List<UnmodifiableTransFormula>>> from : alternatives.entrySet()) {
			final Map<N, UnmodifiableTransFormula> combined = new LinkedHashMap<>();
			for (final Map.Entry<N, List<UnmodifiableTransFormula>> to : from.getValue().entrySet()) {
				// Several call transitions, exits or returns can join the same pair of nodes; their union is the
				// edge, exactly as for the alternatives of an ordinary checkpoint edge.
				combined.put(to.getKey(),
						LoopTreeFormulaBuilder.combineAlternatives(mLogger, mServices, mMgdScript, to.getValue()));
			}
			result.put(from.getKey(), combined);
		}
		return result;
	}

	private <N> void addAlternative(final Map<N, Map<N, List<UnmodifiableTransFormula>>> alternatives, final N from,
			final N to, final UnmodifiableTransFormula formula) {
		alternatives.computeIfAbsent(from, k -> new LinkedHashMap<>()).computeIfAbsent(to, k -> new ArrayList<>())
				.add(formula);
	}

	/**
	 * The formula of every path through {@code data}'s procedure from {@code inits} to {@code target}, or
	 * {@code null} if there is none. Only called for a summarizable procedure, whose graph has no loop.
	 */
	private UnmodifiableTransFormula formulaBetween(final ScopeData data, final Set<STATE> inits,
			final STATE target) {
		mNumBuilds++;
		final LoopTree<STATE> tree = new LoopTreeFormulaBuilder<>(mServices, mLogger, mMgdScript, mAbstraction,
				data.mScopeStates, inits, Collections.singleton(target), data.mVirtualEdges, data.mSealed).build();
		if (!tree.getLoops().isEmpty()) {
			throw new AssertionError("procedure " + data.mProcedure + " was summarized although its graph has a "
					+ "loop; classify() should have marked it for unfolding");
		}
		return tree.getRoot().getEdge(Checkpoint.init(), Checkpoint.fin());
	}

	/**
	 * The formula of a call that never returns because the callee (or something it calls) reaches the error state
	 * {@code error}. The call stays pending, which is what
	 * {@link TransFormulaUtils#sequentialCompositionWithPendingCall} describes; {@code error} may lie deeper than
	 * the direct callee, so the procedure at the end is the one {@code error} belongs to.
	 */
	private UnmodifiableTransFormula pendingCallToError(final String caller, final ICallAction callAction,
			final String callee, final STATE error, final UnmodifiableTransFormula toError) {
		final String procAtEnd = ProcedureCallGraph.procedureOf(error);
		final UnmodifiableTransFormula oldVarsAssignment =
				mCsToolkit.getOldVarsAssignmentCache().getOldVarsAssignment(callee);
		final UnmodifiableTransFormula globalVarsAssignment =
				mCsToolkit.getOldVarsAssignmentCache().getGlobalVarsAssignment(callee);
		final Set<IProgramNonOldVar> modifiableGlobalsAtEnd =
				mCsToolkit.getModifiableGlobalsTable().getModifiedBoogieVars(procAtEnd);
		return TransFormulaUtils.sequentialCompositionWithPendingCall(mMgdScript, false, false, false,
				Collections.emptyList(), callAction.getLocalVarsAssignment(), oldVarsAssignment, globalVarsAssignment,
				scopeToCallerAndCallee(toError, caller, callee), mLogger, mServices, modifiableGlobalsAtEnd,
				SimplificationTechnique.NONE, mCsToolkit.getSymbolTable(), caller, caller, callee, procAtEnd,
				mCsToolkit.getModifiableGlobalsTable());
	}

	/**
	 * {@code toError} with the locals of every procedure other than {@code caller} and {@code callee} dropped from
	 * its interface.
	 * <p>
	 * {@link TransFormulaUtils#sequentialCompositionWithPendingCall} classifies each variable of the formula it is
	 * given as belonging to the caller, to the callee, or to neither - and the third case is an
	 * {@link AssertionError} ("local var neither from caller nor callee"), because the primitive knows only those two
	 * procedures. The error this call runs into may lie deeper than the direct callee, though, and then
	 * {@code toError} spans several activations and mentions the locals of all of them.
	 * <p>
	 * Dropping them is what the formula means anyway, not an approximation of it. An inVar stands for the value the
	 * variable has where the composed formula starts, which is the callee's entry - at that point the deeper
	 * activation does not exist and its locals hold nothing, so leaving the inVar in would claim a relationship
	 * between two values that never coexist; removing it turns the variable into an existentially quantified aux var,
	 * which is what "unconstrained" is. An outVar stands for a value at the error state, and an error node is a dead
	 * end of the graph ({@code unfold} stops at a sealed state), so nothing ever reads it.
	 */
	private UnmodifiableTransFormula scopeToCallerAndCallee(final UnmodifiableTransFormula toError,
			final String caller, final String callee) {
		final List<IProgramVar> inVarsToRemove = new ArrayList<>();
		for (final IProgramVar pv : toError.getInVars().keySet()) {
			if (isLocalOfOtherProcedure(pv, caller, callee)) {
				inVarsToRemove.add(pv);
			}
		}
		final List<IProgramVar> outVarsToRemove = new ArrayList<>();
		for (final IProgramVar pv : toError.getOutVars().keySet()) {
			if (isLocalOfOtherProcedure(pv, caller, callee)) {
				outVarsToRemove.add(pv);
			}
		}
		if (inVarsToRemove.isEmpty() && outVarsToRemove.isEmpty()) {
			return toError;
		}
		mLogger.debug("KInduction: dropping %d in- and %d outvar(s) of procedures other than %s and %s from a "
				+ "pending call to an error", inVarsToRemove.size(), outVarsToRemove.size(), caller, callee);
		return TransFormulaBuilder.constructCopy(mMgdScript, toError, inVarsToRemove, outVarsToRemove,
				Collections.emptyMap());
	}

	private static boolean isLocalOfOtherProcedure(final IProgramVar pv, final String caller, final String callee) {
		return !pv.isGlobal() && !caller.equals(pv.getProcedure()) && !callee.equals(pv.getProcedure());
	}

	/**
	 * What entering {@code callee} does to the state of the flat graph, i.e. the first half of what
	 * {@link TransFormulaUtils#sequentialCompositionWithCallAndReturn} composes for a summarized call: the
	 * parameter assignment, the snapshot of the oldvars of the globals the callee may modify, and the globals
	 * assignment. The matching second half is the return's own assignment, which is the formula of the virtual
	 * edge leaving the unfolded copy.
	 * <p>
	 * The callee's locals are havoced first. In an unfolded graph they are ordinary state variables that outlive
	 * the activation, so without this they would still hold the values of the previous call to the same procedure
	 * - an under-approximation, which could prove an unsafe program safe. A summarized call needs no such step
	 * because {@code sequentialCompositionWithCallAndReturn} projects the callee's locals out of the summary,
	 * which has the same effect. {@link KInductionCounterexampleBuilder} makes them fresh constants for the same
	 * reason.
	 * <p>
	 * Whether the havoc comes before or after the parameter assignment only matters when the caller and the callee
	 * are the same procedure, which is to say for a directly recursive call: then the actual parameters the call
	 * reads <em>are</em> locals of the callee, and havocing first would destroy them before they are passed. For a
	 * call between two different procedures the two steps write disjoint variables and commute, so
	 * {@code havocAfterParameters} only has to be set where recursion is possible.
	 * <p>
	 * The parameter assignment is composed as the intraprocedural formula {@link #keepReadVariables} makes of it,
	 * so the caller's arguments keep their values across the call.
	 */
	private UnmodifiableTransFormula callEntryFormula(final ICallAction callAction, final String callee,
			final boolean havocAfterParameters) {
		final UnmodifiableTransFormula callTf = keepReadVariables(callAction.getLocalVarsAssignment());
		final UnmodifiableTransFormula oldVarsAssignment =
				mCsToolkit.getOldVarsAssignmentCache().getOldVarsAssignment(callee);
		final UnmodifiableTransFormula globalVarsAssignment =
				mCsToolkit.getOldVarsAssignmentCache().getGlobalVarsAssignment(callee);
		final Set<IProgramVar> havoced = new LinkedHashSet<>();
		for (final ILocalProgramVar local : mCsToolkit.getSymbolTable().getLocals(callee)) {
			if (!callTf.getAssignedVars().contains(local)) {
				havoced.add(local);
			}
		}
		final UnmodifiableTransFormula havoc = TransFormulaUtils.constructHavoc(havoced, mMgdScript);
		final List<UnmodifiableTransFormula> parts = havocAfterParameters
				? Arrays.asList(callTf, havoc, oldVarsAssignment, globalVarsAssignment)
				: Arrays.asList(havoc, callTf, oldVarsAssignment, globalVarsAssignment);
		return TransFormulaUtils.sequentialComposition(mLogger, mServices, mMgdScript, false, false, false,
				SimplificationTechnique.NONE, parts);
	}

	/**
	 * {@code callTf} with an outVar for every inVar that has none, the same {@link TermVariable}, i.e. the variable
	 * keeps its value.
	 * <p>
	 * A call's parameter assignment reads the caller's arguments without writing them. For the interprocedural
	 * compositions it is made for that is harmless, the caller's scope is restored at the return. For
	 * {@link TransFormulaUtils#sequentialComposition}, however, an inVar without an outVar is havoced
	 * ({@link TransFormulaUtils#computeAssignedVars}), and in the flat graph the caller's variables live on after the
	 * call - so every argument would lose its value at the call, an over-approximation under which the base case
	 * reports violations that no run has. It also keeps a read-only local of the callee (the argument of a
	 * recursive call) out of {@link UnmodifiableTransFormula#getAssignedVars()}, so the activation havocs it as it
	 * havocs every other local; {@link KInductionCounterexampleBuilder} does the same.
	 */
	private UnmodifiableTransFormula keepReadVariables(final UnmodifiableTransFormula callTf) {
		final Map<IProgramVar, TermVariable> kept = new LinkedHashMap<>();
		for (final Map.Entry<IProgramVar, TermVariable> in : callTf.getInVars().entrySet()) {
			if (!callTf.getOutVars().containsKey(in.getKey())) {
				kept.put(in.getKey(), in.getValue());
			}
		}
		if (kept.isEmpty()) {
			return callTf;
		}
		return TransFormulaBuilder.constructCopy(mMgdScript, callTf, Collections.emptyList(), Collections.emptyList(),
				kept);
	}

	// ----------------------------------------------------------------------------------------------------------
	// Traversal of one procedure's own scope
	// ----------------------------------------------------------------------------------------------------------

	/**
	 * Every way to leave {@code state} inside {@code data}'s scope, over the same edges
	 * {@link LoopTreeFormulaBuilder} would use: internal transitions that stay in the scope and virtual call
	 * edges, nothing else. A sealed state has none.
	 */
	private List<STATE> scopeSuccessors(final ScopeData data, final STATE state) {
		if (data.mSealed.contains(state)) {
			return Collections.emptyList();
		}
		final List<STATE> result = new ArrayList<>();
		for (final OutgoingInternalTransition<LETTER, STATE> t : mAbstraction.internalSuccessors(state)) {
			if (data.mScopeStates.contains(t.getSucc())) {
				result.add(t.getSucc());
			}
		}
		result.addAll(data.mVirtualEdges.getOrDefault(state, Collections.emptyMap()).keySet());
		return result;
	}

	/**
	 * The states of {@code data}'s scope reachable from {@code inits}. Only used to skip exit and error states
	 * that no path can reach, so that no checkpoint graph is built for them.
	 */
	private Set<STATE> reachableInScope(final ScopeData data, final Set<STATE> inits) {
		final Set<STATE> visited = new LinkedHashSet<>(inits);
		final Deque<STATE> worklist = new ArrayDeque<>(inits);
		while (!worklist.isEmpty()) {
			for (final STATE succ : scopeSuccessors(data, worklist.poll())) {
				if (visited.add(succ)) {
					worklist.add(succ);
				}
			}
		}
		return visited;
	}

	/**
	 * Whether {@code data}'s scope has a cycle reachable from {@code inits}, i.e. whether the procedure contains a
	 * loop and therefore has no single loop-free entry-to-exit formula. Iterative depth-first search, because a
	 * deep program must not overflow the stack; this only has to answer yes or no, so unlike
	 * {@link LoopTreeFormulaBuilder} it composes no formula.
	 */
	private boolean hasCycleInScope(final ScopeData data, final Set<STATE> inits) {
		final Set<STATE> finished = new LinkedHashSet<>();
		final Set<STATE> onPath = new LinkedHashSet<>();
		final Deque<STATE> path = new ArrayDeque<>();
		final Deque<Iterator<STATE>> pending = new ArrayDeque<>();
		for (final STATE init : inits) {
			if (finished.contains(init)) {
				continue;
			}
			path.push(init);
			onPath.add(init);
			pending.push(scopeSuccessors(data, init).iterator());
			while (!path.isEmpty()) {
				final Iterator<STATE> it = pending.peek();
				if (!it.hasNext()) {
					onPath.remove(path.peek());
					finished.add(path.pop());
					pending.pop();
					continue;
				}
				final STATE succ = it.next();
				if (onPath.contains(succ)) {
					return true;
				}
				if (finished.contains(succ)) {
					continue;
				}
				path.push(succ);
				onPath.add(succ);
				pending.push(scopeSuccessors(data, succ).iterator());
			}
		}
		return false;
	}

	private static ICallAction asCallAction(final IAction letter) {
		if (!(letter instanceof ICallAction)) {
			throw new UnsupportedOperationException("the call letter " + letter + " is a "
					+ letter.getClass().getSimpleName() + ", not an ICallAction, so it has no local variable "
					+ "assignment and the call cannot be resolved");
		}
		return (ICallAction) letter;
	}

	private static IReturnAction asReturnAction(final IAction letter) {
		if (!(letter instanceof IReturnAction)) {
			throw new UnsupportedOperationException("the return letter " + letter + " is a "
					+ letter.getClass().getSimpleName() + ", not an IReturnAction, so it has no assignment of the "
					+ "return value and the call cannot be resolved");
		}
		return (IReturnAction) letter;
	}
}
