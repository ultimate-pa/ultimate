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
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.scc.DefaultSccComputation;
import de.uni_freiburg.informatik.ultimate.util.scc.StronglyConnectedComponent;

/**
 * Builds the procedure call graph of a nested word automaton (nodes = procedure names, edges = "caller calls
 * callee", derived from the automaton's call transitions) and answers the two questions its interprocedural
 * consumers ask of it: in which order to process the procedures, and which of them lie on a call cycle.
 * <p>
 * A call cycle matters because {@link LoopTreeFormulaBuilder}'s virtual call edges (see its class javadoc) need
 * their callee's summary to already exist as a finished formula, which is undefined for a cycle. A consumer that
 * can encode a cycle some other way asks {@link #getSccsCalleeFirst(java.util.Collection)}, which keeps the
 * procedures of a cycle together in one component, and {@link #getRecursiveSccs(java.util.Collection)}, which
 * names them - {@link ProcedureSummaries} gives those an activation record instead of a summary, see
 * {@link CallStack}. A consumer that cannot asks {@link #getProceduresCalleeFirst()}, which refuses a recursive
 * call graph with an {@link UnsupportedOperationException} naming the offending call and the full cycle.
 * <p>
 * Either way the order is the one every interprocedural consumer needs: every callee fully processed (and thus
 * already holding a summary, if it needs one) before any of its callers. {@link ProcedureSummaries} uses it that
 * way; the small per-procedure helpers (state grouping, exit states, the call/summary/return composition) live here.
 */
public final class ProcedureCallGraph {

	private final ILogger mLogger;
	private final Set<String> mProcedures = new LinkedHashSet<>();
	private final Set<String> mEntryProcedures = new LinkedHashSet<>();
	private final HashRelation<String, String> mCalls = new HashRelation<>();

	public <LETTER extends IAction, STATE> ProcedureCallGraph(final ILogger logger,
			final INestedWordAutomaton<LETTER, STATE> abstraction) {
		mLogger = logger;
		for (final STATE state : abstraction.getStates()) {
			mProcedures.add(procedureOf(state));
		}
		for (final STATE init : abstraction.getInitialStates()) {
			mEntryProcedures.add(procedureOf(init));
		}
		for (final STATE state : abstraction.getStates()) {
			for (final OutgoingCallTransition<LETTER, STATE> t : abstraction.callSuccessors(state)) {
				mCalls.addPair(t.getLetter().getPrecedingProcedure(), t.getLetter().getSucceedingProcedure());
			}
		}
	}

	/**
	 * The procedure a state belongs to. Only an {@link ISLPredicate} names a program point and therefore a
	 * procedure; anything else is refused here rather than further down as a {@link ClassCastException}.
	 */
	public static <STATE> String procedureOf(final STATE state) {
		if (!(state instanceof ISLPredicate)) {
			throw new UnsupportedOperationException("abstraction state " + state + " is a "
					+ state.getClass().getSimpleName() + ", not an ISLPredicate, so it has no program point and no "
					+ "procedure; an interprocedural analysis cannot scope it");
		}
		return ((ISLPredicate) state).getProgramPoint().getProcedure();
	}

	public Set<String> getEntryProcedures() {
		return mEntryProcedures;
	}

	/** Every procedure that {@code caller} calls directly. */
	public Set<String> getCallees(final String caller) {
		return mCalls.getImage(caller);
	}

	/**
	 * Every procedure, in an order where every callee occurs before every one of its callers. Throws if the call
	 * graph is recursive (a procedure transitively/mutually calls itself).
	 * <p>
	 * For a caller that can handle recursion, {@link #getSccsCalleeFirst(Collection)} is the same order without the
	 * refusal: it keeps the procedures of a call cycle together in one component instead of rejecting them.
	 */
	public List<String> getProceduresCalleeFirst() {
		final List<String> result = new ArrayList<>();
		for (final Set<String> scc : getSccsCalleeFirst(mProcedures)) {
			if (scc.size() > 1 || mCalls.getImage(scc.iterator().next()).contains(scc.iterator().next())) {
				final String caller = someCallerInside(scc);
				throw new UnsupportedOperationException("Recursion is not supported: procedure "
						+ someCalleeInside(scc, caller) + " is (transitively) reachable from itself via a call from "
						+ caller + "; the full recursive call cycle is " + scc);
			}
			result.add(scc.iterator().next());
		}
		return result;
	}

	/**
	 * The strongly connected components of the call graph restricted to {@code scope}, in an order where every
	 * component occurs before every component that calls into it.
	 * <p>
	 * A component with more than one procedure, or a single procedure that calls itself, is a call cycle: its
	 * procedures have no summary, because a summary of one of them would need the summaries of all of them. Every
	 * other component is a single procedure and the order is the plain callee-first order. Restricting to
	 * {@code scope} matters: a call cycle among procedures that no entry procedure can reach says nothing about the
	 * program being analysed, and grouping it in anyway would encode procedures that are never executed.
	 */
	public List<Set<String>> getSccsCalleeFirst(final Collection<String> scope) {
		final Set<String> inScope = new LinkedHashSet<>(scope);
		final DefaultSccComputation<String> sccComputation =
				new DefaultSccComputation<>(mLogger, node -> calleesInside(node, inScope).iterator(), inScope.size(),
						inScope);
		final List<Set<String>> result = new ArrayList<>();
		for (final StronglyConnectedComponent<String> comp : sccComputation.getSCCs()) {
			result.add(comp.getNodes());
		}
		return result;
	}

	/**
	 * The components of {@link #getSccsCalleeFirst(Collection)} that are call cycles, i.e. the procedures that cannot
	 * be summarized because they are (mutually) recursive.
	 */
	public List<Set<String>> getRecursiveSccs(final Collection<String> scope) {
		final Set<String> inScope = new LinkedHashSet<>(scope);
		final DefaultSccComputation<String> sccComputation =
				new DefaultSccComputation<>(mLogger, node -> calleesInside(node, inScope).iterator(), inScope.size(),
						inScope);
		final List<Set<String>> result = new ArrayList<>();
		for (final StronglyConnectedComponent<String> ball : sccComputation.getBalls()) {
			result.add(ball.getNodes());
		}
		return result;
	}

	/** Every procedure that a chain of calls can reach from an entry procedure. */
	public Set<String> getReachableProcedures() {
		final Set<String> visited = new LinkedHashSet<>(mEntryProcedures);
		final Deque<String> worklist = new ArrayDeque<>(mEntryProcedures);
		while (!worklist.isEmpty()) {
			for (final String callee : getCallees(worklist.poll())) {
				if (visited.add(callee)) {
					worklist.add(callee);
				}
			}
		}
		return visited;
	}

	private Set<String> calleesInside(final String caller, final Set<String> scope) {
		final Set<String> result = new LinkedHashSet<>();
		for (final String callee : mCalls.getImage(caller)) {
			if (scope.contains(callee)) {
				result.add(callee);
			}
		}
		return result;
	}

	private String someCallerInside(final Set<String> cycle) {
		for (final String c : cycle) {
			for (final String d : mCalls.getImage(c)) {
				if (cycle.contains(d)) {
					return c;
				}
			}
		}
		throw new AssertionError("component " + cycle + " was reported as a call cycle but has no call inside it");
	}

	private String someCalleeInside(final Set<String> cycle, final String caller) {
		for (final String d : mCalls.getImage(caller)) {
			if (cycle.contains(d)) {
				return d;
			}
		}
		throw new AssertionError(caller + " was reported as a caller inside " + cycle + " but calls nothing in it");
	}

	// ----------------------------------------------------------------------------------------------------------
	// Helpers shared by the interprocedural consumers
	// ----------------------------------------------------------------------------------------------------------

	/** The states of the abstraction, grouped by the procedure they belong to. */
	public static <STATE> Map<String, Set<STATE>> groupStatesByProcedure(final Iterable<STATE> states) {
		final Map<String, Set<STATE>> result = new LinkedHashMap<>();
		for (final STATE state : states) {
			result.computeIfAbsent(procedureOf(state), k -> new LinkedHashSet<>()).add(state);
		}
		return result;
	}

	/**
	 * States in {@code scopeStates} with an outgoing return transition to at least one of {@code callSites} - a
	 * procedure's own normal-return points, call-site-agnostic (reused as the FINAL set for every caller's virtual
	 * edge into this procedure). {@code callSites} is every call site anywhere in the automaton that is known to
	 * call this procedure, so this is sound and complete without needing to query the automaton for "any return
	 * transition regardless of hier", which its API does not expose directly.
	 */
	public static <LETTER extends IAction, STATE> Set<STATE> computeExitStates(
			final INestedWordAutomaton<LETTER, STATE> abstraction, final Set<STATE> scopeStates,
			final Set<STATE> callSites) {
		final Set<STATE> result = new LinkedHashSet<>();
		for (final STATE state : scopeStates) {
			for (final STATE callSite : callSites) {
				if (abstraction.returnSuccessorsGivenHier(state, callSite).iterator().hasNext()) {
					result.add(state);
					break;
				}
			}
		}
		return result;
	}

	/** The elements of {@code a} that are also in {@code b}. */
	public static <STATE> Set<STATE> intersect(final Iterable<STATE> a, final Set<STATE> b) {
		final Set<STATE> result = new LinkedHashSet<>();
		for (final STATE s : a) {
			if (b.contains(s)) {
				result.add(s);
			}
		}
		return result;
	}

	/**
	 * The formula of a virtual call edge: the whole call-to-return span of one call site, i.e. the parameter
	 * assignment of the call, the callee's summary and the assignment of the return, composed by
	 * {@link TransFormulaUtils#sequentialCompositionWithCallAndReturn} - the primitive that gets the scoping of
	 * oldvars, modifiable globals and the callee's locals right, and the same one the rest of this codebase (e.g.
	 * {@code IcfgEdgeBuilder}) uses for this composition.
	 */
	public static UnmodifiableTransFormula computeVirtualEdge(final IUltimateServiceProvider services,
			final ILogger logger, final CfgSmtToolkit csToolkit, final ManagedScript mgdScript,
			final ICallAction callAction, final String callee, final UnmodifiableTransFormula calleeSummary,
			final UnmodifiableTransFormula returnTf) {
		final UnmodifiableTransFormula oldVarsAssignment =
				csToolkit.getOldVarsAssignmentCache().getOldVarsAssignment(callee);
		final UnmodifiableTransFormula globalVarsAssignment =
				csToolkit.getOldVarsAssignmentCache().getGlobalVarsAssignment(callee);
		final Set<IProgramNonOldVar> modifiableGlobals =
				csToolkit.getModifiableGlobalsTable().getModifiedBoogieVars(callee);
		return TransFormulaUtils.sequentialCompositionWithCallAndReturn(mgdScript, false, false, false,
				callAction.getLocalVarsAssignment(), oldVarsAssignment, globalVarsAssignment, calleeSummary, returnTf,
				logger, services, SimplificationTechnique.NONE, csToolkit.getSymbolTable(), modifiableGlobals);
	}
}
