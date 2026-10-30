/*
 * Copyright (C) 2026 University of Freiburg
 * Copyright (C) 2026 LMU Munich
 * Copyright (C) 2026 Max Barth (Max.Barth@lmu.de)
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.invariants;

import java.math.BigInteger;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.invariants.InvariantSubscription.RunningQuery;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.CallNode;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.KInductionQuery;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.KInductionQuery.Invariant;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.KInductionQuery.Kind;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.PcTransitionSystem;

/**
 * The probation of the {@link InvariantSupplier}: finds out whether an invariant makes a query of k-induction slow.
 * <p>
 * A query of k-induction is due for probation once it runs longer than the limit, {@code factor} times the previous
 * query of its kind but at least {@code minimum}. The supplier then asks the same query, via {@link KInductionQuery} on
 * its own transition system and solver, with earlier invariants, each under the limit. Only an invariant that answers
 * within the limit replaces the current one, so a query that is slow for another reason never costs k-induction more
 * than the time the supplier spends on its own solver.
 * <p>
 * Only used by the supplier's thread.
 *
 * @author Max Barth (Max.Barth@lmu.de)
 */
final class InvariantProbation {

	private final ILogger mLogger;
	private final ManagedScript mScript;
	private final int mFactor;
	private final long mMinimumMillis;
	// The per-query timeout of the supplier's solver, restored after a probe.
	private final long mSolverTimeoutMillis;
	private final Object mLock = new Object();
	private final Map<InvariantSubscription, RunningQuery> mProbed = new HashMap<>();
	private KInductionQuery<CallNode<IPredicate>> mQuery;
	private PcTransitionSystem<CallNode<IPredicate>> mSystem;

	/**
	 * @param script
	 *            the supplier's script, backed by z3
	 * @param solverTimeoutMillis
	 *            the per-query timeout the supplier's solver has otherwise
	 */
	InvariantProbation(final ILogger logger, final ManagedScript script, final int factor, final long minimumMillis,
			final long solverTimeoutMillis) {
		if (factor < 1 || minimumMillis <= 0 || solverTimeoutMillis <= 0) {
			throw new IllegalArgumentException("invalid probation limit: factor " + factor + ", minimum "
					+ minimumMillis + " ms, solver timeout " + solverTimeoutMillis + " ms");
		}
		mLogger = logger;
		mScript = script;
		mFactor = factor;
		mMinimumMillis = minimumMillis;
		mSolverTimeoutMillis = solverTimeoutMillis;
	}

	/**
	 * @return how long a query of {@code kind} of the subscriber may run before it is on probation
	 */
	long limitMillis(final InvariantSubscription subscription, final Kind kind) {
		return Math.max(mMinimumMillis, mFactor * subscription.previousMillis(kind));
	}

	/**
	 * @return the query of the subscriber that is due for probation now, or {@code null}; a query is due only once
	 */
	RunningQuery due(final InvariantSubscription subscription) {
		final RunningQuery query = subscription.runningQuery();
		if (query == null || query.equals(mProbed.get(subscription))) {
			return null;
		}
		final long runningMillis = (System.nanoTime() - query.startNanos()) / 1_000_000;
		if (runningMillis < limitMillis(subscription, query.kind())) {
			return null;
		}
		mProbed.put(subscription, query);
		return query;
	}

	/**
	 * Asks the query of {@code kind} for {@code k} on the supplier's solver.
	 *
	 * @param invariants
	 *            conjuncts of the invariant per location, as published
	 * @return the answer, {@link LBool#UNKNOWN} if the solver did not answer within {@code limitMillis}
	 */
	LBool ask(final InductivenessChecker checker, final Kind kind, final int k,
			final Map<IcfgLocation, Set<Term>> invariants, final long limitMillis) {
		final PcTransitionSystem<CallNode<IPredicate>> system = checker.getSystem();
		final KInductionQuery<CallNode<IPredicate>> query = getQuery(checker);
		final Map<Integer, Invariant> atHeads = new HashMap<>();
		for (final Map.Entry<CallNode<IPredicate>, Integer> head : system.getHeadNodes().entrySet()) {
			final Set<Term> conjuncts = invariants.getOrDefault(InvariantSupplier.locationOf(head.getKey().getState()),
					Collections.emptySet());
			if (conjuncts.isEmpty()) {
				continue;
			}
			final Term term = SmtUtils.and(mScript.getScript(), conjuncts);
			// As k-induction does: an invariant over a variable of no transition is left out.
			final Map<IProgramVar, TermVariable> vars = query.variablesOf(term);
			if (vars != null) {
				atHeads.put(head.getValue(), new Invariant(term, vars));
			}
		}
		mScript.lock(mLock);
		try {
			final List<Term> assertions = query.prepare(k, atHeads);
			mScript.push(mLock, 1);
			try {
				query.assertQuery(kind, k, assertions);
				mScript.getScript().setOption(":timeout", BigInteger.valueOf(limitMillis));
				try {
					return mScript.checkSat(mLock);
				} finally {
					mScript.getScript().setOption(":timeout", BigInteger.valueOf(mSolverTimeoutMillis));
				}
			} finally {
				mScript.pop(mLock, 1);
			}
		} finally {
			mScript.unlock(mLock);
		}
	}

	private KInductionQuery<CallNode<IPredicate>> getQuery(final InductivenessChecker checker) {
		if (mQuery == null || mSystem != checker.getSystem()) {
			mSystem = checker.getSystem();
			// The checker's constants: both declare the constants of the program variables on the same script.
			mQuery = new KInductionQuery<>(mSystem, mScript, mLock, checker.constants("probe"));
		}
		return mQuery;
	}
}
