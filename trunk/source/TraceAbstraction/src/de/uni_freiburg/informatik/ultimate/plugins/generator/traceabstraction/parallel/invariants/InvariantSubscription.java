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

import java.util.EnumMap;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.function.BooleanSupplier;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.CallNode;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.IInvariantSupplier;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.KInductionQuery.Kind;

/**
 * The outgoing channel of an {@link InvariantSupplier} for one consumer. The supplier puts the locations whose
 * invariant got stronger, each with its whole current invariant, into the queue; {@link #update()} takes them without
 * waiting, and {@link #getInvariant} copies the latest invariant of a location into the consumer's script.
 * <p>
 * Everything but {@link #offer} must be called by the thread that owns {@code target}.
 * <p>
 * The other way round, k-induction reports its queries here, and the supplier reads them to put a slow query on
 * probation ({@link #runningQuery}, {@link #previousMillis}) and may {@link #interrupt} it.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public final class InvariantSubscription implements IInvariantSupplier<CallNode<IPredicate>> {

	private final ManagedScript mSource;
	private final ManagedScript mTarget;
	/**
	 * A query k-induction is asking.
	 *
	 * @param version
	 *            the version of the published invariants it runs with
	 * @param startNanos
	 *            when it started, by {@link System#nanoTime()}
	 */
	record RunningQuery(Kind kind, int k, int version, long startNanos) {
	}

	private record Update(int version, Map<IcfgLocation, Term> invariants) {
	}

	private final BlockingQueue<Update> mQueue = new LinkedBlockingQueue<>();
	// Written by the consumer, read by the supplier.
	private volatile int mTakenVersion;
	private volatile RunningQuery mRunning;
	private final Map<Kind, Long> mPreviousMillis = new EnumMap<>(Kind.class);
	private volatile BooleanSupplier mInterrupter;
	// The answer of the supplier's probe for the query it interrupted, until k-induction takes it.
	private record ProbeAnswer(Kind kind, int k, LBool answer) {
	}

	private volatile ProbeAnswer mAnswer;
	private final boolean mMayInterrupt;
	// the invariants taken so far, as terms of mSource
	private final Map<IcfgLocation, Term> mInvariants = new HashMap<>();
	// term of mSource -> its copy in mTarget, so that an unchanged invariant is always the very same object
	private final Map<Term, Term> mTransferred = new HashMap<>();
	private TermTransferrer mTransferrer;

	/**
	 * @param mayInterrupt
	 *            whether the supplier puts queries on probation and may interrupt them
	 */
	InvariantSubscription(final ManagedScript source, final ManagedScript target, final boolean mayInterrupt) {
		mSource = source;
		mTarget = target;
		mMayInterrupt = mayInterrupt;
	}

	@Override
	public boolean mayInterrupt() {
		return mMayInterrupt;
	}

	/**
	 * Called by the supplier.
	 *
	 * @param version
	 *            the version of the published invariants after this update
	 */
	void offer(final int version, final Map<IcfgLocation, Term> invariants) {
		mQueue.add(new Update(version, invariants));
	}

	@Override
	public boolean update() {
		boolean changed = false;
		Update update;
		while ((update = mQueue.poll()) != null) {
			mInvariants.putAll(update.invariants());
			mTakenVersion = update.version();
			changed = true;
		}
		return changed;
	}

	@Override
	public void queryStarted(final Kind kind, final int k) {
		mRunning = new RunningQuery(kind, k, mTakenVersion, System.nanoTime());
	}

	@Override
	public void queryFinished(final Kind kind, final int k, final long millis) {
		mRunning = null;
		synchronized (mPreviousMillis) {
			mPreviousMillis.put(kind, millis);
		}
	}

	@Override
	public void setInterrupter(final BooleanSupplier interrupter) {
		mInterrupter = interrupter;
	}

	/**
	 * Called by the supplier.
	 *
	 * @return the query k-induction is asking, or {@code null}
	 */
	RunningQuery runningQuery() {
		return mRunning;
	}

	/**
	 * Called by the supplier.
	 *
	 * @return how long the last finished query of {@code kind} took, or 0 if there was none
	 */
	long previousMillis(final Kind kind) {
		synchronized (mPreviousMillis) {
			return mPreviousMillis.getOrDefault(kind, 0L);
		}
	}

	/**
	 * Called by the supplier: interrupts the query of k-induction, which then takes what was published and the answer
	 * of the supplier's probe.
	 *
	 * @param answer
	 *            what the probe answered for this query
	 * @return whether a query was running and got interrupted; false if k-induction cannot be interrupted
	 */
	boolean interrupt(final Kind kind, final int k, final LBool answer) {
		final BooleanSupplier interrupter = mInterrupter;
		if (interrupter == null) {
			return false;
		}
		mAnswer = new ProbeAnswer(kind, k, answer);
		final boolean interrupted = interrupter.getAsBoolean();
		if (!interrupted) {
			mAnswer = null;
		}
		return interrupted;
	}

	@Override
	public Optional<LBool> takeAnswer(final Kind kind, final int k) {
		final ProbeAnswer answer = mAnswer;
		mAnswer = null;
		if (answer == null || answer.kind() != kind || answer.k() != k) {
			return Optional.empty();
		}
		return Optional.of(answer.answer());
	}

	@Override
	public Optional<Term> getInvariant(final CallNode<IPredicate> loopHead, final ManagedScript targetScript) {
		if (targetScript != mTarget) {
			throw new IllegalArgumentException(
					"this subscription delivers terms of " + mTarget + ", but they were asked for " + targetScript);
		}
		// A location invariant holds in every calling context, hence for every call node of the location.
		final Term invariant = mInvariants.get(InvariantSupplier.locationOf(loopHead.getState()));
		if (invariant == null) {
			return Optional.empty();
		}
		return Optional.of(mTransferred.computeIfAbsent(invariant, this::transfer));
	}

	private Term transfer(final Term invariant) {
		if (mTransferrer == null) {
			mTransferrer = new TermTransferrer(mSource.getScript(), mTarget.getScript());
		}
		return mTransferrer.transform(invariant);
	}
}
