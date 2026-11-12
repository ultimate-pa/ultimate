/*
 * Copyright (C) 2026 University of Freiburg
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.WitnessInvariant;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovabilityReason;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.IInvariantSupplier;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.KInduction;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.KInduction.WitnessInvariants;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.CallNode;
import de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding.PcTransitionSystemFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.proofs.floydhoare.NwaHoareProofProducer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.NwaCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.TransferBetweenMainAndWorker.TransferMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.WorkerThreadResult.WorkerType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.invariants.InvariantMessage;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.invariants.InvariantMessage.InterpolantSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.invariants.InvariantSupplier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.kinduction.KInductionWorkerThread;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * A CEGAR loop that runs three analyses one after the other, all on the main thread:
 * <ol>
 * <li><b>Trace abstraction</b>, the loop of {@link NwaCegarLoop}, for at most
 * {@link TAPreferences#getSequentialTaTimeLimit()} seconds. If it proves or refutes the program, that is the result,
 * with the proof or counterexample of trace abstraction for the witness.</li>
 * <li><b>Invariant synthesis</b>: the {@link InvariantSupplier} checks the interpolants trace abstraction produced for
 * inductive invariants, for at most {@link TAPreferences#getSequentialInvariantTimeLimit()} seconds, on a thread of
 * its own that the main thread waits for.</li>
 * <li><b>k-induction</b> on the abstraction trace abstraction refined so far, with the invariants of the synthesis,
 * without a time limit of its own unless {@link TAPreferences#getSequentialKInductionTimeLimit()} sets one. A
 * violation is reported by the waypoints of its model, see {@link KInductionWorkerThread#reportWaypoints}; a proof
 * gives the correctness witness, see {@link #useKInductionProof}.</li>
 * </ol>
 * Unlike {@link ParallelNwaCegarLoop}, nothing runs alongside trace abstraction, so the abstraction is copied only once,
 * into the script of k-induction, when trace abstraction is done with it. k-induction and the invariant synthesis each
 * get a solver of their own, as in the parallel loop (see
 * {@link ParallelNwaCegarLoop#getSolverSettings(IUltimateServiceProvider, TAPreferences, WorkerType, java.util.function.Supplier, String)}):
 * the main script's solver usually neither produces models nor runs without a per-query timeout.
 *
 * @param <L>
 *            the type of the letters
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public class NwaCegarLoopWithKInduction<L extends IIcfgTransition<?>> extends NwaCegarLoop<L> {

	/** How much longer than its time limit the main thread waits for the invariant synthesis to notice it. */
	private static final long INVARIANT_GRACE_MILLIS = 2_000;

	// The ICFG as it was before k-induction's copy of the abstraction attached copies of its edges, see finish()
	private final Set<IcfgLocation> mOriginalLocations;
	private final Set<IcfgEdge> mOriginalEdges;

	// The interpolants of trace abstraction, for the invariant synthesis
	private final List<InvariantMessage> mInterpolants = new ArrayList<>();
	// Set by trace abstraction: whether its last emptiness check found the abstraction empty
	private boolean mTaProvedProgram;
	// The error locations trace abstraction found a feasible counterexample for
	private final Set<IcfgLocation> mTaRefutedLocations = new HashSet<>();
	// Whether one of those counterexamples has an overapproximated letter, which makes the result UNKNOWN
	private boolean mTaViolationOverapproximated;
	// Whether trace abstraction is computing a difference, see computeAutomataDifference
	private boolean mInDifference;
	// Whether the Hoare annotation fragments of mProofUpdater may not fit mAbstraction any more, see
	// computeAutomataDifference
	private boolean mProofOutOfSync;
	private final AtomicBoolean mLoggedZ3InsteadOfBitwuzla = new AtomicBoolean();

	public NwaCegarLoopWithKInduction(final DebugIdentifier name,
			final INestedWordAutomaton<L, IPredicate> initialAbstraction, final IIcfg<?> rootNode,
			final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory, final TAPreferences taPrefs,
			final Set<? extends IcfgLocation> errorLocs, final NwaHoareProofProducer<L> proofProducer,
			final IUltimateServiceProvider services, final Class<L> transitionClazz,
			final PredicateFactoryRefinement stateFactoryForRefinement) {
		super(name, initialAbstraction, rootNode, csToolkit, predicateFactory, taPrefs, errorLocs, proofProducer,
				services, transitionClazz, stateFactoryForRefinement);
		mOriginalLocations = ParallelNwaCegarLoop.collectLocations(rootNode);
		mOriginalEdges = ParallelNwaCegarLoop.outgoingEdges(mOriginalLocations);
	}

	@Override
	protected void iterate() throws AutomataLibraryException {
		if (runTraceAbstraction()) {
			return;
		}
		runKInduction();
	}

	// ------------------------------------------------------------------------------------------------------------
	// Trace abstraction
	// ------------------------------------------------------------------------------------------------------------

	/**
	 * Runs the loop of {@link NwaCegarLoop} until it decides the program or its time limit is up.
	 *
	 * @return whether trace abstraction decided the program, so that its result stands
	 */
	private boolean runTraceAbstraction() throws AutomataLibraryException {
		final long limit = TimeUnit.SECONDS.toMillis(mPref.getSequentialTaTimeLimit());
		if (limit == 0) {
			mLogger.info("NwaCegarLoopWithKInduction: phase TA skipped, its time limit is 0");
			return false;
		}
		mLogger.info("NwaCegarLoopWithKInduction: phase TA starts, time limit %d s", mPref.getSequentialTaTimeLimit());
		final IUltimateServiceProvider services = mServices;
		mServices = withTimeLimit(services, limit);
		try {
			super.iterate();
		} catch (final AutomataOperationCanceledException | ToolchainCanceledException e) {
			if (!services.getProgressMonitorService().continueProcessing()) {
				throw e;
			}
			mLogger.info("NwaCegarLoopWithKInduction: phase TA ends at its time limit after %d iteration(s)",
					getIteration());
			if (mInDifference && mProofUpdater != null) {
				mProofOutOfSync = true;
				mLogger.warn("NwaCegarLoopWithKInduction: the time limit stopped a difference, so the Hoare annotation "
						+ "fragments may not fit the abstraction; a proof of k-induction gets a witness without "
						+ "invariants");
			}
			return mTaViolationOverapproximated;
		} finally {
			mServices = services;
		}
		if (mTaProvedProgram) {
			mLogger.info("NwaCegarLoopWithKInduction: phase TA proved the program after %d iteration(s)",
					getIteration());
			return true;
		}
		if (mTaViolationOverapproximated) {
			// The result is UNKNOWN, and Ultimate.py retries with the bit-precise settings, which are precise where
			// these overapproximate. That run should start now, not after k-induction, whose violations of this program
			// are no verdict either.
			mLogger.info("NwaCegarLoopWithKInduction: phase TA found a violation with an overapproximation after %d "
					+ "iteration(s), the loop ends without k-induction", getIteration());
			return true;
		}
		if (!mTaRefutedLocations.isEmpty() && mPref.stopAfterFirstViolation()) {
			mLogger.info("NwaCegarLoopWithKInduction: phase TA refuted the program after %d iteration(s)",
					getIteration());
			return true;
		}
		mLogger.info("NwaCegarLoopWithKInduction: phase TA ends without a verdict after %d iteration(s)",
				getIteration());
		return false;
	}

	@Override
	protected Pair<LBool, IProgramExecution<L, Term>> isCounterexampleFeasible()
			throws AutomataOperationCanceledException {
		final Pair<LBool, IProgramExecution<L, Term>> result = super.isCounterexampleFeasible();
		if (result.getFirst() == LBool.SAT) {
			mTaRefutedLocations.add(getErrorLocFromCounterexample());
			if (result.getSecond() != null
					&& !UnprovabilityReason.getUnprovabilityReasons(result.getSecond()).isEmpty()) {
				mTaViolationOverapproximated = true;
			}
		} else if (result.getFirst() == LBool.UNSAT && mPref.submitInterpolantInvariants()) {
			collectInterpolants();
		}
		return result;
	}

	/**
	 * Marks the difference while it runs. It updates the Hoare annotation fragments to its states before it removes the
	 * dead ends, and replaces {@link #mAbstraction} by its result only after that. If the time limit of trace abstraction
	 * stops it in between, the abstraction is still the previous one and fine for k-induction, but the fragments
	 * describe states it does not have, and a proof extracted from them could miss the states of the abstraction.
	 */
	@Override
	protected void computeAutomataDifference(final INestedWordAutomaton<L, IPredicate> minuend,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahend,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahendBeforeEnhancement,
			final IPredicateUnifier predicateUnifier, final boolean explointSigmaStarConcatOfIA,
			final IHoareTripleChecker htc, final InterpolantAutomatonEnhancement enhanceMode,
			final boolean useErrorAutomaton, final AutomatonType automatonType)
			throws AutomataLibraryException, AssertionError {
		mInDifference = true;
		super.computeAutomataDifference(minuend, subtrahend, subtrahendBeforeEnhancement, predicateUnifier,
				explointSigmaStarConcatOfIA, htc, enhanceMode, useErrorAutomaton, automatonType);
		mInDifference = false;
	}

	@Override
	protected boolean isAbstractionEmpty() throws AutomataOperationCanceledException {
		mTaProvedProgram = super.isAbstractionEmpty();
		return mTaProvedProgram;
	}

	/**
	 * Keeps every interpolant sequence of the infeasibility proof of the current counterexample for the invariant
	 * synthesis, as {@code CegarNwaWorkerThread} hands them to the supplier in the parallel loop.
	 */
	private void collectInterpolants() {
		final List<QualifiedTracePredicates> sequences = mRefinementResult.getUsedTracePredicates();
		if (sequences == null) {
			return;
		}
		final List<IcfgLocation> locations = mCounterexample.getStateSequence().stream()
				.map(state -> ((ISLPredicate) state).getProgramPoint()).collect(Collectors.toList());
		// The interpolants are those between two letters, i.e. at the states 1..n-1 of the run.
		final List<IcfgLocation> inner = locations.subList(1, locations.size() - 1);
		for (final QualifiedTracePredicates sequence : sequences) {
			final List<Term> interpolants =
					sequence.getPredicates().stream().map(IPredicate::getFormula).collect(Collectors.toList());
			mInterpolants.add(new InterpolantSequence(mCsToolkit.getManagedScript(), new ArrayList<>(inner),
					interpolants, "TA " + sequence.getOrigin().getSimpleName()));
		}
	}

	// ------------------------------------------------------------------------------------------------------------
	// k-induction, with the invariant synthesis before it
	// ------------------------------------------------------------------------------------------------------------

	private void runKInduction() throws AutomataLibraryException {
		// The solvers of k-induction and of the invariant synthesis are destroyed with these services.
		final TaskScopedServices kiServices = new TaskScopedServices(mServices);
		final TaskScopedServices invServices = new TaskScopedServices(mServices);
		try {
			final TransferBetweenMainAndWorker<L, IPredicate> kiTransfer = new TransferBetweenMainAndWorker<>(
					new AutomataLibraryServices(mServices), mLogger, mCsToolkit.getManagedScript(), kiServices,
					solverSettings(WorkerType.KINDUCTION, "KInduction"), mCsToolkit, "ki_");
			final CfgSmtToolkit kiToolkit = kiTransfer.getWorkerCfgSmtToolKit();
			final ManagedScript kiScript = kiToolkit.getManagedScript();
			final PredicateFactory kiPredicateFactory =
					new PredicateFactory(mServices, kiScript, kiToolkit.getSymbolTable());
			// The only copy of the abstraction. It has the same states, so it is a copy of the letters only. From here on
			// it is the only abstraction there is, see releaseTraceAbstraction.
			@SuppressWarnings("unchecked")
			final INestedWordAutomaton<L, IPredicate> kiAbstraction =
					(INestedWordAutomaton<L, IPredicate>) kiTransfer.transferAutomaton(mAbstraction,
							new PredicateFactoryForInterpolantAutomata(kiScript, kiPredicateFactory, false),
							TransferMode.MAIN2WORKER);
			mLogger.info("NwaCegarLoopWithKInduction: k-induction runs on the abstraction of trace abstraction, %s",
					kiAbstraction.sizeInformation());
			releaseTraceAbstraction();
			final PcTransitionSystemFactory.Result<IPredicate> system =
					KInduction.buildTransitionSystem(mServices, mLogger, kiToolkit, kiAbstraction);

			final IInvariantSupplier<CallNode<IPredicate>> invariants =
					synthesizeInvariants(invServices, kiScript, kiAbstraction, system);

			final long limit = TimeUnit.SECONDS.toMillis(mPref.getSequentialKInductionTimeLimit());
			final IUltimateServiceProvider services = limit == 0 ? kiServices : withTimeLimit(kiServices, limit);
			mLogger.info("NwaCegarLoopWithKInduction: phase KI starts, %s",
					limit == 0 ? "no time limit of its own" : "time limit " + limit / 1000 + " s");
			runKInduction(services, kiToolkit, kiAbstraction, system, invariants);
		} finally {
			invServices.destroyAll(mLogger);
			kiServices.destroyAll(mLogger);
		}
	}

	/**
	 * Drops what trace abstraction leaves behind and k-induction does not need, as
	 * {@link ParallelNwaCegarLoop}'s {@code releaseForKInduction} does when the heap fills up, but always: the main
	 * thread's abstraction, of which k-induction has its copy, and the last counterexample. The empty abstraction keeps
	 * the alphabet, which the solver settings look at.
	 */
	private void releaseTraceAbstraction() {
		final int size = mAbstraction.size();
		mAbstraction = new NestedWordAutomaton<>(new AutomataLibraryServices(getServices()),
				mAbstraction.getVpAlphabet(), mStateFactoryForRefinement);
		mCounterexample = null;
		mArtifactAutomaton = null;
		mLogger.info("NwaCegarLoopWithKInduction: released the abstraction of trace abstraction (%d states), "
				+ "k-induction keeps its copy", size);
	}

	/**
	 * Runs the invariant synthesis on the interpolants of trace abstraction. Its solver is stopped when it is done; the
	 * subscription of k-induction keeps what it published.
	 *
	 * @return the invariants it found, for k-induction on {@code kiScript}
	 */
	private IInvariantSupplier<CallNode<IPredicate>> synthesizeInvariants(final TaskScopedServices invServices,
			final ManagedScript kiScript, final INestedWordAutomaton<L, IPredicate> kiAbstraction,
			final PcTransitionSystemFactory.Result<IPredicate> system) {
		final long limit = TimeUnit.SECONDS.toMillis(mPref.getSequentialInvariantTimeLimit());
		if (limit == 0 || mInterpolants.isEmpty()) {
			mLogger.info("NwaCegarLoopWithKInduction: phase INV skipped, %s",
					limit == 0 ? "its time limit is 0" : "trace abstraction produced no interpolants");
			return IInvariantSupplier.none();
		}
		mLogger.info("NwaCegarLoopWithKInduction: phase INV starts with %d interpolant sequence(s), time limit %d s",
				mInterpolants.size(), mPref.getSequentialInvariantTimeLimit());
		final TransferBetweenMainAndWorker<L, IPredicate> invTransfer = new TransferBetweenMainAndWorker<>(
				new AutomataLibraryServices(mServices), mLogger, mCsToolkit.getManagedScript(), invServices,
				solverSettings(WorkerType.INVARIANT, "InvariantSupplier"), mCsToolkit, "inv_");
		final AtomicBoolean phaseOver = new AtomicBoolean();
		final InvariantSupplier<L, INestedWordAutomaton<L, IPredicate>> supplier = new InvariantSupplier<>(mLogger,
				withTimeLimit(invServices, limit), invTransfer.getWorkerCfgSmtToolKit(), new LinkedBlockingQueue<>(),
				phaseOver::get, null);
		// Only looks at the transition formulas, which k-induction's copy has as well.
		supplier.setAbstraction(kiAbstraction);
		final IInvariantSupplier<CallNode<IPredicate>> subscription = supplier.subscribe(kiScript);
		subscription.systemBuilt(system.system(), kiScript);
		mInterpolants.forEach(supplier.sink()::submit);
		mInterpolants.clear();

		final ExecutorService executor = Executors.newSingleThreadExecutor(runnable -> {
			final Thread thread = new Thread(runnable, "Invariant Supplier");
			thread.setDaemon(true);
			return thread;
		});
		final Future<?> done = executor.submit(supplier::processPending);
		try {
			done.get(limit + INVARIANT_GRACE_MILLIS, TimeUnit.MILLISECONDS);
			mLogger.info("NwaCegarLoopWithKInduction: phase INV ends");
		} catch (final TimeoutException e) {
			// A query that does not notice the time limit: destroying its solver below ends it.
			mLogger.warn("NwaCegarLoopWithKInduction: phase INV did not end within its time limit, stopping its solver");
		} catch (final ExecutionException e) {
			// It only feeds k-induction, which can do without.
			mLogger.warn("NwaCegarLoopWithKInduction: phase INV crashed, k-induction goes on with what it published: "
					+ e.getCause());
		} catch (final InterruptedException e) {
			Thread.currentThread().interrupt();
			throw new ToolchainCanceledException(getClass(), "waiting for the invariant synthesis");
		} finally {
			phaseOver.set(true);
			executor.shutdownNow();
			// Its subscription transfers the published invariants with the symbol table of the supplier's script,
			// which outlives the solver.
			invServices.destroyAll(mLogger);
		}
		return subscription;
	}

	private void runKInduction(final IUltimateServiceProvider services, final CfgSmtToolkit kiToolkit,
			final INestedWordAutomaton<L, IPredicate> kiAbstraction,
			final PcTransitionSystemFactory.Result<IPredicate> system,
			final IInvariantSupplier<CallNode<IPredicate>> invariants) throws AutomataLibraryException {
		final HashRelation<String, ILocation> overapproximations =
				KInductionWorkerThread.overapproximations(kiAbstraction);
		final KInduction<L, IPredicate> kInduction;
		try {
			kInduction = new KInduction<>(services, mLogger, kiToolkit, kiAbstraction, system, invariants,
					mPref.restartKInductionSolverAfterInterrupt());
		} catch (final ToolchainCanceledException e) {
			if (!mServices.getProgressMonitorService().continueProcessing()) {
				throw e;
			}
			mLogger.info("NwaCegarLoopWithKInduction: phase KI ends at its time limit");
			addResultForUndecided(Result.USER_LIMIT_TIME, e, null);
			return;
		} catch (final InterruptedException e) {
			Thread.currentThread().interrupt();
			throw new ToolchainCanceledException(getClass(), "k-induction");
		} catch (final RuntimeException e) {
			if (!KInductionWorkerThread.isLimit(e)) {
				throw e;
			}
			mLogger.warn("NwaCegarLoopWithKInduction: phase KI stopped by %s, no verdict", e);
			addResultForUndecided(Result.UNKNOWN, null, null);
			return;
		}
		if (kInduction.wasUnkown()) {
			mLogger.warn("NwaCegarLoopWithKInduction: phase KI ends without a verdict: " + kInduction.getInconclusive());
			addResultForUndecided(Result.UNKNOWN, null, null);
			return;
		}
		if (kInduction.isSafe()) {
			mLogger.info("NwaCegarLoopWithKInduction: phase KI proved the program at k=%d", kInduction.getProvedK());
			useKInductionProof(kInduction, services, kiToolkit, kiAbstraction);
			addResultForUndecided(Result.SAFE, null, null);
			return;
		}
		if (!overapproximations.isEmpty()) {
			// The waypoints miss the Overapprox annotations by which a counterexample would be reported as UNKNOWN,
			// see KInductionWorkerThread.hasOverapproximation. So the overapproximation is the reason of the UNKNOWN
			// here, reported as for such a counterexample of trace abstraction: Ultimate.py then retries with the
			// bit-precise settings, which are precise where these overapproximate.
			final Entry<String, ILocation> first = overapproximations.iterator().next();
			final UnprovabilityReason reason =
					new UnprovabilityReason("overapproximation of " + first.getKey(), first.getValue());
			mLogger.warn("NwaCegarLoopWithKInduction: phase KI found a violation, but the program has %d "
					+ "overapproximation(s), so it may be spurious; UNKNOWN because of the %s",
					overapproximations.size(), reason);
			addResultForUndecided(Result.UNKNOWN, null, reason);
			return;
		}
		mLogger.info("NwaCegarLoopWithKInduction: phase KI refuted the program");
		KInductionWorkerThread.reportWaypoints(kInduction.getWaypoints(), mResultBuilder, services,
				kiToolkit.getManagedScript(), mPref.stopAfterFirstViolation(), mLogger);
		mResultBuilder.addResultForAllRemaining(Result.UNKNOWN);
	}

	/**
	 * Registers {@code result} for every error location that trace abstraction did not refute. A location whose
	 * iteration trace abstraction ended at its time limit has TIMEOUT already, which a verdict overrides.
	 *
	 * @param limit
	 *            the limit that was reached, only for a limit result
	 * @param reasonUnknown
	 *            why the result is UNKNOWN, only for that result
	 */
	private void addResultForUndecided(final Result result, final ToolchainCanceledException limit,
			final UnprovabilityReason reasonUnknown) {
		for (final IcfgLocation errorLoc : mErrorLocs) {
			if (!mTaRefutedLocations.contains(errorLoc)) {
				mResultBuilder.addResult(errorLoc, result, null, result.isLimit() ? limit : null, reasonUnknown);
			}
		}
	}

	// ------------------------------------------------------------------------------------------------------------
	// The correctness witness of a k-induction proof
	// ------------------------------------------------------------------------------------------------------------

	/**
	 * Makes the invariants of a k-induction proof part of the proof of this loop.
	 * <p>
	 * k-induction ran on the abstraction that trace abstraction refined, whose states are products of a program
	 * location with interpolants, and it found its invariants per such state. The invariant of a location must hold for
	 * every execution that reaches it, also for those that end in a state trace abstraction already removed from the
	 * abstraction as a dead end. The Hoare annotation of trace abstraction ({@link NwaHoareProofProducer}) covers those:
	 * it is the disjunction of the formulas of all states of a location, removed or not, and the formula of a state holds
	 * after every execution that ends in it. So each state of the abstraction is replaced by one whose formula is the
	 * conjunction of its own formula and the invariant k-induction found for it, and the Hoare annotation of the proof
	 * is extracted from that abstraction as if trace abstraction had proven the program. The abstraction is k-induction's
	 * copy, the only one left (see {@link #releaseTraceAbstraction()}); its letters belong to k-induction's script, but
	 * the extraction only follows its transitions and never looks at a letter's formula.
	 * <p>
	 * Invariants k-induction could not compute in time, or the parts of them that cannot be backtranslated, are left out,
	 * which only weakens the annotation. If the fragments may not fit the abstraction (see
	 * {@link #computeAutomataDifference}), the proof has no invariants at all, i.e. the correctness witness is trivial.
	 */
	private void useKInductionProof(final KInduction<L, IPredicate> kInduction,
			final IUltimateServiceProvider services, final CfgSmtToolkit kiToolkit,
			final INestedWordAutomaton<L, IPredicate> kiAbstraction) throws AutomataLibraryException {
		if (mProofUpdater == null) {
			return;
		}
		if (mProofOutOfSync) {
			mLogger.warn("NwaCegarLoopWithKInduction: the proof of k-induction has no invariants, the Hoare annotation "
					+ "fragments may not fit the abstraction");
			mProofUpdater.setProof(Collections.emptyMap());
			return;
		}
		WitnessInvariants<IPredicate> witness;
		try {
			witness = KInductionWorkerThread.computeWitnessInvariants(kInduction, services, mPref, kiToolkit,
					() -> false, mLogger);
		} catch (final InterruptedException e) {
			Thread.currentThread().interrupt();
			throw new ToolchainCanceledException(getClass(), "computing the invariants of the k-induction proof");
		}
		final Map<IPredicate, Term> invariants = witness == null ? Map.of() : witness.invariants();
		final WorkerStateTransferrer<L> transferrer = new WorkerStateTransferrer<>(
				new AutomataLibraryServices(mServices), mCsToolkit.getManagedScript(), mPredicateFactory);
		final Set<IcfgLocation> loopLocations = new HashSet<>(mIcfg.getLoopLocations());
		if (!kiAbstraction.getStates().stream().allMatch(ISLPredicate.class::isInstance)) {
			mLogger.warn("NwaCegarLoopWithKInduction: a state of the abstraction has no single location, the proof does "
					+ "without the invariants of k-induction");
			return;
		}
		// A new state for each one, also those that stay as they are: the Hoare annotation fragments forget the
		// location of a state that a minimization maps to itself. A "don't care" state becomes one whose formula is
		// true, which means the same; the extraction of the Hoare annotation from a nonempty abstraction expects that.
		final Map<IPredicate, IPredicate> old2New = new HashMap<>();
		final Term trueTerm = mCsToolkit.getManagedScript().getScript().term("true");
		// Per loop location, whether all of its states have the invariant true, see below
		final Map<IcfgLocation, Boolean> onlyTrue = new LinkedHashMap<>();
		int strengthened = 0;
		for (final IPredicate state : kiAbstraction.getStates()) {
			final IcfgLocation loc = ((ISLPredicate) state).getProgramPoint();
			final boolean dontCare = mPredicateFactory.isDontCare(state);
			final Term invariant = loopLocations.contains(loc) ? invariants.get(state) : null;
			if (loopLocations.contains(loc)) {
				onlyTrue.merge(loc, invariant != null && SmtUtils.isTrueLiteral(invariant)
						&& (dontCare || SmtUtils.isTrueLiteral(state.getFormula())), Boolean::logicalAnd);
			}
			Term translatable = null;
			if (invariant != null && !SmtUtils.isTrueLiteral(invariant)) {
				translatable = ParallelNwaCegarLoop.weakenToBacktranslatable(
						transferrer.transferTerm(invariant, kiToolkit.getManagedScript()), loc,
						mCsToolkit.getManagedScript().getScript(), mServices.getBacktranslationService(), mLogger);
			}
			if (translatable == null || SmtUtils.isTrueLiteral(translatable)) {
				old2New.put(state, mPredicateFactory.newSPredicate(loc, dontCare ? trueTerm : state.getFormula()));
				continue;
			}
			final IPredicate kInductionInvariant = mPredicateFactory.newPredicate(translatable);
			final IPredicate conjunction =
					dontCare ? kInductionInvariant : mPredicateFactory.and(state, kInductionInvariant);
			old2New.put(state, mPredicateFactory.newSPredicate(loc, conjunction.getFormula()));
			strengthened++;
		}
		// FloydHoareUtils.createInvariantResults leaves out every invariant that is true, so a proof with true at a loop
		// head gives an empty witness there, which validators such as LIV cannot use, see
		// ParallelNwaCegarLoop.kInductionAnnotation. If the invariants prove the program and the annotation of a loop
		// head may well be true, the witness states it explicitly. An annotation that is not true replaces it.
		if (witness != null && witness.proving()) {
			onlyTrue.forEach((loc, isTrue) -> {
				if (isTrue) {
					new WitnessInvariant<>("1").annotate(loc);
				}
			});
		}
		mLogger.info("NwaCegarLoopWithKInduction: the proof conjoins invariants of k-induction to %d of %d state(s)",
				strengthened, kiAbstraction.size());
		final NestedWordAutomaton<L, IPredicate> renamed = rename(kiAbstraction, old2New);
		mProofUpdater.updateOnMinimization(old2New, renamed);
		mAbstraction = renamed;
	}

	/**
	 * @return a copy of {@code automaton} with every state replaced by its image under {@code old2New}
	 */
	private NestedWordAutomaton<L, IPredicate> rename(final INestedWordAutomaton<L, IPredicate> automaton,
			final Map<IPredicate, IPredicate> old2New) {
		final NestedWordAutomaton<L, IPredicate> result = new NestedWordAutomaton<>(
				new AutomataLibraryServices(getServices()), automaton.getVpAlphabet(), mStateFactoryForRefinement);
		for (final IPredicate state : automaton.getStates()) {
			result.addState(automaton.isInitial(state), automaton.isFinal(state), old2New.get(state));
		}
		for (final IPredicate state : automaton.getStates()) {
			final IPredicate source = old2New.get(state);
			for (final OutgoingInternalTransition<L, IPredicate> trans : automaton.internalSuccessors(state)) {
				result.addInternalTransition(source, trans.getLetter(), old2New.get(trans.getSucc()));
			}
			for (final OutgoingCallTransition<L, IPredicate> trans : automaton.callSuccessors(state)) {
				result.addCallTransition(source, trans.getLetter(), old2New.get(trans.getSucc()));
			}
			for (final OutgoingReturnTransition<L, IPredicate> trans : automaton.returnSuccessors(state)) {
				result.addReturnTransition(source, old2New.get(trans.getHierPred()), trans.getLetter(),
						old2New.get(trans.getSucc()));
			}
		}
		return result;
	}

	// ------------------------------------------------------------------------------------------------------------
	// Helpers
	// ------------------------------------------------------------------------------------------------------------

	private static IUltimateServiceProvider withTimeLimit(final IUltimateServiceProvider services,
			final long millis) {
		final IProgressMonitorService progressMonitor = services.getProgressMonitorService();
		return progressMonitor.registerChildTimer(services, progressMonitor.getChildTimer(millis));
	}

	private SolverSettings solverSettings(final WorkerType workerType, final String filename) {
		return ParallelNwaCegarLoop.getSolverSettings(mServices, mPref, workerType,
				() -> ParallelNwaCegarLoop.externalSolverCommand(mPref, mLogger, workerType,
						() -> ParallelNwaCegarLoop.bitwuzlaRejectsProgram(mAbstraction.getVpAlphabet()),
						mLoggedZ3InsteadOfBitwuzla),
				filename);
	}

	@Override
	protected void finish() {
		// k-induction's copy of the abstraction attached a copy of every edge to the locations of the ICFG.
		ParallelNwaCegarLoop.detachTransferredEdges(mOriginalLocations, mOriginalEdges, mLogger);
		super.finish();
	}
}
