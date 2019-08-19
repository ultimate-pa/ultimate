/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.io.File;
import java.util.Collection;
import java.util.EnumSet;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter.Format;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaBasis;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.IRunningTaskStackProvider;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.TaskCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.TaskCanceledException.UserDefinedLimit;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainExceptionWrapper;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovabilityReason;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.SubtaskFileIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interactive.InteractiveCegar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.InductivityCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.Artifact;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.HoareAnnotationPositions;

/**
 * CEGAR loop of a trace abstraction. Can be used to check safety and termination of sequential and concurrent programs.
 * Defines roughly the structure of the CEGAR loop, concrete algorithms are implemented in classes which extend this
 * one.
 *
 * @author heizmann@informatik.uni-freiburg.de
 */
public abstract class AbstractCegarLoop<LETTER extends IAction> {
	private static final String MSG_VERIFICATION_CANCELED = "Verification canceled";

	private static final boolean CONTINUE_AFTER_ERROR_TRACE_FOUND = false;

	/**
	 * Result of CEGAR loop iteration
	 */
	public enum Result {
		/**
		 * there is no feasible trace to an error location
		 */
		SAFE,
		/**
		 * there is a feasible trace to an error location (the underlying program has at least one execution which
		 * violates its specification)
		 */
		UNSAFE,
		/**
		 * The core timeout was hit or a user canceled the verification
		 */
		TIMEOUT,
		/**
		 * we found a trace for which we could not decide feasibility or we found an infeasible trace but were not able
		 * to exclude it in abstraction refinement.
		 */
		UNKNOWN,
		/**
		 * The user-specified timeout for the analysis was hit
		 */
		USER_LIMIT_TIME,
		/**
		 * The user-specified limit for the max-size of the trace histogram was hit
		 */
		USER_LIMIT_TRACEHISTOGRAM,
		/**
		 * The user-specified limit for the amount of CEGAR iterations was hit
		 */
		USER_LIMIT_ITERATIONS,
		/**
		 * The user-specified limit for the amount of analysis attempts per path program was hit
		 */
		USER_LIMIT_PATH_PROGRAM;

		public static final EnumSet<Result> USER_LIMIT_RESULTS =
				EnumSet.of(USER_LIMIT_ITERATIONS, USER_LIMIT_PATH_PROGRAM, USER_LIMIT_TIME, USER_LIMIT_TRACEHISTOGRAM);

		public static final Result convert(final TaskCanceledException.UserDefinedLimit limit) {
			switch (limit) {
			case ITERATIONS:
				return Result.USER_LIMIT_ITERATIONS;
			case PATH_PROGRAM_ATTEMPTS:
				return Result.USER_LIMIT_PATH_PROGRAM;
			case TIME_PER_ERROR_LOCATION:
				return USER_LIMIT_TIME;
			case TRACE_HISTOGRAM:
				return Result.USER_LIMIT_TRACEHISTOGRAM;
			default:
				throw new UnsupportedOperationException("Unknown UserDefinedLimit " + limit);
			}
		}
	}

	protected final ILogger mLogger;
	protected final SimplificationTechnique mSimplificationTechnique;
	protected final XnfConversionTechnique mXnfConversionTechnique;

	/**
	 * Unique mName of this CEGAR loop to distinguish this instance from other instances in a complex verification task.
	 * Important only for debugging and debugging output written to files.
	 */
	private final DebugIdentifier mName;

	/**
	 * Interprocedural control flow graph.
	 */
	protected final IIcfg<?> mIcfg;

	/**
	 * Intermediate layer to encapsulate communication with SMT solvers.
	 */
	protected final CfgSmtToolkit mCsToolkit;
	protected final PredicateFactory mPredicateFactory;

	/**
	 * Intermediate layer to encapsulate preferences.
	 */
	protected final TAPreferences mPref;

	/**
	 * Set of error location whose reachability is analyzed by this CEGAR loop.
	 */
	protected final Collection<? extends IcfgLocation> mErrorLocs;

	/**
	 * Current Iteration of this CEGAR loop.
	 */
	protected int mIteration;

	/**
	 * Accepting run of the abstraction obtained in this iteration.
	 */
	protected IRun<LETTER, IPredicate, ?> mCounterexample;

	/**
	 * Abstraction of this iteration. The language of mAbstraction is a set of traces which is
	 * <ul>
	 * <li>a superset of the feasible program traces.
	 * <li>a subset of the traces which respect the control flow of the program.
	 */
	protected IAutomaton<LETTER, IPredicate> mAbstraction;

	/**
	 * IInterpolantGenerator that was used in the current iteration.
	 */
	protected IInterpolantGenerator<LETTER> mInterpolantGenerator;

	/**
	 * Interpolant automaton of this iteration.
	 */
	protected NestedWordAutomaton<LETTER, IPredicate> mInterpolAutomaton;

	/**
	 * Program execution that leads to error. Only computed in the last iteration of the CEGAR loop if the program is
	 * incorrect.
	 */
	protected IProgramExecution<IIcfgTransition<IcfgLocation>, Term> mRcfgProgramExecution;

	// used for debugging only
	protected IAutomaton<LETTER, IPredicate> mArtifactAutomaton;

	protected final Format mPrintAutomataLabeling;

	protected CegarLoopStatisticsGenerator mCegarLoopBenchmark;

	protected final IUltimateServiceProvider mServices;
	private IRunningTaskStackProvider mRunningTaskStackProvider;
	protected final TaskIdentifier mTaskIdentifier;

	protected Dumper mDumper;
	/**
	 * only != null if analysis result is UNKNOWN Textual explanation why result is unknown.
	 */
	private UnprovabilityReason mReasonUnknown;
	protected final InteractiveCegar mInteractive;

	private static final boolean DUMP_BIGGEST_AUTOMATON = false;

	public AbstractCegarLoop(final IUltimateServiceProvider services, final DebugIdentifier name,
			final IIcfg<?> rootNode, final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory,
			final TAPreferences taPrefs, final Collection<? extends IcfgLocation> errorLocs, final ILogger logger) {
		mServices = services;
		mLogger = logger;
		mSimplificationTechnique = taPrefs.getSimplificationTechnique();
		mXnfConversionTechnique = taPrefs.getXnfConversionTechnique();
		mPrintAutomataLabeling = taPrefs.getAutomataFormat();
		mName = name;
		mIcfg = rootNode;
		mCsToolkit = csToolkit;
		mPredicateFactory = predicateFactory;
		mPref = taPrefs;
		mErrorLocs = errorLocs;
		// TODO: TaskIdentifier should probably be provided by caller
		mTaskIdentifier = new SubtaskFileIdentifier(null, mIcfg.getIdentifier() + "_" + name);
		mInteractive = new InteractiveCegar(services, logger);
		mLogger.info("Starting to check reachability of " + errorLocs.size() + " error locations.");
	}

	public IRunningTaskStackProvider getRunningTaskStackProvider() {
		return mRunningTaskStackProvider;
	}

	/**
	 * Construct the automaton mAbstraction such that the language recognized by mAbstation is a superset of the
	 * language of the program. The initial abstraction in our implementations will usually be an automaton that has the
	 * same graph as the program.
	 *
	 * @throws AutomataLibraryException
	 */
	protected abstract void getInitialAbstraction() throws AutomataLibraryException;

	/**
	 * Return true iff the mAbstraction does not accept any trace.
	 *
	 * @throws AutomataOperationCanceledException
	 */
	protected abstract boolean isAbstractionEmpty() throws AutomataOperationCanceledException;

	/**
	 * Determine if the trace of mCounterexample is a feasible sequence of CodeBlocks. Return
	 * <ul>
	 * <li>SAT if the trace is feasible
	 * <li>UNSAT if the trace is infeasible
	 * <li>UNKNOWN if the algorithm was not able to determine the feasibility.
	 * </ul>
	 *
	 * @throws AutomataOperationCanceledException
	 *
	 *             TODO Christian 2016-11-11: Merge the methods isCounterexampleFeasible() and
	 *             constructInterpolantAutomaton() after {@link TreeAutomizerCEGAR} does not depend on this class
	 *             anymore.
	 */
	protected abstract LBool isCounterexampleFeasible() throws AutomataOperationCanceledException;

	/**
	 * Construct an automaton mInterpolantAutomaton which
	 * <ul>
	 * <li>accepts the trace of mCounterexample,
	 * <li>accepts only infeasible traces.
	 * </ul>
	 *
	 * @throws AutomataOperationCanceledException
	 */
	protected abstract void constructInterpolantAutomaton() throws AutomataOperationCanceledException;

	/**
	 * Construct an automaton that
	 * <ul>
	 * <li>accepts the trace of mCounterexample,
	 * <li>accepts only feasible traces.
	 * </ul>
	 */
	protected abstract void constructErrorAutomaton() throws AutomataOperationCanceledException;

	/**
	 * Reports statistics for error automaton construction.
	 */
	protected abstract void reportErrorAutomatonBenchmarks();

	/**
	 * Construct a new automaton mAbstraction such that
	 * <ul>
	 * <li>the language of the new mAbstraction is (not necessary strictly) smaller than the language of the old
	 * mAbstraction
	 * <li>the new mAbstraction accepts all feasible traces of the old mAbstraction (only infeasible traces are removed)
	 * <ul>
	 *
	 * @return true iff the trace of mCounterexample (which was accepted by the old mAbstraction) is not accepted by the
	 *         mAbstraction.
	 * @throws AutomataLibraryException
	 */
	protected abstract boolean refineAbstraction() throws AutomataLibraryException;

	/**
	 * In case error traces are not reported immediately, the analysis may terminate with an empty abstraction or may
	 * run into termination issues, but it has already found out that the program contains errors. This method can be
	 * used to ask for such results whenever the analysis terminates.
	 *
	 * @param errorGeneralizationEnabled
	 *            {@code true} iff error generalization is enabled
	 * @param abstractResult
	 *            result that would be reported by {@link AbstractCegarLoop}
	 * @return {@code true} if at least one feasible counterexample was detected
	 */
	protected abstract boolean isResultUnsafe(boolean errorGeneralizationEnabled, Result abstractResult);

	/**
	 * Add Hoare annotation to the control flow graph. Use the information computed so far annotate the ProgramPoints of
	 * the control flow graph with invariants.
	 */
	protected abstract void computeCFGHoareAnnotation();

	/**
	 * Return the Artifact whose computation was requested. This artifact can be either the control flow graph, an
	 * abstraction, an interpolant automaton, or a negated interpolant automaton. The artifact is only used for
	 * debugging.
	 *
	 * @return The root node of the artifact after it was transformed to an ULTIMATE model.
	 */
	public abstract IElement getArtifact();

	public int getIteration() {
		return mIteration;
	}

	public IProgramExecution<IIcfgTransition<IcfgLocation>, Term> getRcfgProgramExecution() {
		return mRcfgProgramExecution;
	}

	public String errorLocs() {
		return mErrorLocs.toString();
	}

	public final Result iterate() {
		final Result result = iterateInternal();
		mInteractive.send(result);
		return result;
	}

	private Result iterateInternal() {
		mLogger.info("Interprodecural is " + mPref.interprocedural());
		mLogger.info("Hoare is " + mPref.computeHoareAnnotation());
		mLogger.info("Compute interpolants for " + mPref.interpolation());
		mLogger.info("Backedges is " + mPref.interpolantAutomaton());
		mLogger.info("Determinization is " + mPref.interpolantAutomatonEnhancement());
		mLogger.info("Difference is " + mPref.differenceSenwa());
		mLogger.info("Minimize is " + mPref.getMinimization());

		mInteractive.reportStartCegar(mPref);
		mIteration = 0;

		mLogger.info("======== Iteration " + mIteration + "==of CEGAR loop == " + mName + "========");

		mInteractive.reportIteration(mIteration);

		// initialize dump of debugging output to files if necessary
		if (mPref.dumpAutomata()) {
			mDumper = new Dumper(mLogger, mPref, mName, mIteration);
		}
		try {
			getInitialAbstraction();

			if (mIteration <= mPref.watchIteration()
					&& (mPref.artifact() == Artifact.ABSTRACTION || mPref.artifact() == Artifact.RCFG)) {
				mArtifactAutomaton = mAbstraction;
			}
			if (mPref.dumpAutomata()) {
				final String filename = mTaskIdentifier + "_InitialAbstraction";
				writeAutomatonToFile(mAbstraction, filename);
			}
			mCegarLoopBenchmark.reportAbstractionSize(mAbstraction.size(), mIteration);

			mInteractive.waitIfPaused();
			final boolean initalAbstractionCorrect = isAbstractionEmpty();
			if (initalAbstractionCorrect) {
				return reportResult(Result.SAFE);
			}

			for (mIteration = 1; mIteration <= mPref.maxIterations(); mIteration++) {
				final String msg = "=== Iteration " + mIteration + " === " + errorLocs() + "===";
				mServices.getStorage().pushMarker(msg);
				mLogger.info(msg);
				try {

					mInteractive.reportIteration(mIteration);
					mInteractive.waitIfPaused();
					mCegarLoopBenchmark.announceNextIteration();
					if (mPref.dumpAutomata()) {
						mDumper = new Dumper(mLogger, mPref, mName, mIteration);
					}

					final String automatonType;
					final LBool isCounterexampleFeasible = isCounterexampleFeasible();
					if (isCounterexampleFeasible == Script.LBool.SAT) {
						if (CONTINUE_AFTER_ERROR_TRACE_FOUND) {
							if (mLogger.isInfoEnabled()) {
								mLogger.info("Generalizing and excluding counterexample to continue analysis");
							}
							mInteractive.waitIfPaused();
							automatonType = "Error";
							constructErrorAutomaton();
						} else {
							return reportResult(Result.UNSAFE);
						}
					} else if (isCounterexampleFeasible == Script.LBool.UNKNOWN) {
						if (isResultUnsafe(CONTINUE_AFTER_ERROR_TRACE_FOUND, Result.UNKNOWN)) {
							return reportResult(Result.UNSAFE);
						}
						mReasonUnknown = new UnprovabilityReason("unable to decide satisfiability of path constraint");
						return reportResult(Result.UNKNOWN);
					} else {
						mInteractive.waitIfPaused();
						automatonType = "Interpolant";
						constructInterpolantAutomaton();
					}

					if (mInterpolAutomaton != null) {
						mLogger.info(
								automatonType + " automaton has " + mInterpolAutomaton.getStates().size() + " states");
						if (mIteration <= mPref.watchIteration()
								&& mPref.artifact() == Artifact.INTERPOLANT_AUTOMATON) {
							mArtifactAutomaton = mInterpolAutomaton;
						}
						// if (mPref.dumpAutomata()) {
						// writeAutomatonToFile(mInterpolAutomaton,
						// automatonType + "Automaton_Iteration" + mIteration);
						// }
					}

					mInteractive.waitIfPaused();
					final boolean progress = refineAbstraction();
					if (!progress) {
						mLogger.warn("No progress! Counterexample is still accepted by refined abstraction.");
						throw new AssertionError(
								"No progress! Counterexample is still accepted by refined abstraction.");
					}

					if (mInterpolAutomaton != null) {
						mLogger.info("Abstraction has " + mAbstraction.sizeInformation());
						mLogger.info(automatonType + " automaton has " + mInterpolAutomaton.sizeInformation());
						mInteractive.reportSizeInfo(mAbstraction.sizeInformation(),
								mInterpolAutomaton.sizeInformation());
					}

					if (mPref.computeHoareAnnotation()
							&& mPref.getHoareAnnotationPositions() == HoareAnnotationPositions.All) {
						assert new InductivityCheck<>(mServices,
								(INestedWordAutomaton<LETTER, IPredicate>) mAbstraction, false, true,
								new IncrementalHoareTripleChecker(mCsToolkit, false)).getResult() : "Not inductive";
					}

					if (mIteration <= mPref.watchIteration() && mPref.artifact() == Artifact.ABSTRACTION) {
						mArtifactAutomaton = mAbstraction;
					}

					// if (mPref.dumpAutomata()) {
					// final String filename = "Abstraction" + mIteration;
					// writeAutomatonToFile(mAbstraction, filename);
					// }

					final boolean newMaximumReached =
							mCegarLoopBenchmark.reportAbstractionSize(mAbstraction.size(), mIteration);
					if (DUMP_BIGGEST_AUTOMATON && mIteration > 4 && newMaximumReached) {
						final String filename = mIcfg.getIdentifier() + "_BiggestAutomaton";
						writeAutomatonToFile(mAbstraction, filename);
					}

					mInteractive.waitIfPaused();
					final boolean isAbstractionCorrect = isAbstractionEmpty();
					if (isAbstractionCorrect) {
						if (isResultUnsafe(CONTINUE_AFTER_ERROR_TRACE_FOUND, Result.SAFE)) {
							return reportResult(Result.UNSAFE);
						}
						return reportResult(Result.SAFE);
					}
					mInteractive.send(mCegarLoopBenchmark);
				} finally {
					final Set<String> destroyedStorables = mServices.getStorage().destroyMarker(msg);
					if (!destroyedStorables.isEmpty()) {
						mLogger.warn("Destroyed unattended storables created during the last iteration: "
								+ destroyedStorables.stream().collect(Collectors.joining(",")));
					}
				}
			}
			if (isResultUnsafe(CONTINUE_AFTER_ERROR_TRACE_FOUND, Result.USER_LIMIT_ITERATIONS)) {
				return reportResult(Result.UNSAFE);
			}
			return reportResult(Result.USER_LIMIT_ITERATIONS);
		} catch (AutomataOperationCanceledException | ToolchainCanceledException e) {
			return performLimitReachedActions(e);
		} catch (final AutomataLibraryException e) {
			throw new ToolchainExceptionWrapper(Activator.PLUGIN_ID, e);
		}
	}

	protected Result reportResult(final Result result) {
		mCegarLoopBenchmark.setResult(result);

		if (CONTINUE_AFTER_ERROR_TRACE_FOUND) {
			reportErrorAutomatonBenchmarks();
		}

		return result;
	}

	private Result performLimitReachedActions(final IRunningTaskStackProvider e) {
		mRunningTaskStackProvider = e;
		mLogger.warn(MSG_VERIFICATION_CANCELED);

		final Result res;
		if (e instanceof TaskCanceledException) {
			final EnumSet<UserDefinedLimit> limits = ((TaskCanceledException) e).getLimits();
			res = Result.convert(limits.iterator().next());
		} else {
			res = Result.TIMEOUT;
		}

		if (isResultUnsafe(CONTINUE_AFTER_ERROR_TRACE_FOUND, res)) {
			return reportResult(Result.UNSAFE);
		}
		return reportResult(res);
	}

	protected void writeAutomatonToFile(final IAutomaton<LETTER, IPredicate> automaton, final String filename) {
		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.DUMP_TIME);
		new AutomatonDefinitionPrinter<String, String>(new AutomataLibraryServices(mServices),
				determineAutomatonName(automaton), mPref.dumpPath() + File.separator + filename, mPrintAutomataLabeling,
				"", automaton);
		mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.DUMP_TIME);
	}

	private String determineAutomatonName(final IAutomaton<LETTER, IPredicate> automaton) {
		String result;
		if (automaton instanceof INwaBasis) {
			result = "nwa";
		} else if (automaton instanceof IPetriNet) {
			result = "net";
		} else {
			throw new UnsupportedOperationException(
					"unknown kind of automaton " + automaton.getClass().getSimpleName());
		}
		return result;
	}

	public static String addIndentation(final int indentation, final String s) {
		final StringBuilder sb = new StringBuilder("");
		for (int i = 0; i < indentation; i++) {
			sb.append("    ");
		}
		sb.append(s);
		return sb.toString();
	}

	public UnprovabilityReason getReasonUnknown() {
		return mReasonUnknown;
	}
}
