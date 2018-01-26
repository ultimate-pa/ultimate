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

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter.Format;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.IRunningTaskStackProvider;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainExceptionWrapper;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovabilityReason;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interactive.InteractiveCegar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.InductivityCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.Artifact;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.HoareAnnotationPositions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.IInterpolantGenerator;

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
	 * <ul>
	 * <li>SAFE: there is no feasible trace to an error location
	 * <li>UNSAFE: there is a feasible trace to an error location (the underlying program has at least one execution
	 * which violates its specification)
	 * <li>UNKNOWN: we found a trace for which we could not decide feasibility or we found an infeasible trace but were
	 * not able to exclude it in abstraction refinement.
	 * <li>TIMEOUT:
	 */
	public enum Result {
		SAFE, UNSAFE, TIMEOUT, UNKNOWN
	}

	protected final ILogger mLogger;
	protected final SimplificationTechnique mSimplificationTechnique;
	protected final XnfConversionTechnique mXnfConversionTechnique;

	/**
	 * Unique mName of this CEGAR loop to distinguish this instance from other instances in a complex verification task.
	 * Important only for debugging and debugging output written to files.
	 */
	private final String mName;

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
	protected IInterpolantGenerator mInterpolantGenerator;

	/**
	 * Interpolant automaton of this iteration.
	 */
	protected NestedWordAutomaton<LETTER, IPredicate> mInterpolAutomaton;

	/**
	 * Program execution that leads to error. Only computed in the last iteration of the CEGAR loop if the program is
	 * incorrect.
	 */
	protected IcfgProgramExecution mRcfgProgramExecution;

	// used for debugging only
	protected IAutomaton<LETTER, IPredicate> mArtifactAutomaton;

	protected final Format mPrintAutomataLabeling;

	protected CegarLoopStatisticsGenerator mCegarLoopBenchmark;

	protected final IUltimateServiceProvider mServices;
	protected final IToolchainStorage mToolchainStorage;

	private IRunningTaskStackProvider mRunningTaskStackProvider;

	protected Dumper mDumper;
	/**
	 * only != null if analysis result is UNKNOWN Textual explanation why result is unknown.
	 */
	private UnprovabilityReason mReasonUnknown;
	protected final InteractiveCegar mInteractive;

	private static final boolean DUMP_BIGGEST_AUTOMATON = false;

	public AbstractCegarLoop(final IUltimateServiceProvider services, final IToolchainStorage storage,
			final String name, final IIcfg<?> rootNode, final CfgSmtToolkit csToolkit,
			final PredicateFactory predicateFactory, final TAPreferences taPrefs,
			final Collection<? extends IcfgLocation> errorLocs, final ILogger logger) {
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
		mToolchainStorage = storage;
		mInteractive = new InteractiveCegar(services, logger);
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

	public IcfgProgramExecution getRcfgProgramExecution() {
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
		} catch (final AutomataOperationCanceledException e) {
			return performTimeoutActions(e);
		} catch (final AutomataLibraryException e) {
			throw new ToolchainExceptionWrapper(Activator.PLUGIN_ID, e);
		}

		if (mIteration <= mPref.watchIteration()
				&& (mPref.artifact() == Artifact.ABSTRACTION || mPref.artifact() == Artifact.RCFG)) {
			mArtifactAutomaton = mAbstraction;
		}
		if (mPref.dumpAutomata()) {
			final String filename = mName + "Abstraction" + mIteration;
			writeAutomatonToFile(mAbstraction, filename);
		}
		mCegarLoopBenchmark.reportAbstractionSize(mAbstraction.size(), mIteration);

		mInteractive.waitIfPaused();
		boolean initalAbstractionCorrect;
		try {
			initalAbstractionCorrect = isAbstractionEmpty();
		} catch (final AutomataOperationCanceledException e) {
			return performTimeoutActions(e);
		}
		if (initalAbstractionCorrect) {
			return reportResult(Result.SAFE);
		}

		for (mIteration = 1; mIteration <= mPref.maxIterations(); mIteration++) {
			mLogger.info("=== Iteration " + mIteration + " === " + errorLocs() + "===");
			mInteractive.reportIteration(mIteration);
			mInteractive.waitIfPaused();
			mCegarLoopBenchmark.announceNextIteration();
			if (mPref.dumpAutomata()) {
				mDumper = new Dumper(mLogger, mPref, mName, mIteration);
			}

			final String automatonType;
			try {
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
			} catch (final AutomataOperationCanceledException | ToolchainCanceledException e) {
				return performTimeoutActions(e);
			}

			if (mInterpolAutomaton != null) {
				mLogger.info(automatonType + " automaton has " + mInterpolAutomaton.getStates().size() + " states");
				if (mIteration <= mPref.watchIteration() && mPref.artifact() == Artifact.INTERPOLANT_AUTOMATON) {
					mArtifactAutomaton = mInterpolAutomaton;
				}
				if (mPref.dumpAutomata()) {
					writeAutomatonToFile(mInterpolAutomaton, automatonType + "Automaton_Iteration" + mIteration);
				}
			}

			mInteractive.waitIfPaused();
			try {
				final boolean progress = refineAbstraction();
				if (!progress) {
					mLogger.warn("No progress! Counterexample is still accepted by refined abstraction.");
					throw new AssertionError("No progress! Counterexample is still accepted by refined abstraction.");
				}
			} catch (final ToolchainCanceledException | AutomataOperationCanceledException e) {
				return performTimeoutActions(e);
			} catch (final AutomataLibraryException e) {
				throw new ToolchainExceptionWrapper(Activator.PLUGIN_ID, e);
			}

			if (mInterpolAutomaton != null) {
				mLogger.info("Abstraction has " + mAbstraction.sizeInformation());
				mLogger.info(automatonType + " automaton has " + mInterpolAutomaton.sizeInformation());
				mInteractive.reportSizeInfo(mAbstraction.sizeInformation(), mInterpolAutomaton.sizeInformation());
			}

			if (mPref.computeHoareAnnotation() && mPref.getHoareAnnotationPositions() == HoareAnnotationPositions.All) {
				assert new InductivityCheck<>(mServices, (INestedWordAutomaton<LETTER, IPredicate>) mAbstraction, false,
						true, new IncrementalHoareTripleChecker(mCsToolkit)).getResult() : "Not inductive";
			}

			if (mIteration <= mPref.watchIteration() && mPref.artifact() == Artifact.ABSTRACTION) {
				mArtifactAutomaton = mAbstraction;
			}

			if (mPref.dumpAutomata()) {
				final String filename = "Abstraction" + mIteration;
				writeAutomatonToFile(mAbstraction, filename);
			}

			final boolean newMaximumReached =
					mCegarLoopBenchmark.reportAbstractionSize(mAbstraction.size(), mIteration);
			if (DUMP_BIGGEST_AUTOMATON && mIteration > 4 && newMaximumReached) {
				final String filename = mIcfg.getIdentifier();
				writeAutomatonToFile(mAbstraction, filename);
			}

			mInteractive.waitIfPaused();
			boolean isAbstractionCorrect;
			try {
				isAbstractionCorrect = isAbstractionEmpty();
			} catch (final AutomataOperationCanceledException e) {
				return performTimeoutActions(e);
			}
			if (isAbstractionCorrect) {
				if (isResultUnsafe(CONTINUE_AFTER_ERROR_TRACE_FOUND, Result.SAFE)) {
					return reportResult(Result.UNSAFE);
				}
				return reportResult(Result.SAFE);
			}
			mInteractive.send(mCegarLoopBenchmark);
		}
		if (isResultUnsafe(CONTINUE_AFTER_ERROR_TRACE_FOUND, Result.TIMEOUT)) {
			return reportResult(Result.UNSAFE);
		}
		return reportResult(Result.TIMEOUT);
	}

	protected Result reportResult(final Result result) {
		mCegarLoopBenchmark.setResult(result);

		if (CONTINUE_AFTER_ERROR_TRACE_FOUND) {
			reportErrorAutomatonBenchmarks();
		}

		return result;
	}

	private Result performTimeoutActions(final IRunningTaskStackProvider e) {
		mRunningTaskStackProvider = e;
		mLogger.warn(MSG_VERIFICATION_CANCELED);
		if (isResultUnsafe(CONTINUE_AFTER_ERROR_TRACE_FOUND, Result.TIMEOUT)) {
			return reportResult(Result.UNSAFE);
		}
		return reportResult(Result.TIMEOUT);
	}

	protected void writeAutomatonToFile(final IAutomaton<LETTER, IPredicate> automaton, final String filename) {
		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.DUMP_TIME);
		new AutomatonDefinitionPrinter<String, String>(new AutomataLibraryServices(mServices), "nwa",
				mPref.dumpPath() + File.separator + filename, mPrintAutomataLabeling, "", automaton);
		mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.DUMP_TIME);
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
