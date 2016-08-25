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
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter.Format;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplicationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.InductivityCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.Artifact;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.HoareAnnotationPositions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.util.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.util.statistics.AStatisticsType;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsElement;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsData;

/**
 * CEGAR loop of a trace abstraction. Can be used to check safety and termination of sequential and concurrent programs.
 * Defines roughly the structure of the CEGAR loop, concrete algorithms are implemented in classes which extend this
 * one.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public abstract class AbstractCegarLoop {

	protected final ILogger mLogger;
	protected final SimplicationTechnique mSimplificationTechnique;
	protected final XnfConversionTechnique mXnfConversionTechnique;

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
	public static Result aggregateResult(final Object value1, final Object value2) {
		final Result result1 = (Result) value1;
		final Result result2 = (Result) value2;
		final Set<Result> results = new HashSet<Result>();
		results.add(result1);
		results.add(result2);
		if (results.contains(Result.UNSAFE)) {
			return Result.UNSAFE;
		} else if (results.contains(Result.UNKNOWN)) {
			return Result.UNKNOWN;
		} else if (results.contains(Result.TIMEOUT)) {
			return Result.TIMEOUT;
		} else if (results.contains(Result.SAFE)) {
			return Result.SAFE;
		} else {
			throw new AssertionError();
		}
	}
	
	public static Function<Object, Function<Object,Object>> s_DefaultAggregation = 
			x -> y -> { return aggregateResult(x, y); };

	/**
	 * Unique mName of this CEGAR loop to distinguish this instance from other instances in a complex verification
	 * task. Important only for debugging and debugging output written to files.
	 */
	private final String mName;

	/**
	 * Node of a recursive control flow graph which stores additional information about the program.
	 */
	protected final RootNode mRootNode;

	/**
	 * Intermediate layer to encapsulate communication with SMT solvers.
	 */
	protected final SmtManager mSmtManager;

	protected final ModifiableGlobalVariableManager mModGlobVarManager;

	/**
	 * Intermediate layer to encapsulate preferences.
	 */
	protected final TAPreferences mPref;

	/**
	 * Set of error location whose reachability is analyzed by this CEGAR loop.
	 */
	protected final Collection<ProgramPoint> mErrorLocs;

	/**
	 * Current Iteration of this CEGAR loop.
	 */
	protected int mIteration = 0;

	/**
	 * Accepting run of the abstraction obtained in this iteration.
	 */
	protected IRun<CodeBlock, IPredicate> mCounterexample;

	/**
	 * Abstraction of this iteration. The language of mAbstraction is a set of traces which is
	 * <ul>
	 * <li>a superset of the feasible program traces.
	 * <li>a subset of the traces which respect the control flow of the program.
	 */
	protected IAutomaton<CodeBlock, IPredicate> mAbstraction;

	/**
	 * IInterpolantGenerator that was used in the current iteration.
	 */
	protected IInterpolantGenerator mInterpolantGenerator;

	/**
	 * Interpolant automaton of this iteration.
	 */
	protected NestedWordAutomaton<CodeBlock, IPredicate> mInterpolAutomaton;

	/**
	 * Program execution that leads to error. Only computed in the last iteration of the CEGAR loop if the program is
	 * incorrect.
	 */
	protected RcfgProgramExecution mRcfgProgramExecution;

	// used for the collection of statistics
	public int mInitialAbstractionSize = 0;
	public int mNumberOfErrorLocations = 0;

	// used for debugging only
	protected IAutomaton<CodeBlock, IPredicate> mArtifactAutomaton;
	protected PrintWriter mIterationPW;
	protected final Format mPrintAutomataLabeling;

	protected CegarLoopStatisticsGenerator mCegarLoopBenchmark;

	protected final IUltimateServiceProvider mServices;
	// protected final IToolchainStorage mToolchainStorage = null; TODO: this is not what we want, is it?
	protected final IToolchainStorage mToolchainStorage;

	private ToolchainCanceledException mToolchainCancelledException;

	public ToolchainCanceledException getToolchainCancelledException() {
		return mToolchainCancelledException;
	}

	public AbstractCegarLoop(final IUltimateServiceProvider services, final IToolchainStorage storage, final String name,
			final RootNode rootNode, final SmtManager smtManager, final TAPreferences taPrefs, final Collection<ProgramPoint> errorLocs,
			final ILogger logger) {
		mServices = services;
		mLogger = logger;
		mSimplificationTechnique = taPrefs.getSimplificationTechnique();
		mXnfConversionTechnique = taPrefs.getXnfConversionTechnique();
		mPrintAutomataLabeling = taPrefs.getAutomataFormat();
		mModGlobVarManager = rootNode.getRootAnnot().getModGlobVarManager();
		mName = name;
		mRootNode = rootNode;
		mSmtManager = smtManager;
		mPref = taPrefs;
		mErrorLocs = errorLocs;
		mToolchainStorage = storage;

	}

	/**
	 * Construct the automaton mAbstraction such that the language recognized by mAbstation is a superset of the
	 * language of the program. The initial abstraction in our implementations will usually be an automaton that has the
	 * same graph as the program.
	 * 
	 * @throws AutomataLibraryException
	 */
	protected abstract void getInitialAbstraction() throws AutomataOperationCanceledException, AutomataLibraryException;

	/**
	 * Return true iff the mAbstraction does not accept any trace.
	 * 
	 * @throws AutomataOperationCanceledException
	 */
	protected abstract boolean isAbstractionCorrect() throws AutomataOperationCanceledException;

	/**
	 * Determine if the trace of mCounterexample is a feasible sequence of CodeBlocks. Return
	 * <ul>
	 * <li>SAT if the trace is feasible
	 * <li>UNSAT if the trace is infeasible
	 * <li>UNKNOWN if the algorithm was not able to determine the feasibility.
	 * </ul>
	 */
	protected abstract LBool isCounterexampleFeasible();

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
	 * Construct a new automaton mAbstraction such that
	 * <ul>
	 * <li>the language of the new mAbstraction is (not necessary strictly) smaller than the language of the old
	 * mAbstraction
	 * <li>the new mAbstraction accepts all feasible traces of the old mAbstraction (only infeasible traces are
	 * removed)
	 * <ul>
	 * 
	 * @return true iff the trace of mCounterexample (which was accepted by the old mAbstraction) is not accepted by
	 *         the mAbstraction.
	 * @throws AutomataLibraryException
	 */
	protected abstract boolean refineAbstraction() throws AutomataOperationCanceledException, AutomataLibraryException;

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

	public RcfgProgramExecution getRcfgProgramExecution() {
		return mRcfgProgramExecution;
	}

	public SmtManager getSmtManager() {
		return mSmtManager;
	}

	public String errorLocs() {
		return mErrorLocs.toString();
	}

	public final Result iterate() {
		mLogger.info("Interprodecural is " + mPref.interprocedural());
		mLogger.info("Hoare is " + mPref.computeHoareAnnotation());
		mLogger.info("Compute interpolants for " + mPref.interpolation());
		mLogger.info("Backedges is " + mPref.interpolantAutomaton());
		mLogger.info("Determinization is " + mPref.interpolantAutomatonEnhancement());
		mLogger.info("Difference is " + mPref.differenceSenwa());
		mLogger.info("Minimize is " + mPref.minimize());

		mIteration = 0;
		mLogger.info("======== Iteration " + mIteration + "==of CEGAR loop == " + mName + "========");

		// intialize dump of debugging output to files if necessary
		if (mPref.dumpAutomata()) {
			dumpInitinalize();
		}
		try {
			getInitialAbstraction();
		} catch (final AutomataOperationCanceledException e1) {
			mLogger.warn("Verification cancelled");
			mCegarLoopBenchmark.setResult(Result.TIMEOUT);
			return Result.TIMEOUT;
		} catch (final AutomataLibraryException e) {
			throw new AssertionError(e.getMessage());
		}

		if (mIteration <= mPref.watchIteration()
				&& (mPref.artifact() == Artifact.ABSTRACTION || mPref.artifact() == Artifact.RCFG)) {
			mArtifactAutomaton = mAbstraction;
		}
		if (mPref.dumpAutomata()) {
			final String filename = mName + "Abstraction" + mIteration;
			writeAutomatonToFile(mAbstraction, filename);
		}
		mInitialAbstractionSize = mAbstraction.size();
		mCegarLoopBenchmark.reportAbstractionSize(mAbstraction.size(), mIteration);
		mNumberOfErrorLocations = mErrorLocs.size();

		boolean initalAbstractionCorrect;
		try {
			initalAbstractionCorrect = isAbstractionCorrect();
		} catch (final AutomataOperationCanceledException e1) {
			mLogger.warn("Verification cancelled");
			mCegarLoopBenchmark.setResult(Result.TIMEOUT);
			return Result.TIMEOUT;
		}
		if (initalAbstractionCorrect) {
			mCegarLoopBenchmark.setResult(Result.SAFE);
			return Result.SAFE;
		}

		for (mIteration = 1; mIteration <= mPref.maxIterations(); mIteration++) {
			mLogger.info("=== Iteration " + mIteration + " === " + errorLocs() + "===");
			mSmtManager.setIteration(mIteration);
			mCegarLoopBenchmark.announceNextIteration();
			if (mPref.dumpAutomata()) {
				dumpInitinalize();
			}
			try {
				final LBool isCounterexampleFeasible = isCounterexampleFeasible();
				if (isCounterexampleFeasible == Script.LBool.SAT) {
					mCegarLoopBenchmark.setResult(Result.UNSAFE);
					return Result.UNSAFE;
				}
				if (isCounterexampleFeasible == Script.LBool.UNKNOWN) {
					mCegarLoopBenchmark.setResult(Result.UNKNOWN);
					return Result.UNKNOWN;
				}
			} catch (final ToolchainCanceledException e) {
				mToolchainCancelledException = e;
				mLogger.warn("Verification cancelled");
				mCegarLoopBenchmark.setResult(Result.TIMEOUT);
				return Result.TIMEOUT;
			}

			try {
				constructInterpolantAutomaton();
			} catch (final AutomataOperationCanceledException e1) {
				mLogger.warn("Verification cancelled");
				mCegarLoopBenchmark.setResult(Result.TIMEOUT);
				return Result.TIMEOUT;
			} catch (final ToolchainCanceledException e) {
				mToolchainCancelledException = e;
				mLogger.warn("Verification cancelled");
				mCegarLoopBenchmark.setResult(Result.TIMEOUT);
				return Result.TIMEOUT;
			}

			mLogger.info("Interpolant Automaton has " + mInterpolAutomaton.getStates().size() + " states");

			if (mIteration <= mPref.watchIteration() && mPref.artifact() == Artifact.INTERPOLANT_AUTOMATON) {
				mArtifactAutomaton = mInterpolAutomaton;
			}
			if (mPref.dumpAutomata()) {
				writeAutomatonToFile(mInterpolAutomaton, "InterpolantAutomaton_Iteration" + mIteration);
			}

			try {
				final boolean progress = refineAbstraction();
				if (!progress) {
					mLogger.warn("No progress! Counterexample is still accepted by refined abstraction.");
					throw new AssertionError("No progress! Counterexample is still accepted by refined abstraction.");
					// return Result.UNKNOWN;
				}
			} catch (final AutomataOperationCanceledException e) {
				mLogger.warn("Verification cancelled");
				mCegarLoopBenchmark.setResult(Result.TIMEOUT);
				mCegarLoopBenchmark.stopIfRunning(CegarLoopStatisticsDefinitions.AbstIntTime.toString());
				return Result.TIMEOUT;
			} catch (final ToolchainCanceledException e) {
				mToolchainCancelledException = e;
				mLogger.warn("Verification cancelled");
				mCegarLoopBenchmark.setResult(Result.TIMEOUT);
				mCegarLoopBenchmark.stopIfRunning(CegarLoopStatisticsDefinitions.AbstIntTime.toString());
				return Result.TIMEOUT;
			} catch (final AutomataLibraryException e) {
				throw new AssertionError("Automata Operation failed" + e.getMessage());
			}

			mLogger.info("Abstraction has " + mAbstraction.sizeInformation());
			mLogger.info("Interpolant automaton has " + mInterpolAutomaton.sizeInformation());

			if (mPref.computeHoareAnnotation() && 
					mPref.getHoareAnnotationPositions() == HoareAnnotationPositions.All) {
				assert (new InductivityCheck(mServices, (INestedWordAutomaton<CodeBlock, IPredicate>) mAbstraction,
						false, true, new IncrementalHoareTripleChecker(mRootNode.getRootAnnot().getManagedScript(), mModGlobVarManager)))
								.getResult() : "Not inductive";
			}

			if (mIteration <= mPref.watchIteration() && mPref.artifact() == Artifact.ABSTRACTION) {
				mArtifactAutomaton = mAbstraction;
			}

			if (mPref.dumpAutomata()) {
				final String filename = "Abstraction" + mIteration;
				writeAutomatonToFile(mAbstraction, filename);
			}

			mCegarLoopBenchmark.reportAbstractionSize(mAbstraction.size(), mIteration);

			boolean isAbstractionCorrect;
			try {
				isAbstractionCorrect = isAbstractionCorrect();
			} catch (final AutomataOperationCanceledException e) {
				mLogger.warn("Verification cancelled");
				mCegarLoopBenchmark.setResult(Result.TIMEOUT);
				return Result.TIMEOUT;
			}
			if (isAbstractionCorrect) {
				mCegarLoopBenchmark.setResult(Result.SAFE);
				return Result.SAFE;
			}
		}
		mCegarLoopBenchmark.setResult(Result.TIMEOUT);
		return Result.TIMEOUT;
	}

	protected void writeAutomatonToFile(final IAutomaton<CodeBlock, IPredicate> automaton, final String filename) {
		new AutomatonDefinitionPrinter<String, String>(new AutomataLibraryServices(mServices), "nwa",
				mPref.dumpPath() + "/" + filename, mPrintAutomataLabeling, "", automaton);
	}

	private void dumpInitinalize() {
		final File file = new File(mPref.dumpPath() + "/" + mName + "_iteration" + mIteration + ".txt");
		FileWriter fileWriter;
		try {
			fileWriter = new FileWriter(file);
			mIterationPW = new PrintWriter(fileWriter);
		} catch (final IOException e) {
			e.printStackTrace();
		}
	}

	/*
	 * TODO unify sequential and concurrent
	 */
	protected static void dumpNestedRun(final IRun<CodeBlock, IPredicate> run, final PrintWriter pW, final ILogger logger) {
		final NestedWord<CodeBlock> counterexample = NestedWord.nestedWord(run.getWord());
		ArrayList<IPredicate> stateSequence = null;
		if (run instanceof NestedRun) {
			stateSequence = ((NestedRun<CodeBlock, IPredicate>) run).getStateSequence();
		}
		String line;
		int indentation = 0;
		try {
			line = "===============Run of potential Counterexample==========";
			pW.println(line);
			for (int i = 0; i < counterexample.length(); i++) {

				if (run instanceof NestedRun) {
					line = addIndentation(indentation,
							"Location" + i + ": " + ((ISLPredicate) stateSequence.get(i)).getProgramPoint());
					logger.debug(line);
					pW.println(line);
				}

				if (counterexample.isCallPosition(i)) {
					indentation++;
				}
				line = addIndentation(indentation,
						"Statement" + i + ": " + counterexample.getSymbolAt(i).getPrettyPrintedStatements());
				logger.debug(line);
				pW.println(line);
				if (counterexample.isReturnPosition(i)) {
					indentation--;
				}
			}
			pW.println("ErrorLocation");
			pW.println("");
			pW.println("");
		} finally {
			pW.flush();
		}
	}

	@SuppressWarnings("unused")
	private void dumpSsa(final Term[] ssa) {
		final FormulaUnLet unflet = new FormulaUnLet();
		try {
			mIterationPW.println("===============SSA of potential Counterexample==========");
			for (int i = 0; i < ssa.length; i++) {
				mIterationPW.println("UnFletedTerm" + i + ": " + unflet.unlet(ssa[i]));
			}
			mIterationPW.println("");
			mIterationPW.println("");
		} finally {
			mIterationPW.flush();
		}
	}

	@SuppressWarnings("unused")
	private void dumpStateFormulas(final IPredicate[] interpolants) {
		try {
			mIterationPW.println("===============Interpolated StateFormulas==========");
			for (int i = 0; i < interpolants.length; i++) {
				mIterationPW.println("Interpolant" + i + ": " + interpolants[i]);
			}
			mIterationPW.println("");
			mIterationPW.println("");
		} finally {
			mIterationPW.flush();
		}
	}

	public static String addIndentation(final int indentation, final String s) {
		final StringBuilder sb = new StringBuilder("");
		for (int i = 0; i < indentation; i++) {
			sb.append("    ");
		}
		sb.append(s);
		return sb.toString();
	}

	static void dumpBackedges(final ProgramPoint repLocName, final int position, final IPredicate state,
			final Collection<IPredicate> linPredStates, final CodeBlock transition, final IPredicate succState, final IPredicate sf1,
			final IPredicate sf2, final LBool result, final int iteration, final int satProblem, final PrintWriter iterationPW) {
		try {
			iterationPW.println(repLocName + " occured once again at position " + position + ". Added backedge");
			iterationPW.println("from:   " + state);
			iterationPW.println("labeled with:   " + transition.getPrettyPrintedStatements());
			iterationPW.println("to:   " + succState);
			if (linPredStates != null) {
				iterationPW.println("for each linPredStates:   " + linPredStates);
			}
			if (satProblem == -1) {
				iterationPW.println("because ");
			} else {
				assert (result == Script.LBool.UNSAT);
				iterationPW.println("because Iteration" + iteration + "_SatProblem" + satProblem + " says:");
			}
			iterationPW.println("  " + sf1);
			iterationPW.println("implies");
			iterationPW.println("  " + sf2);
			iterationPW.println("");
		} finally {
			iterationPW.flush();
		}
	}
	
	
	public enum CegarLoopStatisticsDefinitions implements IStatisticsElement {
		
		Result(Result.class, AbstractCegarLoop.s_DefaultAggregation, AStatisticsType.s_DataBeforeKey),
		OverallTime(Long.class, AStatisticsType.s_LongAddition, AStatisticsType.s_TimeBeforeKey),
		OverallIterations(Integer.class, AStatisticsType.s_IntegerAddition, AStatisticsType.s_DataBeforeKey),
		TraceHistogramMax(Integer.class, AStatisticsType.s_IntegerMaximum, AStatisticsType.s_DataBeforeKey),
		AutomataDifference(Long.class, AStatisticsType.s_LongAddition, AStatisticsType.s_TimeBeforeKey),
		DeadEndRemovalTime(Long.class, AStatisticsType.s_LongAddition, AStatisticsType.s_TimeBeforeKey),
		AutomataMinimizationTime(Long.class, AStatisticsType.s_LongAddition, AStatisticsType.s_TimeBeforeKey),
		HoareAnnotationTime(Long.class, AStatisticsType.s_LongAddition, AStatisticsType.s_TimeBeforeKey),
		HoareTripleCheckerStatistics(StatisticsData.class, AStatisticsType.s_StatisticsDataAggregation, AStatisticsType.s_KeyBeforeData),
		PredicateUnifierStatistics(StatisticsData.class, AStatisticsType.s_StatisticsDataAggregation, AStatisticsType.s_KeyBeforeData),
		StatesRemovedByMinimization(Long.class, AStatisticsType.s_IntegerAddition, AStatisticsType.s_DataBeforeKey),
		BasicInterpolantAutomatonTime(Long.class, AStatisticsType.s_LongAddition, AStatisticsType.s_TimeBeforeKey),
		BiggestAbstraction(Integer.class, CegarStatisticsType.s_SizeIterationPairDataAggregation, AStatisticsType.s_KeyBeforeData),
		TraceCheckerStatistics(StatisticsData.class, AStatisticsType.s_StatisticsDataAggregation, AStatisticsType.s_KeyBeforeData),
		InterpolantConsolidationStatistics(StatisticsData.class, AStatisticsType.s_StatisticsDataAggregation, AStatisticsType.s_KeyBeforeData),
		InterpolantCoveringCapability(BackwardCoveringInformation.class, CoverageAnalysis.s_DefaultAggregation, AStatisticsType.s_DataBeforeKey),
		TotalInterpolationStatistics(StatisticsData.class, AStatisticsType.s_StatisticsDataAggregation, AStatisticsType.s_KeyBeforeData),
		AbstIntTime(Long.class, AStatisticsType.s_LongAddition, AStatisticsType.s_TimeBeforeKey),
		AbstIntIterations(Integer.class, AStatisticsType.s_IntegerAddition, AStatisticsType.s_DataBeforeKey),
		AbstIntStrong(Integer.class, AStatisticsType.s_IntegerAddition, AStatisticsType.s_DataBeforeKey),
		;
		
		private final Class<?> mClazz;
		private final Function<Object, Function<Object, Object>> mAggr;
		private final Function<String, Function<Object, String>> mPrettyprinter;
		
		CegarLoopStatisticsDefinitions(final Class<?> clazz, 
				final Function<Object, Function<Object, Object>> aggr, 
				final Function<String, Function<Object, String>> prettyprinter) {
			mClazz = clazz;
			mAggr = aggr;
			mPrettyprinter = prettyprinter;
		}

		@Override
		public Object aggregate(final Object o1, final Object o2) {
			return mAggr.apply(o1).apply(o2);
		}

		@Override
		public String prettyprint(final Object o) {
			return mPrettyprinter.apply(name()).apply(o);
		}

		@Override
		public Class<?> getDataType() {
			return mClazz;
		}
	}

}
