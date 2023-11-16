/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder;

import java.io.IOException;
import java.math.BigDecimal;
import java.util.Collections;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IStorable;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.HistoryRecordingScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.DiffWrapperScript;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.WrapperScript;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.muses.MusEnumerationScript;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.TerminationRequest;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.NonIncrementalScriptor;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.Scriptor;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.ScriptorWithGetInterpolants;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.ScriptorWithGetInterpolants.ExternalInterpolator;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.SmtInterpolLogProxyWrapper;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.ReflectionUtil;

/**
 * Wrapper that constructs SMTInterpol or an external SMT solver.
 *
 * @author heizmann@informatik.uni-freiburg.de
 * @author dietsch@informatik.uni-freiburg.de
 */
public final class SolverBuilder {

	public enum SolverMode {
		Internal_SMTInterpol(false),

		External_PrincessInterpolationMode(true),

		External_SMTInterpolInterpolationMode(true),

		External_Z3InterpolationMode(true),

		External_MathsatInterpolationMode(true),

		External_ModelsAndUnsatCoreMode(true),

		External_ModelsMode(true),

		External_DefaultMode(true);

		private final boolean mIsExternal;

		SolverMode(final boolean isExternal) {
			mIsExternal = isExternal;
		}

		public boolean isExternal() {
			return mIsExternal;
		}
	}

	public static final boolean USE_DIFF_WRAPPER_SCRIPT = true;

	private static final boolean USE_WRAPPER_SCRIPT_WITH_TERM_CONSTRUCTION_CHECKS = false;

	private SolverBuilder() {
		// do not instantiate utility class
	}

	/**
	 * Create simple {@link SolverSettings} instance that can be used to start SMTInterpol.
	 */
	public static SolverSettings constructSolverSettings() throws AssertionError {
		return new SolverSettings(SolverMode.Internal_SMTInterpol, false, false, null, null, -1, null, false, false,
				false, null, null, false, false, null, false, Collections.emptyMap(), null, false);
	}

	/**
	 * Build an SMT solver.
	 *
	 * @return A Script that represents an SMT solver which is defined by settings.
	 */
	public static Script buildScript(final IUltimateServiceProvider services, final SolverSettings settings) {
		final ILogger localLogger = services.getLoggingService().getLogger(SolverBuilder.class);
		final ILogger solverLogger = getSolverLogger(services, settings);
		Script script;
		if (settings.useExternalSolver()) {
			script = createExternalSolver(services, settings, solverLogger, localLogger);
		} else {
			localLogger.info(
					"Constructing new instance of SMTInterpol with explicit timeout %s ms and remaining time %s ms",
					settings.getTimeoutSmtInterpol(), services.getProgressMonitorService().remainingTime());
			final LogProxy loggerWrapper = new SmtInterpolLogProxyWrapper(solverLogger);
			final TerminationRequest termRequest =
					new SMTInterpolTerminationRequest(services.getProgressMonitorService());
			if (settings.useMinimalUnsatCoreEnumerationForSmtInterpol()) {
				script = new MusEnumerationScript(new SMTInterpol(loggerWrapper, termRequest));
			} else {
				script = new SMTInterpol(loggerWrapper, termRequest);
			}
			if (settings.dumpSmtScriptToFile()) {
				script = wrapScriptWithLoggingScript(services, script, localLogger,
						settings.constructFullPathOfDumpedScript());
			}
			if (settings.getTimeoutSmtInterpol() != -1) {
				script.setOption(":timeout", settings.getTimeoutSmtInterpol());
			}

			// ensure that SMTInterpol is exited when toolchain ends
			script = new SelfDestructingSolverStorable(script, services.getStorage());
		}

		if (USE_WRAPPER_SCRIPT_WITH_TERM_CONSTRUCTION_CHECKS) {
			script = new ScriptWithTermConstructionChecks(script);
		}
		if (settings.dumpFeatureExtractionVector()) {
			script = new SMTFeatureExtractorScript(script, getSolverLogger(services, settings),
					settings.getFeatureVectorDumpPath());
		}
		if (settings.dumpUnsatCoreTrackBenchmark()) {
			script = new LoggingScriptForUnsatCoreBenchmarks(script, settings.getBaseNameOfDumpedScript(),
					settings.getPathOfDumpedScript());
		}
		if (settings.dumpMainTrackBenchmark()) {
			script = new LoggingScriptForMainTrackBenchmarks(script, settings.getBaseNameOfDumpedScript(),
					settings.getPathOfDumpedScript());
		}
		return new HistoryRecordingScript(script);
	}

	private static Script createExternalSolver(final IUltimateServiceProvider services, final SolverSettings settings,
			final ILogger solverLogger, final ILogger localLogger) {
		assert settings.getSolverMode() == null || settings
				.getSolverMode() != SolverMode.Internal_SMTInterpol : "You set solver mode to Internal* and enabled useExternalSolver";
		final String command = settings.getCommandExternalSolver();
		localLogger.info("Constructing external solver with command: %s", settings.getCommandExternalSolver());
		final String fullPathOfDumpedFile;
		if (settings.dumpSmtScriptToFile()) {
			fullPathOfDumpedFile = settings.constructFullPathOfDumpedScript();
			localLogger.info("Dumping SMT script to " + fullPathOfDumpedFile);
		} else {
			fullPathOfDumpedFile = null;
		}

		Script script;
		try {
			final ExternalInterpolator externalInterpolator = settings.getExternalInterpolator();
			if (externalInterpolator == null) {
				if (settings.fakeNonIncrementalScript()) {
					script = new NonIncrementalScriptor(command, solverLogger, services, "External_FakeNonIncremental",
							settings.dumpSmtScriptToFile(), settings.getPathOfDumpedScript(),
							settings.getBaseNameOfDumpedScript(), fullPathOfDumpedFile);
				} else {
					script = new Scriptor(command, solverLogger, services, "External", fullPathOfDumpedFile);
				}
			} else {
				localLogger.info("external solver will use " + externalInterpolator + " interpolation mode");
				script = new ScriptorWithGetInterpolants(command, solverLogger, services, externalInterpolator,
						"ExternalInterpolator", fullPathOfDumpedFile);
			}
			if (settings.useDiffWrapper()) {
				script = new DiffWrapperScript(script);
			}
		} catch (final IOException e) {
			localLogger.fatal("Unable to construct solver: %s", e.getMessage());
			throw new RuntimeException(e);
		}
		return script;
	}

	public static Script buildAndInitializeSolver(final IUltimateServiceProvider services,
			final SolverSettings solverSettings, final String solverId) throws AssertionError {

		if (solverSettings.getSolverMode() == null) {
			throw new IllegalArgumentException(
					"You cannot initialize a solver without specifying the solver mode in the solver settings instance");
		}

		final Script script = SolverBuilder.buildScript(services, solverSettings);

		if (!solverSettings.getAdditionalOptions().isEmpty()) {
			for (final Entry<String, String> setting : solverSettings.getAdditionalOptions().entrySet()) {
				script.setOption(":" + setting.getKey(), setting.getValue());
			}
		}

		setSolverModeDependentOptions(solverSettings, script);

		final String advertising = "SMT script generated on " + CoreUtil.getIsoUtcTimestampWithUtcOffset()
				+ " by Ultimate (https://ultimate.informatik.uni-freiburg.de/)";

		script.setInfo(":source", advertising);
		script.setInfo(":smt-lib-version", new BigDecimal("2.5"));
		script.setInfo(":category", new QuotedObject("industrial"));
		script.setInfo(":ultimate-id", solverId);
		return script;
	}

	private static Script wrapScriptWithLoggingScript(final IUltimateServiceProvider services, final Script script,
			final ILogger localLogger, final String fullPathOfDumpedFile) {
		final Script wrappedScript;
		try {
			// wrap with SelfDestructingSolverStorable to ensure that .gz streams are closed if solver crashes
			wrappedScript = new SelfDestructingSolverStorable(new LoggingScript(script, fullPathOfDumpedFile, true),
					services.getStorage());
			localLogger.info("Dumping SMT script to " + fullPathOfDumpedFile);
		} catch (final IOException e) {
			localLogger.error("Unable dump SMT script to " + fullPathOfDumpedFile);
			throw new RuntimeException(e);
		}
		return wrappedScript;
	}

	private static ILogger getSolverLogger(final IUltimateServiceProvider services, final SolverSettings settings) {
		if (settings.getSolverLogger() != null) {
			return settings.getSolverLogger();
		}
		return services.getLoggingService().getLoggerForExternalTool(SolverBuilder.class);
	}

	private static void setSolverModeDependentOptions(final SolverSettings solverSettings, final Script script)
			throws AssertionError {
		final Logics logic = solverSettings.getSolverLogics();
		switch (solverSettings.getSolverMode()) {
		case External_DefaultMode:
			if (logic != null) {
				script.setLogic(logic);
			}
			break;
		case External_ModelsMode:
			script.setOption(":produce-models", true);
			if (logic != null) {
				script.setLogic(logic);
			}
			break;
		case External_ModelsAndUnsatCoreMode:
			script.setOption(":produce-models", true);
			script.setOption(":produce-unsat-cores", true);
			if (logic != null) {
				script.setLogic(logic);
			}
			break;
		case External_PrincessInterpolationMode:
		case External_SMTInterpolInterpolationMode:
		case External_MathsatInterpolationMode:
			script.setOption(":produce-models", true);
			script.setOption(":produce-interpolants", true);
			if (logic != null) {
				script.setLogic(logic);
			}
			break;
		case External_Z3InterpolationMode:
			script.setOption(":produce-models", true);
			script.setOption(":produce-interpolants", true);
			if (logic != null) {
				script.setLogic(logic);
				final Sort indexSort;
				if (logic.isArray()) {
					// add array-ext function
					indexSort = SmtSortUtils.getIntSort(script);
					final Sort intSort = SmtSortUtils.getIntSort(script);
					final Sort intArraySort = SmtSortUtils.getArraySort(script, indexSort, intSort);
					script.declareFun("array-ext", new Sort[] { intArraySort, intArraySort }, indexSort);
				} else if (logic.isBitVector()) {
					// do nothing. several have to be added here
				}
			}
			break;
		case Internal_SMTInterpol:
			script.setOption(":produce-models", true);
			script.setOption(":produce-unsat-cores", true);
			script.setOption(":produce-interpolants", true);
			script.setOption(":interpolant-check-mode", true);
			script.setOption(":proof-transformation", "LU");
			if (logic == null) {
				throw new AssertionError("SMTInterpol requires explicit logic");
			}
			script.setLogic(logic);
			break;
		default:
			throw new AssertionError("unknown solver");
		}
	}

	private static final class SMTInterpolTerminationRequest implements TerminationRequest {
		private final IProgressMonitorService mMonitor;

		SMTInterpolTerminationRequest(final IProgressMonitorService monitor) {
			mMonitor = monitor;
		}

		@Override
		public boolean isTerminationRequested() {
			return !mMonitor.continueProcessing();
		}
	}

	/**
	 * Settings that define how a solver is build.
	 */
	public static final class SolverSettings {

		private final ILogger mSolverLogger;

		/**
		 * Emulate incremental script (push/pop) using reset and re-asserting all terms and re-declaring all sorts and
		 * functions.
		 */
		private final boolean mFakeNonIncrementalScript;

		private final boolean mUseExternalSolver;

		/**
		 * What shell command should be used to call the external smt solver?
		 */
		private final String mExternalSolverCommand;

		private final long mTimeoutSmtInterpol;

		private final ExternalInterpolator mExternalInterpolator;

		/**
		 * Write SMT solver script to file.
		 */
		private final boolean mDumpSmtScriptToFile;

		/**
		 * Path to which the SMT solver script is written.
		 */
		private final String mPathOfDumpedScript;

		/**
		 * Base name (without path and without file ending) of the file to which the SMT solver script is written.
		 */
		private final String mBaseNameOfDumpedScript;

		/**
		 * Use the diff wrapper script to add support for the diff function.
		 */
		private final boolean mUseDiffWrapper;

		private final boolean mDumpFeatureVector;

		private final String mFeatureVectorDumpPath;

		private final boolean mDumpUnsatCoreTrackBenchmark;

		private final boolean mDumpMainTrackBenchmark;

		private final SolverMode mSolverMode;

		private final Logics mSolverLogics;

		private final boolean mCompressDumpedScript;

		private final Map<String, String> mAdditionalOptions;

		private final boolean mUseMinimalUnsatCoreEnumerationForSmtInterpol;

		private SolverSettings(final SolverMode solverMode, final boolean fakeNonIncrementalScript,
				final boolean useExternalSolver, final String commandExternalSolver, final Logics solverLogic,
				final long timeoutSmtInterpol, final ExternalInterpolator externalInterpolator,
				final boolean dumpSmtScriptToFile, final boolean dumpUnsatCoreTrackBenchmark,
				final boolean dumpMainTrackBenchmark, final String pathOfDumpedScript,
				final String baseNameOfDumpedScript, final boolean useDiffWrapper, final boolean dumpFeatureVector,
				final String featureVectorDumpPath, final boolean compressDumpedScript,
				final Map<String, String> additionalOptions, final ILogger logger,
				final boolean useMinimalUnsatCoreEnumerationForSmtInterpol) {
			mSolverMode = solverMode;
			mFakeNonIncrementalScript = fakeNonIncrementalScript;
			mUseExternalSolver = useExternalSolver;
			mExternalSolverCommand = commandExternalSolver;
			mSolverLogics = solverLogic;
			mTimeoutSmtInterpol = timeoutSmtInterpol;
			mExternalInterpolator = externalInterpolator;
			mDumpSmtScriptToFile = dumpSmtScriptToFile;
			mDumpUnsatCoreTrackBenchmark = dumpUnsatCoreTrackBenchmark;
			mDumpMainTrackBenchmark = dumpMainTrackBenchmark;
			mPathOfDumpedScript = pathOfDumpedScript;
			mBaseNameOfDumpedScript = baseNameOfDumpedScript;
			mUseDiffWrapper = useDiffWrapper;
			mDumpFeatureVector = dumpFeatureVector;
			mFeatureVectorDumpPath = featureVectorDumpPath;
			mCompressDumpedScript = compressDumpedScript;
			mAdditionalOptions = additionalOptions;
			mSolverLogger = logger;
			mUseMinimalUnsatCoreEnumerationForSmtInterpol = useMinimalUnsatCoreEnumerationForSmtInterpol;
		}

		public boolean fakeNonIncrementalScript() {
			return mFakeNonIncrementalScript;
		}

		public boolean useExternalSolver() {
			return mUseExternalSolver;
		}

		public Map<String, String> getAdditionalOptions() {
			return mAdditionalOptions;
		}

		public String getCommandExternalSolver() {
			return mExternalSolverCommand;
		}

		public long getTimeoutSmtInterpol() {
			return mTimeoutSmtInterpol;
		}

		public ExternalInterpolator getExternalInterpolator() {
			return mExternalInterpolator;
		}

		public Logics getSolverLogics() {
			return mSolverLogics;
		}

		public boolean dumpSmtScriptToFile() {
			return mDumpSmtScriptToFile;
		}

		public boolean compressDumpedScript() {
			return mCompressDumpedScript;
		}

		public boolean dumpUnsatCoreTrackBenchmark() {
			return mDumpUnsatCoreTrackBenchmark;
		}

		public boolean dumpMainTrackBenchmark() {
			return mDumpMainTrackBenchmark;
		}

		public String getPathOfDumpedScript() {
			return mPathOfDumpedScript;
		}

		public String getBaseNameOfDumpedScript() {
			return mBaseNameOfDumpedScript;
		}

		/**
		 * Check whether to use the diff wrapper script to add support for the diff function.
		 */
		public boolean useDiffWrapper() {
			return mUseDiffWrapper;
		}

		public boolean useMinimalUnsatCoreEnumerationForSmtInterpol() {
			return mUseMinimalUnsatCoreEnumerationForSmtInterpol;
		}

		public boolean dumpFeatureExtractionVector() {
			return mDumpFeatureVector;
		}

		public String getFeatureVectorDumpPath() {
			return mFeatureVectorDumpPath;
		}

		public SolverMode getSolverMode() {
			return mSolverMode;
		}

		public ILogger getSolverLogger() {
			return mSolverLogger;
		}

		public String constructFullPathOfDumpedScript() {
			final StringBuilder sb = new StringBuilder();
			sb.append(CoreUtil.addFileSeparator(getPathOfDumpedScript()));
			sb.append(getBaseNameOfDumpedScript());
			if (compressDumpedScript()) {
				sb.append(".smt2.gz");
			} else {
				sb.append(".smt2");
			}
			return sb.toString();
		}

		public SolverSettings setDumpSmtScriptToFile(final boolean enabled, final String folderPathOfDumpedFile,
				final String basenameOfDumpedFile, final boolean compressScript) {
			return new SolverSettings(mSolverMode, mFakeNonIncrementalScript, mUseExternalSolver,
					mExternalSolverCommand, mSolverLogics, mTimeoutSmtInterpol, mExternalInterpolator, enabled,
					mDumpUnsatCoreTrackBenchmark, mDumpMainTrackBenchmark, folderPathOfDumpedFile, basenameOfDumpedFile,
					mUseDiffWrapper, mDumpFeatureVector, mFeatureVectorDumpPath, compressScript, mAdditionalOptions,
					mSolverLogger, mUseMinimalUnsatCoreEnumerationForSmtInterpol);
		}

		public SolverSettings setDumpUnsatCoreTrackBenchmark(final boolean enable) {
			assert !enable || mDumpSmtScriptToFile && mPathOfDumpedScript != null && mBaseNameOfDumpedScript != null;
			return new SolverSettings(mSolverMode, mFakeNonIncrementalScript, mUseExternalSolver,
					mExternalSolverCommand, mSolverLogics, mTimeoutSmtInterpol, mExternalInterpolator,
					mDumpSmtScriptToFile, enable, mDumpMainTrackBenchmark, mPathOfDumpedScript, mBaseNameOfDumpedScript,
					mUseDiffWrapper, mDumpFeatureVector, mFeatureVectorDumpPath, mCompressDumpedScript,
					mAdditionalOptions, mSolverLogger, mUseMinimalUnsatCoreEnumerationForSmtInterpol);
		}

		public SolverSettings setDumpMainTrackBenchmark(final boolean enable) {
			assert !enable || mDumpSmtScriptToFile && mPathOfDumpedScript != null && mBaseNameOfDumpedScript != null;
			return new SolverSettings(mSolverMode, mFakeNonIncrementalScript, mUseExternalSolver,
					mExternalSolverCommand, mSolverLogics, mTimeoutSmtInterpol, mExternalInterpolator,
					mDumpSmtScriptToFile, mDumpUnsatCoreTrackBenchmark, enable, mPathOfDumpedScript,
					mBaseNameOfDumpedScript, mUseDiffWrapper, mDumpFeatureVector, mFeatureVectorDumpPath,
					mCompressDumpedScript, mAdditionalOptions, mSolverLogger,
					mUseMinimalUnsatCoreEnumerationForSmtInterpol);
		}

		public SolverSettings setDumpFeatureVectors(final boolean enabled, final String dumpPath) {
			return new SolverSettings(mSolverMode, mFakeNonIncrementalScript, mUseExternalSolver,
					mExternalSolverCommand, mSolverLogics, mTimeoutSmtInterpol, mExternalInterpolator,
					mDumpSmtScriptToFile, mDumpUnsatCoreTrackBenchmark, mDumpMainTrackBenchmark, mPathOfDumpedScript,
					mBaseNameOfDumpedScript, mUseDiffWrapper, enabled, dumpPath, mCompressDumpedScript,
					mAdditionalOptions, mSolverLogger, mUseMinimalUnsatCoreEnumerationForSmtInterpol);
		}

		/**
		 * Set timeout for SmtInterpol in milliseconds.
		 *
		 * @param timeoutInMsSmtInterpol
		 *            timeout in milliseconds. Must be non-negative or -1 to disable timeout.
		 */
		public SolverSettings setSmtInterpolTimeout(final long timeoutInMsSmtInterpol) {
			if (timeoutInMsSmtInterpol < 0 && timeoutInMsSmtInterpol != -1) {
				throw new IllegalArgumentException(
						"Timeout for SMTInterpol must be non-negative or -1 to disable timeout");
			}
			return new SolverSettings(mSolverMode, mFakeNonIncrementalScript, mUseExternalSolver,
					mExternalSolverCommand, mSolverLogics, timeoutInMsSmtInterpol, mExternalInterpolator,
					mDumpSmtScriptToFile, mDumpUnsatCoreTrackBenchmark, mDumpMainTrackBenchmark, mPathOfDumpedScript,
					mBaseNameOfDumpedScript, mUseDiffWrapper, mDumpFeatureVector, mFeatureVectorDumpPath,
					mCompressDumpedScript, mAdditionalOptions, mSolverLogger,
					mUseMinimalUnsatCoreEnumerationForSmtInterpol);
		}

		public SolverSettings setUseExternalSolver(final boolean enable, final String externalSolverCommand,
				final Logics externalSolverLogics) {
			return new SolverSettings(mSolverMode, mFakeNonIncrementalScript, enable, externalSolverCommand,
					externalSolverLogics, mTimeoutSmtInterpol, mExternalInterpolator, mDumpSmtScriptToFile,
					mDumpUnsatCoreTrackBenchmark, mDumpMainTrackBenchmark, mPathOfDumpedScript, mBaseNameOfDumpedScript,
					mUseDiffWrapper, mDumpFeatureVector, mFeatureVectorDumpPath, mCompressDumpedScript,
					mAdditionalOptions, mSolverLogger, mUseMinimalUnsatCoreEnumerationForSmtInterpol);
		}

		/**
		 * Use an external solver with default command, logic, and no timeout
		 */
		public SolverSettings setUseExternalSolver(final ExternalSolver solver) {
			return setUseExternalSolver(true, solver.getSolverCommand(), solver.getDefaultLogic());
		}

		/**
		 * Use an external solver with default command.
		 *
		 * @param solver
		 *            The external solver.
		 * @param logic
		 *            The logic we should set in the solver or null if we should not set any logic
		 * @param timeout
		 *            A timeout in ms that should be supplied to the solver. Use only non-negative values. Some solvers
		 *            do not support setting a timeout.
		 */
		public SolverSettings setUseExternalSolver(final ExternalSolver solver, final Logics logic,
				final long timeout) {
			return setUseExternalSolver(true, solver.getSolverCommand(timeout), logic);
		}

		/**
		 * Use an external solver with default command and no timeout.
		 *
		 * @param solver
		 *            The external solver.
		 * @param logic
		 *            The logic we should set in the solver or null if we should not set any logic
		 */
		public SolverSettings setUseExternalSolver(final ExternalSolver solver, final Logics logic) {
			return setUseExternalSolver(true, solver.getSolverCommand(), logic);
		}

		/**
		 * Use an external solver with default command and default logic.
		 *
		 * @param solver
		 *            The external solver.
		 * @param timeout
		 *            A non-negative timeout in ms that should be supplied to the solver or -1 if no timeout should be
		 *            used. Some solvers do not support setting a timeout.
		 */
		public SolverSettings setUseExternalSolver(final ExternalSolver solver, final long timeout) {
			return setUseExternalSolver(true, solver.getSolverCommand(timeout), solver.getDefaultLogic());
		}

		public SolverSettings setUseFakeIncrementalScript(final boolean enable) {
			return new SolverSettings(mSolverMode, enable, mUseExternalSolver, mExternalSolverCommand, mSolverLogics,
					mTimeoutSmtInterpol, mExternalInterpolator, mDumpSmtScriptToFile, mDumpUnsatCoreTrackBenchmark,
					mDumpMainTrackBenchmark, mPathOfDumpedScript, mBaseNameOfDumpedScript, mUseDiffWrapper,
					mDumpFeatureVector, mFeatureVectorDumpPath, mCompressDumpedScript, mAdditionalOptions,
					mSolverLogger, mUseMinimalUnsatCoreEnumerationForSmtInterpol);
		}

		public SolverSettings setSolverLogics(final Logics logics) {
			return new SolverSettings(mSolverMode, mFakeNonIncrementalScript, mUseExternalSolver,
					mExternalSolverCommand, logics, mTimeoutSmtInterpol, mExternalInterpolator, mDumpSmtScriptToFile,
					mDumpUnsatCoreTrackBenchmark, mDumpMainTrackBenchmark, mPathOfDumpedScript, mBaseNameOfDumpedScript,
					mUseDiffWrapper, mDumpFeatureVector, mFeatureVectorDumpPath, mCompressDumpedScript,
					mAdditionalOptions, mSolverLogger, mUseMinimalUnsatCoreEnumerationForSmtInterpol);
		}

		public SolverSettings setUseMinimalUnsatCoreEnumerationForSmtInterpol(final boolean enable) {
			return new SolverSettings(mSolverMode, mFakeNonIncrementalScript, mUseExternalSolver,
					mExternalSolverCommand, mSolverLogics, mTimeoutSmtInterpol, mExternalInterpolator,
					mDumpSmtScriptToFile, mDumpUnsatCoreTrackBenchmark, mDumpMainTrackBenchmark, mPathOfDumpedScript,
					mBaseNameOfDumpedScript, mUseDiffWrapper, mDumpFeatureVector, mFeatureVectorDumpPath,
					mCompressDumpedScript, mAdditionalOptions, mSolverLogger, enable);
		}

		/**
		 * Set the {@link SolverMode} of these settings and automatically adjust values for the following fields.
		 * <ul>
		 * <li>{@link #useExternalSolver()}
		 * <li>{@link #useDiffWrapper()}
		 * <li>{@link #getTimeoutSmtInterpol()}
		 * <li>{@link #getExternalInterpolator()}
		 * <li>{@link #getSolverLogics()} (only for {@link SolverMode}s Internal*)
		 * </ul>
		 *
		 * You may change these fields afterwards.
		 *
		 * If you want to explicitly disable {@link SolverMode} (e.g., for usage with
		 * {@link SolverBuilder#buildScript(IUltimateServiceProvider, SolverSettings)}, use null as parameter. Note that
		 * in this case, the values for the fields mentioned above are not changed.
		 */
		public SolverSettings setSolverMode(final SolverMode solverMode) {
			if (solverMode == null) {
				return new SolverSettings(solverMode, mFakeNonIncrementalScript, mUseExternalSolver,
						mExternalSolverCommand, mSolverLogics, mTimeoutSmtInterpol, mExternalInterpolator,
						mDumpSmtScriptToFile, mDumpUnsatCoreTrackBenchmark, mDumpMainTrackBenchmark,
						mPathOfDumpedScript, mBaseNameOfDumpedScript, mUseDiffWrapper, mDumpFeatureVector,
						mFeatureVectorDumpPath, mCompressDumpedScript, mAdditionalOptions, mSolverLogger,
						mUseMinimalUnsatCoreEnumerationForSmtInterpol);
			}

			final boolean useExternalSolver;
			final boolean useDiffWrapper;
			final int timeoutSmtInterpol;
			final ExternalInterpolator externalInterpolator;
			final Logics logics;

			switch (solverMode) {
			case External_DefaultMode:
			case External_ModelsMode:
			case External_ModelsAndUnsatCoreMode:
				useExternalSolver = true;
				timeoutSmtInterpol = -1;
				externalInterpolator = null;
				useDiffWrapper = USE_DIFF_WRAPPER_SCRIPT;
				logics = mSolverLogics;
				break;
			case External_PrincessInterpolationMode:
				useExternalSolver = true;
				timeoutSmtInterpol = -1;
				externalInterpolator = ExternalInterpolator.PRINCESS;
				useDiffWrapper = USE_DIFF_WRAPPER_SCRIPT;
				logics = mSolverLogics;
				break;
			case External_SMTInterpolInterpolationMode:
				useExternalSolver = true;
				timeoutSmtInterpol = -1;
				externalInterpolator = ExternalInterpolator.SMTINTERPOL;
				useDiffWrapper = false;
				logics = mSolverLogics;
				break;
			case External_Z3InterpolationMode:
				useExternalSolver = true;
				timeoutSmtInterpol = -1;
				externalInterpolator = ExternalInterpolator.IZ3;
				useDiffWrapper = USE_DIFF_WRAPPER_SCRIPT;
				logics = mSolverLogics;
				break;
			case External_MathsatInterpolationMode:
				useExternalSolver = true;
				timeoutSmtInterpol = -1;
				externalInterpolator = ExternalInterpolator.MATHSAT;
				useDiffWrapper = USE_DIFF_WRAPPER_SCRIPT;
				logics = mSolverLogics;
				break;
			case Internal_SMTInterpol:
				useExternalSolver = false;
				timeoutSmtInterpol = -1;
				externalInterpolator = null;
				useDiffWrapper = false;
				logics = ExternalSolver.SMTINTERPOL.getDefaultLogic();
				break;
			default:
				throw new AssertionError("unknown solver mode " + solverMode);
			}

			return new SolverSettings(solverMode, mFakeNonIncrementalScript, useExternalSolver, mExternalSolverCommand,
					logics, timeoutSmtInterpol, externalInterpolator, mDumpSmtScriptToFile,
					mDumpUnsatCoreTrackBenchmark, mDumpMainTrackBenchmark, mPathOfDumpedScript, mBaseNameOfDumpedScript,
					useDiffWrapper, mDumpFeatureVector, mFeatureVectorDumpPath, mCompressDumpedScript,
					mAdditionalOptions, mSolverLogger, mUseMinimalUnsatCoreEnumerationForSmtInterpol);
		}

		public SolverSettings setAdditionalOptions(final Map<String, String> additionalOptions) {
			return new SolverSettings(mSolverMode, mFakeNonIncrementalScript, mUseExternalSolver,
					mExternalSolverCommand, mSolverLogics, mTimeoutSmtInterpol, mExternalInterpolator,
					mDumpSmtScriptToFile, mDumpUnsatCoreTrackBenchmark, mDumpMainTrackBenchmark, mPathOfDumpedScript,
					mBaseNameOfDumpedScript, mUseDiffWrapper, mDumpFeatureVector, mFeatureVectorDumpPath,
					mCompressDumpedScript, Objects.requireNonNull(additionalOptions), mSolverLogger,
					mUseMinimalUnsatCoreEnumerationForSmtInterpol);
		}

		public SolverSettings setSolverLogger(final ILogger logger) {
			return new SolverSettings(mSolverMode, mFakeNonIncrementalScript, mUseExternalSolver,
					mExternalSolverCommand, mSolverLogics, mTimeoutSmtInterpol, mExternalInterpolator,
					mDumpSmtScriptToFile, mDumpUnsatCoreTrackBenchmark, mDumpMainTrackBenchmark, mPathOfDumpedScript,
					mBaseNameOfDumpedScript, mUseDiffWrapper, mDumpFeatureVector, mFeatureVectorDumpPath,
					mCompressDumpedScript, mAdditionalOptions, logger, mUseMinimalUnsatCoreEnumerationForSmtInterpol);
		}

		@Override
		public String toString() {
			return ReflectionUtil.instanceFieldsToString(this);
		}

	}

	private static final class SelfDestructingSolverStorable extends WrapperScript implements IStorable {

		private static int sCounter = 0;
		private final int mId;
		private IToolchainStorage mStorage;

		protected SelfDestructingSolverStorable(final Script wrappedScript, final IToolchainStorage storage) {
			super(wrappedScript);
			mId = sCounter++;
			mStorage = storage;
			mStorage.putStorable(getKey(), this);
		}

		@Override
		public void destroy() {
			if (mStorage != null) {
				super.exit();
				removeFromStorage();
			}
		}

		@Override
		public void exit() {
			super.exit();
			removeFromStorage();
		}

		private void removeFromStorage() {
			if (mStorage != null) {
				mStorage.removeStorable(getKey());
				mStorage = null;
			}
		}

		private String getKey() {
			return getClass().getSimpleName() + mId;
		}
	}

	/**
	 * Enumeration that provides default command line strings for SMT solvers in different modes as well as their
	 * default logics and -- if available -- commands for setting a timeout.
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	public enum ExternalSolver {
		Z3("z3 -smt2 -in SMTLIB2_COMPLIANT=true", "z3 -smt2 -in SMTLIB2_COMPLIANT=true" + " -t:%d", Logics.ALL),

		CVC4("cvc4 --incremental --print-success --lang smt",
				"cvc4 --incremental --print-success --lang smt" + " --tlimit-per=%d", Logics.ALL),

		CVC5("cvc5 --incremental --print-success --lang smt",
				"cvc5 --incremental --print-success --lang smt" + " --tlimit-per=%d", Logics.ALL),

		MATHSAT("mathsat -theory.fp.to_bv_overflow_mode=1 -theory.fp.minmax_zero_mode=4 -theory.bv.div_by_zero_mode=1 -unsat_core_generation=3",
				null, Logics.ALL),

		MATHSAT_INTERPOLATION(
				"mathsat -theory.fp.to_bv_overflow_mode=1 -theory.fp.minmax_zero_mode=4 -theory.bv.div_by_zero_mode=1 -theory.bv.eager=false -theory.fp.enabled=false",
				null, Logics.ALL),

		SMTINTERPOL(null, null, Logics.ALL),

		PRINCESS(null, null, null);

		private final String mSolverCommand;
		private final String mSolverCommandTimeoutFormatString;
		private final Logics mDefaultLogic;

		ExternalSolver(final String solverCommand, final String solverCommandTimeoutFormatString,
				final Logics defaultLogic) {
			mSolverCommand = solverCommand;
			mSolverCommandTimeoutFormatString = solverCommandTimeoutFormatString;
			mDefaultLogic = defaultLogic;
		}

		public String getSolverCommand() {
			if (mSolverCommand == null) {
				throw new UnsupportedOperationException("Unknown or not implemented solver command: " + this);
			}
			return mSolverCommand;
		}

		public String getSolverCommand(final long timeout) {
			if (timeout == -1) {
				return getSolverCommand();
			}
			if (timeout < 0) {
				throw new IllegalArgumentException("Timeout must be non-negative");
			}
			if (mSolverCommandTimeoutFormatString == null) {
				throw new UnsupportedOperationException(
						"Unknown or not implemented solver command with timeouts: " + this);
			}
			return String.format(mSolverCommandTimeoutFormatString, timeout);
		}

		public Logics getDefaultLogic() {
			return mDefaultLogic;
		}
	}
}
