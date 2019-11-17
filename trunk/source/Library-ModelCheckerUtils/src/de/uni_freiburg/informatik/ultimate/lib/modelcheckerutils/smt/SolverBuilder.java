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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.math.BigDecimal;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.DiffWrapperScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.HistoryRecordingScript;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.TerminationRequest;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.NonIncrementalScriptor;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.Scriptor;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.ScriptorWithGetInterpolants;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.ScriptorWithGetInterpolants.ExternalInterpolator;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.SmtInterpolLogProxyWrapper;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

/**
 * Wrapper that constructs SMTInterpol or an external solver.
 *
 * @author heizmann@informatik.uni-freiburg.de
 * @author dietsch@informatik.uni-freiburg.de,
 */
public class SolverBuilder {

	public enum SolverMode {
		Internal_SMTInterpol,

		Internal_SMTInterpol_NoArrayInterpol,

		External_PrincessInterpolationMode,

		External_SMTInterpolInterpolationMode,

		External_Z3InterpolationMode,

		External_ModelsAndUnsatCoreMode,

		External_ModelsMode,

		External_DefaultMode,
	}

	public static final String COMMAND_Z3_NO_TIMEOUT = "z3 -smt2 -in SMTLIB2_COMPLIANT=true";
	public static final String COMMAND_Z3_TIMEOUT = COMMAND_Z3_NO_TIMEOUT + " -t:12000";

	public static final String COMMAND_CVC4_NO_TIMEOUT = "cvc4 --incremental --print-success --lang smt --rewrite-divk";
	public static final String COMMAND_CVC4_TIMEOUT = COMMAND_CVC4_NO_TIMEOUT + " --tlimit-per=12000";

	// 20161214 Matthias: MathSAT does not support timeouts
	public static final String COMMAND_MATHSAT = "mathsat -unsat_core_generation=3";
	public static final long TIMEOUT_SMTINTERPOL = 12_000L;
	public static final long TIMEOUT_NONE_SMTINTERPOL = 0L;
	public static final Logics LOGIC_Z3 = Logics.ALL;
	public static final Logics LOGIC_CVC4_DEFAULT = Logics.AUFLIRA;
	public static final Logics LOGIC_CVC4_BITVECTORS = Logics.ALL;
	public static final Logics LOGIC_MATHSAT = Logics.ALL;
	public static final Logics LOGIC_SMTINTERPOL = Logics.QF_AUFLIRA;

	public static final boolean USE_DIFF_WRAPPER_SCRIPT = true;

	private static final String SOLVER_LOGGER_NAME = "SolverLogger";
	private static final boolean USE_WRAPPER_SCRIPT_WITH_TERM_CONSTRUCTION_CHECKS = false;

	private static Script wrapScriptWithLoggingScript(final Script script, final ILogger solverLogger,
			final String fullPathOfDumpedFile) {
		final Script wrappedScript;
		try {
			wrappedScript = new LoggingScript(script, fullPathOfDumpedFile, true);
			solverLogger.info("Dumping SMT script to " + fullPathOfDumpedFile);
		} catch (final FileNotFoundException e) {
			solverLogger.error("Unable dump SMT script to " + fullPathOfDumpedFile);
			throw new RuntimeException(e);
		}
		return wrappedScript;
	}

	public static ILogger getSolverLogger(final IUltimateServiceProvider services) {
		return services.getLoggingService().getLoggerForExternalTool(SOLVER_LOGGER_NAME);
	}

	/**
	 * Create simple {@link SolverSettings} instance that can be used to start SMTInterpol.
	 */
	public static SolverSettings constructSolverSettings() throws AssertionError {
		return new SolverSettings(SolverMode.Internal_SMTInterpol, false, false, null, null, -1, null, false, false,
				false, null, null, false, false, null);
	}

	/**
	 * Build an SMT solver.
	 *
	 * @return A Script that represents an SMT solver which is defined by settings.
	 */
	public static Script buildScript(final IUltimateServiceProvider services, final SolverSettings settings) {
		final ILogger solverLogger = getSolverLogger(services);
		Script script;
		if (settings.useExternalSolver()) {
			assert settings.getSolverMode() == null
					|| settings.getSolverMode() != SolverMode.Internal_SMTInterpol && settings
							.getSolverMode() != SolverMode.Internal_SMTInterpol_NoArrayInterpol : "You set solver mode to Internal* and enabled useExternalSolver";
			final String command = settings.getCommandExternalSolver();
			solverLogger.info("constructing external solver with command" + settings.getCommandExternalSolver());
			try {
				final ExternalInterpolator externalInterpolator = settings.getExternalInterpolator();
				if (externalInterpolator == null) {
					if (settings.fakeNonIncrementalScript()) {
						script = new NonIncrementalScriptor(command, solverLogger, services,
								"External_FakeNonIncremental", settings.dumpSmtScriptToFile(),
								settings.getPathOfDumpedScript(), settings.getBaseNameOfDumpedScript());
					} else {
						script = new Scriptor(command, solverLogger, services, "External");
					}
				} else {
					solverLogger.info("external solver will use " + externalInterpolator + " interpolation mode");
					script = new ScriptorWithGetInterpolants(command, solverLogger, services, externalInterpolator,
							"ExternalInterpolator");
				}
				if (settings.useDiffWrapper()) {
					script = new DiffWrapperScript(script);
				}
			} catch (final IOException e) {
				solverLogger.fatal("Unable to construct solver");
				throw new RuntimeException(e);
			}
		} else {
			solverLogger.info("constructing new instance of SMTInterpol");
			final LogProxy loggerWrapper = new SmtInterpolLogProxyWrapper(solverLogger);
			final TerminationRequest termRequest =
					new SMTInterpolTerminationRequest(services.getProgressMonitorService());
			script = new SMTInterpol(loggerWrapper, termRequest);
		}
		if (settings.dumpSmtScriptToFile()) {
			script = wrapScriptWithLoggingScript(script, solverLogger, settings.constructFullPathOfDumpedScript());
		}
		if (!settings.useExternalSolver()) {
			script.setOption(":timeout", settings.getTimeoutSmtInterpol());
		}
		if (USE_WRAPPER_SCRIPT_WITH_TERM_CONSTRUCTION_CHECKS) {
			script = new ScriptWithTermConstructionChecks(script);
		}
		if (settings.dumpFeatureExtractionVector()) {
			script = new SMTFeatureExtractorScript(script, getSolverLogger(services),
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

	public static Script buildAndInitializeSolver(final IUltimateServiceProvider services,
			final SolverSettings solverSettings, final String solverId) throws AssertionError {

		if (solverSettings.getSolverMode() == null) {
			throw new IllegalArgumentException(
					"You cannot initialize a solver without specifying the solver mode in the solver settings instance");
		}

		final Script script = SolverBuilder.buildScript(services, solverSettings);
		final Logics logicForExternalSolver = solverSettings.getExternalSolverLogics();

		switch (solverSettings.getSolverMode()) {
		case External_DefaultMode:
			if (logicForExternalSolver != null) {
				script.setLogic(logicForExternalSolver);
			}
			break;
		case External_ModelsMode:
			script.setOption(":produce-models", true);
			if (logicForExternalSolver != null) {
				script.setLogic(logicForExternalSolver);
			}
			break;
		case External_ModelsAndUnsatCoreMode:
			script.setOption(":produce-models", true);
			script.setOption(":produce-unsat-cores", true);
			if (logicForExternalSolver != null) {
				script.setLogic(logicForExternalSolver);
			}
			break;
		case External_PrincessInterpolationMode:
			script.setOption(":produce-models", true);
			script.setOption(":produce-interpolants", true);
			script.setLogic(logicForExternalSolver);
			break;
		case External_SMTInterpolInterpolationMode:
			script.setOption(":produce-models", true);
			script.setOption(":produce-interpolants", true);
			script.setOption(":array-interpolation", true);
			script.setLogic(logicForExternalSolver);
			break;
		case External_Z3InterpolationMode:
			script.setOption(":produce-models", true);
			script.setOption(":produce-interpolants", true);
			script.setLogic(logicForExternalSolver);
			final Sort indexSort;
			if (logicForExternalSolver.isArray()) {
				// add array-ext function
				indexSort = SmtSortUtils.getIntSort(script);
				final Sort intSort = SmtSortUtils.getIntSort(script);
				final Sort intArraySort = SmtSortUtils.getArraySort(script, indexSort, intSort);
				script.declareFun("array-ext", new Sort[] { intArraySort, intArraySort }, indexSort);
			} else if (logicForExternalSolver.isBitVector()) {
				// do nothing. several have to be added here
			}
			break;
		case Internal_SMTInterpol:
			script.setOption(":produce-models", true);
			script.setOption(":produce-unsat-cores", true);
			script.setOption(":produce-interpolants", true);
			script.setOption(":interpolant-check-mode", true);
			script.setOption(":proof-transformation", "LU");
			script.setOption(":array-interpolation", true);
			// mScript.setOption(":proof-transformation", "RPI");
			// mScript.setOption(":proof-transformation", "LURPI");
			// mScript.setOption(":proof-transformation", "RPILU");
			// mScript.setOption(":verbosity", 0);
			script.setLogic(LOGIC_SMTINTERPOL.toString());
			break;
		case Internal_SMTInterpol_NoArrayInterpol:
			script.setOption(":produce-models", true);
			script.setOption(":produce-unsat-cores", true);
			script.setOption(":produce-interpolants", true);
			script.setOption(":interpolant-check-mode", true);
			script.setOption(":proof-transformation", "LU");
			script.setOption(":array-interpolation", false);
			// mScript.setOption(":proof-transformation", "RPI");
			// mScript.setOption(":proof-transformation", "LURPI");
			// mScript.setOption(":proof-transformation", "RPILU");
			// mScript.setOption(":verbosity", 0);
			script.setLogic(LOGIC_SMTINTERPOL.toString());
			break;
		default:
			throw new AssertionError("unknown solver");
		}

		final String advertising = "SMT script generated on " + CoreUtil.getIsoUtcTimestamp()
				+ " by Ultimate (https://ultimate.informatik.uni-freiburg.de/)";

		script.setInfo(":source", advertising);
		script.setInfo(":smt-lib-version", new BigDecimal("2.5"));
		script.setInfo(":category", new QuotedObject("industrial"));
		script.setInfo(":ultimate-id", solverId);
		return script;
	}

	private static final class SMTInterpolTerminationRequest implements TerminationRequest {
		private final IProgressMonitorService mMonitor;

		SMTInterpolTerminationRequest(final IProgressMonitorService monitor) {
			mMonitor = monitor;
		}

		@Override
		public boolean isTerminationRequested() {
			return !mMonitor.continueProcessingRoot();
		}
	}

	/**
	 * Settings that define how a solver is build.
	 */
	public static final class SolverSettings {

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

		private final Logics mExternalSolverLogics;

		private SolverSettings(final SolverMode solverMode, final boolean fakeNonIncrementalScript,
				final boolean useExternalSolver, final String commandExternalSolver, final Logics externalSolverLogic,
				final long timeoutSmtInterpol, final ExternalInterpolator externalInterpolator,
				final boolean dumpSmtScriptToFile, final boolean dumpUnsatCoreTrackBenchmark,
				final boolean dumpMainTrackBenchmark, final String pathOfDumpedScript,
				final String baseNameOfDumpedScript, final boolean useDiffWrapper, final boolean dumpFeatureVector,
				final String featureVectorDumpPath) {
			mSolverMode = solverMode;
			mFakeNonIncrementalScript = fakeNonIncrementalScript;
			mUseExternalSolver = useExternalSolver;
			mExternalSolverCommand = commandExternalSolver;
			mExternalSolverLogics = externalSolverLogic;
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

		}

		public boolean fakeNonIncrementalScript() {
			return mFakeNonIncrementalScript;
		}

		public boolean useExternalSolver() {
			return mUseExternalSolver;
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

		public Logics getExternalSolverLogics() {
			return mExternalSolverLogics;
		}

		public boolean dumpSmtScriptToFile() {
			return mDumpSmtScriptToFile;
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

		public boolean dumpFeatureExtractionVector() {
			return mDumpFeatureVector;
		}

		public String getFeatureVectorDumpPath() {
			return mFeatureVectorDumpPath;
		}

		public SolverMode getSolverMode() {
			return mSolverMode;
		}

		public String constructFullPathOfDumpedScript() {
			String result = getPathOfDumpedScript();
			result = addFileSeparator(result);
			result += getBaseNameOfDumpedScript() + ".smt2";
			return result;
		}

		public SolverSettings setDumpSmtScriptToFile(final boolean enabled, final String folderPathOfDumpedFile,
				final String basenameOfDumpedFile) {
			return new SolverSettings(mSolverMode, mFakeNonIncrementalScript, mUseExternalSolver,
					mExternalSolverCommand, mExternalSolverLogics, mTimeoutSmtInterpol, mExternalInterpolator, enabled,
					mDumpUnsatCoreTrackBenchmark, mDumpMainTrackBenchmark, folderPathOfDumpedFile, basenameOfDumpedFile,
					mUseDiffWrapper, mDumpFeatureVector, mFeatureVectorDumpPath);
		}

		public SolverSettings setDumpUnsatCoreTrackBenchmark(final boolean enable) {
			assert !enable || mDumpSmtScriptToFile && mPathOfDumpedScript != null && mBaseNameOfDumpedScript != null;
			return new SolverSettings(mSolverMode, mFakeNonIncrementalScript, mUseExternalSolver,
					mExternalSolverCommand, mExternalSolverLogics, mTimeoutSmtInterpol, mExternalInterpolator,
					mDumpSmtScriptToFile, enable, mDumpMainTrackBenchmark, mPathOfDumpedScript, mBaseNameOfDumpedScript,
					mUseDiffWrapper, mDumpFeatureVector, mFeatureVectorDumpPath);
		}

		public SolverSettings setDumpMainTrackBenchmark(final boolean enable) {
			assert !enable || mDumpSmtScriptToFile && mPathOfDumpedScript != null && mBaseNameOfDumpedScript != null;
			return new SolverSettings(mSolverMode, mFakeNonIncrementalScript, mUseExternalSolver,
					mExternalSolverCommand, mExternalSolverLogics, mTimeoutSmtInterpol, mExternalInterpolator,
					mDumpSmtScriptToFile, mDumpUnsatCoreTrackBenchmark, enable, mPathOfDumpedScript,
					mBaseNameOfDumpedScript, mUseDiffWrapper, mDumpFeatureVector, mFeatureVectorDumpPath);
		}

		public SolverSettings setDumpFeatureVectors(final boolean enabled, final String dumpPath) {
			return new SolverSettings(mSolverMode, mFakeNonIncrementalScript, mUseExternalSolver,
					mExternalSolverCommand, mExternalSolverLogics, mTimeoutSmtInterpol, mExternalInterpolator,
					mDumpSmtScriptToFile, mDumpUnsatCoreTrackBenchmark, mDumpMainTrackBenchmark, mPathOfDumpedScript,
					mBaseNameOfDumpedScript, mUseDiffWrapper, enabled, dumpPath);
		}

		public SolverSettings setSmtInterpolTimeout(final long timeoutSmtInterpol) {
			return new SolverSettings(mSolverMode, mFakeNonIncrementalScript, mUseExternalSolver,
					mExternalSolverCommand, mExternalSolverLogics, timeoutSmtInterpol, mExternalInterpolator,
					mDumpSmtScriptToFile, mDumpUnsatCoreTrackBenchmark, mDumpMainTrackBenchmark, mPathOfDumpedScript,
					mBaseNameOfDumpedScript, mUseDiffWrapper, mDumpFeatureVector, mFeatureVectorDumpPath);
		}

		public SolverSettings setUseExternalSolver(final boolean enable, final String externalSolverCommand,
				final Logics externalSolverLogics) {
			return new SolverSettings(mSolverMode, mFakeNonIncrementalScript, enable, externalSolverCommand,
					externalSolverLogics, mTimeoutSmtInterpol, mExternalInterpolator, mDumpSmtScriptToFile,
					mDumpUnsatCoreTrackBenchmark, mDumpMainTrackBenchmark, mPathOfDumpedScript, mBaseNameOfDumpedScript,
					mUseDiffWrapper, mDumpFeatureVector, mFeatureVectorDumpPath);
		}

		public SolverSettings setUseFakeIncrementalScript(final boolean enable) {
			return new SolverSettings(mSolverMode, enable, mUseExternalSolver, mExternalSolverCommand,
					mExternalSolverLogics, mTimeoutSmtInterpol, mExternalInterpolator, mDumpSmtScriptToFile,
					mDumpUnsatCoreTrackBenchmark, mDumpMainTrackBenchmark, mPathOfDumpedScript, mBaseNameOfDumpedScript,
					mUseDiffWrapper, mDumpFeatureVector, mFeatureVectorDumpPath);
		}

		public SolverSettings setExternalSolverLogics(final Logics logics) {
			return new SolverSettings(mSolverMode, mFakeNonIncrementalScript, mUseExternalSolver,
					mExternalSolverCommand, logics, mTimeoutSmtInterpol, mExternalInterpolator, mDumpSmtScriptToFile,
					mDumpUnsatCoreTrackBenchmark, mDumpMainTrackBenchmark, mPathOfDumpedScript, mBaseNameOfDumpedScript,
					mUseDiffWrapper, mDumpFeatureVector, mFeatureVectorDumpPath);
		}

		/**
		 * Set the {@link SolverMode} of these settings and automatically adjust values for
		 * {@link #useExternalSolver()}, {@link #useDiffWrapper()}, {@link #getTimeoutSmtInterpol()}, and
		 * {@link #getExternalInterpolator()}.
		 *
		 * You may change these fields afterwards.
		 *
		 * If you want to explicitly disable {@link SolverMode} (e.g., for usage with
		 * {@link SolverBuilder#buildScript(IUltimateServiceProvider, SolverSettings)}, use null as parameter. Note that
		 * in this case, the values for the four fields mentioned above are not changed.
		 */
		public SolverSettings setSolverMode(final SolverMode solverMode) {
			if (solverMode == null) {
				return new SolverSettings(solverMode, mFakeNonIncrementalScript, mUseExternalSolver,
						mExternalSolverCommand, mExternalSolverLogics, mTimeoutSmtInterpol, mExternalInterpolator,
						mDumpSmtScriptToFile, mDumpUnsatCoreTrackBenchmark, mDumpMainTrackBenchmark,
						mPathOfDumpedScript, mBaseNameOfDumpedScript, mUseDiffWrapper, mDumpFeatureVector,
						mFeatureVectorDumpPath);
			}

			final boolean useExternalSolver;
			final boolean useDiffWrapper;
			final int timeoutSmtInterpol;
			final ExternalInterpolator externalInterpolator;

			switch (solverMode) {
			case External_DefaultMode:
			case External_ModelsMode:
			case External_ModelsAndUnsatCoreMode:
				useExternalSolver = true;
				timeoutSmtInterpol = -1;
				externalInterpolator = null;
				useDiffWrapper = USE_DIFF_WRAPPER_SCRIPT;
				break;
			case External_PrincessInterpolationMode:
				useExternalSolver = true;
				timeoutSmtInterpol = -1;
				externalInterpolator = ExternalInterpolator.PRINCESS;
				useDiffWrapper = USE_DIFF_WRAPPER_SCRIPT;
				break;
			case External_SMTInterpolInterpolationMode:
				useExternalSolver = true;
				timeoutSmtInterpol = -1;
				externalInterpolator = ExternalInterpolator.SMTINTERPOL;
				useDiffWrapper = false;
				break;
			case External_Z3InterpolationMode:
				useExternalSolver = true;
				timeoutSmtInterpol = -1;
				externalInterpolator = ExternalInterpolator.IZ3;
				useDiffWrapper = USE_DIFF_WRAPPER_SCRIPT;
				break;
			case Internal_SMTInterpol_NoArrayInterpol:
			case Internal_SMTInterpol:
				useExternalSolver = false;
				timeoutSmtInterpol = -1;
				externalInterpolator = null;
				useDiffWrapper = false;
				break;
			default:
				throw new AssertionError("unknown solver mode " + solverMode);
			}

			return new SolverSettings(solverMode, mFakeNonIncrementalScript, useExternalSolver, mExternalSolverCommand,
					mExternalSolverLogics, timeoutSmtInterpol, externalInterpolator, mDumpSmtScriptToFile,
					mDumpUnsatCoreTrackBenchmark, mDumpMainTrackBenchmark, mPathOfDumpedScript, mBaseNameOfDumpedScript,
					useDiffWrapper, mDumpFeatureVector, mFeatureVectorDumpPath);
		}

		/**
		 * Add file separator if last symbol is not already file separator.
		 */
		private static String addFileSeparator(final String string) {
			if (string.endsWith(System.getProperty("file.separator"))) {
				return string;
			}
			return string + System.getProperty("file.separator");

		}

	}

}
