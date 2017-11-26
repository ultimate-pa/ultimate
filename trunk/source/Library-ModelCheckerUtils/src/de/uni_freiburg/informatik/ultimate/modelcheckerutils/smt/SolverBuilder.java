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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.math.BigDecimal;
import java.text.SimpleDateFormat;
import java.util.Date;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IStorable;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.DiffWrapperScript;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.TerminationRequest;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.NonIncrementalScriptor;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.Scriptor;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.ScriptorWithGetInterpolants;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.ScriptorWithGetInterpolants.ExternalInterpolator;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.SmtInterpolLogProxyWrapper;

/**
 * Wrapper that constructs SMTInterpol or an external solver.
 *
 * @author heizmann@informatik.uni-freiburg.de
 * @author dietsch@informatik.uni-freiburg.de,
 */
public class SolverBuilder {

	public enum SolverMode {
		Internal_SMTInterpol,

		External_PrincessInterpolationMode,

		External_SMTInterpolInterpolationMode,

		External_Z3InterpolationMode,

		External_ModelsAndUnsatCoreMode,

		External_ModelsMode,

		External_DefaultMode,
	}

	private static final String SOLVER_LOGGER_NAME = "SolverLogger";
	private static final boolean USE_WRAPPER_SCRIPT_WITH_TERM_CONSTRUCTION_CHECKS = false;
	public static final boolean USE_DIFF_WRAPPER_SCRIPT = true;

	private static Script createSMTInterpol(final IUltimateServiceProvider services, final IToolchainStorage storage) {
		final ILogger solverLogger = services.getLoggingService().getLoggerForExternalTool(SOLVER_LOGGER_NAME);
		final LogProxy loggerWrapper = new SmtInterpolLogProxyWrapper(solverLogger);
		final TerminationRequest termRequest = new SMTInterpolTerminationRequest(services.getProgressMonitorService());
		return new SMTInterpol(loggerWrapper, termRequest);
	}

	private static Script createExternalSolver(final IUltimateServiceProvider services, final IToolchainStorage storage,
			final String command, final boolean fakeNonIncrementalScript, final boolean dumpFakeNonIncrementalScript,
			final String pathOfDumpedFakeNonIncrementalScript, final String basenameOfDumpedFakeNonIcrementalScript,
			final boolean useDiffWrapper) throws IOException {
		final ILogger solverLogger = services.getLoggingService().getLoggerForExternalTool(SOLVER_LOGGER_NAME);
		Script script;
		if (fakeNonIncrementalScript) {
			script = new NonIncrementalScriptor(command, solverLogger, services, storage, "External_FakeNonIncremental",
					dumpFakeNonIncrementalScript, pathOfDumpedFakeNonIncrementalScript,
					basenameOfDumpedFakeNonIcrementalScript);
		} else {
			script = new Scriptor(command, solverLogger, services, storage, "External");
		}
		if (useDiffWrapper) {
			script = new DiffWrapperScript(script);
		}
		return script;
	}

	private static Script createExternalSolverWithInterpolation(final IUltimateServiceProvider services,
			final IToolchainStorage storage, final String command, final ExternalInterpolator externalInterpolator,
			final boolean useDiffWrapper) throws IOException {
		final ILogger solverLogger = services.getLoggingService().getLoggerForExternalTool(SOLVER_LOGGER_NAME);
		Script script = new ScriptorWithGetInterpolants(command, solverLogger, services, storage, externalInterpolator,
				"ExternalInterpolator");
		if (useDiffWrapper) {
			script = new DiffWrapperScript(script);
		}
		return script;
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
	 * Build an SMT solver.
	 *
	 * @return A Script that represents an SMT solver which is defined by settings.
	 */
	public static Script buildScript(final IUltimateServiceProvider services, final IToolchainStorage storage,
			final Settings settings) {
		final ILogger solverLogger = services.getLoggingService().getLoggerForExternalTool(SOLVER_LOGGER_NAME);
		Script result;
		if (settings.useExternalSolver()) {
			solverLogger.info("constructing external solver with command" + settings.getCommandExternalSolver());
			try {
				if (settings.getExternalInterpolator() == null) {
					result = createExternalSolver(services, storage, settings.getCommandExternalSolver(),
							settings.fakeNonIncrementalScript(), settings.dumpSmtScriptToFile(),
							settings.getPathOfDumpedScript(), settings.getBaseNameOfDumpedScript(),
							settings.getUseDiffWrapper());
				} else {
					solverLogger.info(
							"external solver will use " + settings.getExternalInterpolator() + " interpolation mode");
					result = createExternalSolverWithInterpolation(services, storage,
							settings.getCommandExternalSolver(), settings.getExternalInterpolator(),
							settings.getUseDiffWrapper());
				}
			} catch (final IOException e) {
				solverLogger.fatal("Unable to construct solver");
				throw new RuntimeException(e);
			}
		} else {
			solverLogger.info("constructing new instance of SMTInterpol");
			result = createSMTInterpol(services, storage);
		}
		if (settings.dumpSmtScriptToFile()) {
			try {
				result = new LoggingScript(result, settings.constructFullPathOfDumpedScript(), true);
				solverLogger.info("Dumping SMT script to " + settings.constructFullPathOfDumpedScript());
			} catch (final FileNotFoundException e) {
				solverLogger.error("Unable dump SMT script to " + settings.constructFullPathOfDumpedScript());
				throw new RuntimeException(e);
			}
		}
		if (!settings.useExternalSolver()) {
			result.setOption(":timeout", String.valueOf(settings.getTimeoutSmtInterpol()));
		}
		if (USE_WRAPPER_SCRIPT_WITH_TERM_CONSTRUCTION_CHECKS) {
			result = new ScriptWithTermConstructionChecks(result);
		}
		return result;
	}

	/**
	 * Settings that define how a solver is build.
	 */
	public static class Settings {

		public Settings(final boolean fakeNonIncrementalScript, final boolean useExternalSolver,
				final String commandExternalSolver, final long timeoutSmtInterpol,
				final ExternalInterpolator externalInterpolator, final boolean dumpSmtScriptToFile,
				final String pathOfDumpedScript, final String baseNameOfDumpedScript) {
			this(fakeNonIncrementalScript, useExternalSolver, commandExternalSolver, timeoutSmtInterpol,
					externalInterpolator, dumpSmtScriptToFile, pathOfDumpedScript, baseNameOfDumpedScript, false);
		}

		public Settings(final boolean fakeNonIncrementalScript, final boolean useExternalSolver,
				final String commandExternalSolver, final long timeoutSmtInterpol,
				final ExternalInterpolator externalInterpolator, final boolean dumpSmtScriptToFile,
				final String pathOfDumpedScript, final String baseNameOfDumpedScript, final boolean useDiffWrapper) {
			super();
			mFakeNonIncrementalScript = fakeNonIncrementalScript;
			mUseExternalSolver = useExternalSolver;
			mCommandExternalSolver = commandExternalSolver;
			mTimeoutSmtInterpol = timeoutSmtInterpol;
			mExternalInterpolator = externalInterpolator;
			mDumpSmtScriptToFile = dumpSmtScriptToFile;
			mPathOfDumpedScript = pathOfDumpedScript;
			mBaseNameOfDumpedScript = baseNameOfDumpedScript;
			mUseDiffWrapper = useDiffWrapper;
		}

		/**
		 * Emulate incremental script (push/pop) using reset and re-asserting all terms and re-declaring all sorts and
		 * functions.
		 */
		private final boolean mFakeNonIncrementalScript;

		private final boolean mUseExternalSolver;

		/**
		 * What shell command should be used to call the external smt solver?
		 */
		private final String mCommandExternalSolver;

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

		public boolean fakeNonIncrementalScript() {
			return mFakeNonIncrementalScript;
		}

		public boolean useExternalSolver() {
			return mUseExternalSolver;
		}

		public String getCommandExternalSolver() {
			return mCommandExternalSolver;
		}

		public long getTimeoutSmtInterpol() {
			return mTimeoutSmtInterpol;
		}

		public ExternalInterpolator getExternalInterpolator() {
			return mExternalInterpolator;
		}

		public boolean dumpSmtScriptToFile() {
			return mDumpSmtScriptToFile;
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
		public boolean getUseDiffWrapper() {
			return mUseDiffWrapper;
		}

		public String constructFullPathOfDumpedScript() {
			String result = getPathOfDumpedScript();
			result = addFileSeparator(result);
			result += getBaseNameOfDumpedScript() + ".smt2";
			return result;
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

	public static Settings constructSolverSettings(final String filename, final SolverMode solverMode,
			final boolean fakeNonIncrementalScript, final String commandExternalSolver,
			final boolean dumpSmtScriptToFile, final String pathOfDumpedScript) throws AssertionError {
		final boolean useExternalSolver;
		boolean useDiffWrapper = false;

		final int timeoutSmtInterpol;
		final ExternalInterpolator externalInterpolator;
		switch (solverMode) {
		case External_DefaultMode:
		case External_ModelsMode:
		case External_ModelsAndUnsatCoreMode: {
			useExternalSolver = true;
			timeoutSmtInterpol = -1;
			externalInterpolator = null;
			useDiffWrapper = USE_DIFF_WRAPPER_SCRIPT;
		}
			break;
		case External_PrincessInterpolationMode: {
			useExternalSolver = true;
			timeoutSmtInterpol = -1;
			externalInterpolator = ExternalInterpolator.PRINCESS;
			useDiffWrapper = USE_DIFF_WRAPPER_SCRIPT;
		}
			break;
		case External_SMTInterpolInterpolationMode: {
			useExternalSolver = true;
			timeoutSmtInterpol = -1;
			externalInterpolator = ExternalInterpolator.SMTINTERPOL;
		}
			break;
		case External_Z3InterpolationMode: {
			useExternalSolver = true;
			timeoutSmtInterpol = -1;
			externalInterpolator = ExternalInterpolator.IZ3;
			useDiffWrapper = USE_DIFF_WRAPPER_SCRIPT;
		}
			break;
		case Internal_SMTInterpol: {
			useExternalSolver = false;
			timeoutSmtInterpol = 900 * 1000;
			externalInterpolator = null;
		}
			break;
		default:
			throw new AssertionError("unknown solver mode");
		}
		final Settings solverSettings =
				new Settings(fakeNonIncrementalScript, useExternalSolver, commandExternalSolver, timeoutSmtInterpol,
						externalInterpolator, dumpSmtScriptToFile, pathOfDumpedScript, filename, useDiffWrapper);
		return solverSettings;
	}

	public static Script buildAndInitializeSolver(final IUltimateServiceProvider services,
			final IToolchainStorage storage, final SolverMode solverMode, final Settings solverSettings,
			final boolean dumpUsatCoreTrackBenchmark, final boolean dumpMainTrackBenchmark,
			final String logicForExternalSolver, final String solverId) throws AssertionError {

		Script script = SolverBuilder.buildScript(services, storage, solverSettings);
		if (dumpUsatCoreTrackBenchmark) {
			script = new LoggingScriptForUnsatCoreBenchmarks(script, solverSettings.getBaseNameOfDumpedScript(),
					solverSettings.getPathOfDumpedScript());
		}
		if (dumpMainTrackBenchmark) {
			script = new LoggingScriptForMainTrackBenchmarks(script, solverSettings.getBaseNameOfDumpedScript(),
					solverSettings.getPathOfDumpedScript());
		}
		final Script result = script;

		switch (solverMode) {
		case External_DefaultMode:
			if (logicForExternalSolver != null) {
				result.setLogic(logicForExternalSolver);
			}
			break;
		case External_ModelsMode:
			result.setOption(":produce-models", true);
			if (logicForExternalSolver != null) {
				result.setLogic(logicForExternalSolver);
			}
			break;
		case External_ModelsAndUnsatCoreMode:
			result.setOption(":produce-models", true);
			result.setOption(":produce-unsat-cores", true);
			if (logicForExternalSolver != null) {
				result.setLogic(logicForExternalSolver);
			}
			break;
		case External_PrincessInterpolationMode:
		case External_SMTInterpolInterpolationMode:
			result.setOption(":produce-models", true);
			result.setOption(":produce-interpolants", true);
			result.setLogic(logicForExternalSolver);
			break;
		case External_Z3InterpolationMode:
			result.setOption(":produce-models", true);
			result.setOption(":produce-interpolants", true);
			result.setLogic(logicForExternalSolver);
			// add array-ext function
			final Sort indexSort;
			if (logicForExternalSolver.endsWith("A")) {
				indexSort = SmtSortUtils.getIntSort(result);
				// Sort boolSort = SmtSortUtils.getBoolSort(result);
				// Sort boolArraySort = SmtSortUtils.getArraySort(result, indexSort, boolSort);
				// result.declareFun("array-ext", new Sort[] { boolArraySort, boolArraySort }, indexSort);
				final Sort intSort = SmtSortUtils.getIntSort(result);
				final Sort intArraySort = SmtSortUtils.getArraySort(result, indexSort, intSort);
				result.declareFun("array-ext", new Sort[] { intArraySort, intArraySort }, indexSort);
			} else if (logicForExternalSolver.endsWith("BV")) {
				// do nothing. several have to be added here
			}
			break;
		case Internal_SMTInterpol:
			result.setOption(":produce-models", true);
			result.setOption(":produce-unsat-cores", true);
			result.setOption(":produce-interpolants", true);
			result.setOption(":interpolant-check-mode", true);
			result.setOption(":proof-transformation", "LU");
			// mScript.setOption(":proof-transformation", "RPI");
			// mScript.setOption(":proof-transformation", "LURPI");
			// mScript.setOption(":proof-transformation", "RPILU");
			// mScript.setOption(":verbosity", 0);
			result.setLogic("QF_AUFLIRA");
			break;
		default:
			throw new AssertionError("unknown solver");
		}

		final String advertising = System.lineSeparator() + "    SMT script generated on "
				+ new SimpleDateFormat("yyyy/MM/dd").format(new Date())
				+ " by Ultimate. http://ultimate.informatik.uni-freiburg.de/" + System.lineSeparator();
		result.setInfo(":source", advertising);
		result.setInfo(":smt-lib-version", new BigDecimal("2.5"));
		result.setInfo(":category", new QuotedObject("industrial"));

		storage.putStorable(solverId, new IStorable() {

			final Script theScript = result;

			@Override
			public void destroy() {
				try {
					theScript.exit();
				} catch (final SMTLIBException ex) {
					// DD 2015-11-18: If we store all created solvers during a toolchain execution, we should also
					// suppress broken solver exceptions if the solver was already killed by the user
				} catch (final ToolchainCanceledException ex) {
					// DD 2016-05-13: Same as above.
				}
			}
		});
		return result;
	}
}
