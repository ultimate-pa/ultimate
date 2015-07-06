package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.io.FileNotFoundException;
import java.io.IOException;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.IProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.TerminationRequest;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.Scriptor;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.ScriptorWithGetInterpolants;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.ScriptorWithGetInterpolants.ExternalInterpolator;

/**
 * Wrapper that constructs SMTInterpol or an external solver.
 * 
 * @author dietsch@informatik.uni-freiburg.de,
 *         heizmann@informatik.uni-freiburg.de
 * 
 */
public class SolverBuilder {

	private static final String sSolverLoggerName = "SolverLogger";
	private static final boolean s_UseWrapperScriptWithTermConstructionChecks = false;

	private static Script createSMTInterpol(IUltimateServiceProvider services, IToolchainStorage storage) {
		Logger solverLogger = services.getLoggingService().getLoggerForExternalTool(sSolverLoggerName);
		TerminationRequest termRequest = new SMTInterpolTerminationRequest(services.getProgressMonitorService());
		Script script = new SMTInterpol(solverLogger, false, termRequest);
		script.setOption(":interactive-mode", Boolean.TRUE);
		return script;
	}

	private static Script createExternalSolver(IUltimateServiceProvider services, IToolchainStorage storage,
			String command) throws IOException {
		Logger solverLogger = services.getLoggingService().getLoggerForExternalTool(sSolverLoggerName);
		Script script = new Scriptor(command, solverLogger, services, storage);
		return script;
	}

	private static Script createExternalSolverWithInterpolation(IUltimateServiceProvider services,
			IToolchainStorage storage, String command, ExternalInterpolator externalInterpolator) throws IOException {
		Logger solverLogger = services.getLoggingService().getLoggerForExternalTool(sSolverLoggerName);
		Script script = new ScriptorWithGetInterpolants(command, solverLogger, services, storage, externalInterpolator);
		return script;
	}

	private static class SMTInterpolTerminationRequest implements TerminationRequest {
		private final IProgressMonitorService mMonitor;

		private SMTInterpolTerminationRequest(IProgressMonitorService monitor) {
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
	 * @return A Script that represents an SMT solver which is defined by
	 *         settings.
	 */
	public static Script buildScript(IUltimateServiceProvider services, IToolchainStorage storage, Settings settings) {
		Logger solverLogger = services.getLoggingService().getLoggerForExternalTool(sSolverLoggerName);
		Script result;
		if (settings.useExternalSolver()) {
			solverLogger.info("constructing external solver with command" + settings.getCommandExternalSolver());
			try {
				if (settings.getExternalInterpolator() == null) {
					result = createExternalSolver(services, storage, settings.getCommandExternalSolver());
				} else {
					solverLogger.info("external solver will use " + settings.getExternalInterpolator()
							+ " interpolation mode");
					result = createExternalSolverWithInterpolation(services, storage,
							settings.getCommandExternalSolver(), settings.getExternalInterpolator());
				}
			} catch (IOException e) {
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
			} catch (FileNotFoundException e) {
				solverLogger.error("Unable dump SMT script to " + settings.constructFullPathOfDumpedScript());
				throw new RuntimeException(e);
			}
		}
		if (!settings.useExternalSolver()) {
			result.setOption(":timeout", String.valueOf(settings.getTimeoutSmtInterpol()));
		}
		if (s_UseWrapperScriptWithTermConstructionChecks) {
			result = new ScriptWithTermConstructionChecks(result);
		}
		return result;
	}

	/**
	 * Settings that define how a solver is build.
	 */
	public static class Settings {

		public Settings(boolean useExternalSolver, String commandExternalSolver, long timeoutSmtInterpol,
				ExternalInterpolator externalInterpolator, boolean dumpSmtScriptToFile, String pathOfDumpedScript,
				String baseNameOfDumpedScript) {
			super();
			m_UseExternalSolver = useExternalSolver;
			m_CommandExternalSolver = commandExternalSolver;
			m_TimeoutSmtInterpol = timeoutSmtInterpol;
			m_ExternalInterpolator = externalInterpolator;
			m_DumpSmtScriptToFile = dumpSmtScriptToFile;
			m_PathOfDumpedScript = pathOfDumpedScript;
			m_BaseNameOfDumpedScript = baseNameOfDumpedScript;
		}

		private final boolean m_UseExternalSolver;

		/**
		 * What shell command should be used to call the external smt solver?
		 */
		private final String m_CommandExternalSolver;

		private final long m_TimeoutSmtInterpol;

		private final ExternalInterpolator m_ExternalInterpolator;

		/**
		 * Write SMT solver script to file.
		 */
		private final boolean m_DumpSmtScriptToFile;

		/**
		 * Path to which the SMT solver script is written.
		 */
		private final String m_PathOfDumpedScript;

		/**
		 * Base name (without path and without file ending) of the file to which
		 * the SMT solver script is written.
		 */
		private final String m_BaseNameOfDumpedScript;

		public boolean useExternalSolver() {
			return m_UseExternalSolver;
		}

		public String getCommandExternalSolver() {
			return m_CommandExternalSolver;
		}

		public long getTimeoutSmtInterpol() {
			return m_TimeoutSmtInterpol;
		}

		public ExternalInterpolator getExternalInterpolator() {
			return m_ExternalInterpolator;
		}

		public boolean dumpSmtScriptToFile() {
			return m_DumpSmtScriptToFile;
		}

		public String getPathOfDumpedScript() {
			return m_PathOfDumpedScript;
		}

		public String getBaseNameOfDumpedScript() {
			return m_BaseNameOfDumpedScript;
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
		private String addFileSeparator(String string) {
			if (string.endsWith(System.getProperty("file.separator"))) {
				return string;
			} else {
				return string + System.getProperty("file.separator");
			}

		}
	}
}
