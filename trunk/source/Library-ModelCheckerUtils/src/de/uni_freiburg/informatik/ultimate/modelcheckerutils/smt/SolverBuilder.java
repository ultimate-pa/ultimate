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
import java.text.SimpleDateFormat;
import java.util.Date;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.model.IProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.core.services.model.IStorable;
import de.uni_freiburg.informatik.ultimate.core.services.model.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.Settings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.TerminationRequest;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.Scriptor;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.ScriptorWithGetInterpolants;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.ScriptorWithGetInterpolants.ExternalInterpolator;

/**
 * Wrapper that constructs SMTInterpol or an external solver.
 * 
 * @author dietsch@informatik.uni-freiburg.de, heizmann@informatik.uni-freiburg.de
 * 
 */
public class SolverBuilder {
	
	public enum SolverMode { Internal_SMTInterpol, External_PrincessInterpolationMode, 
		External_SMTInterpolInterpolationMode, External_Z3InterpolationMode, External_DefaultMode };

	private static final String sSolverLoggerName = "SolverLogger";
	private static final boolean s_UseWrapperScriptWithTermConstructionChecks = false;

	private static Script createSMTInterpol(IUltimateServiceProvider services, IToolchainStorage storage) {
		Logger solverLogger = services.getLoggingService().getLoggerForExternalTool(sSolverLoggerName);
		TerminationRequest termRequest = new SMTInterpolTerminationRequest(services.getProgressMonitorService());
		Script script = new SMTInterpol(solverLogger, false, termRequest);
		return script;
	}

	private static Script createExternalSolver(IUltimateServiceProvider services, IToolchainStorage storage,
			String command) throws IOException {
		Logger solverLogger = services.getLoggingService().getLoggerForExternalTool(sSolverLoggerName);
		Script script = new Scriptor(command, solverLogger, services, storage);
		return script;
	}
	
	private static Script createExternalSolverWithInterpolation(IUltimateServiceProvider services, IToolchainStorage storage,
			String command, ExternalInterpolator externalInterpolator) throws IOException {
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
	 * @return A Script that represents an SMT solver which is defined by settings.
	 */
	public static Script buildScript(IUltimateServiceProvider services, IToolchainStorage storage, Settings settings) {
		Logger solverLogger = services.getLoggingService().getLoggerForExternalTool(sSolverLoggerName);
		Script result;
		if (settings.useExternalSolver()) {
			solverLogger.info("constructing external solver with command" + settings.getCommandExternalSolver());
			try {
				if (settings.getExternalInterpolator() == null) {
					result = createExternalSolver(
							services, storage, settings.getCommandExternalSolver());
				} else {
					solverLogger.info("external solver will use " + settings.getExternalInterpolator() + " interpolation mode");
					result = createExternalSolverWithInterpolation(
							services, storage, settings.getCommandExternalSolver(), settings.getExternalInterpolator());
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
		
		public Settings(boolean useExternalSolver,
				String commandExternalSolver, long timeoutSmtInterpol,
				ExternalInterpolator externalInterpolator,
				boolean dumpSmtScriptToFile, String pathOfDumpedScript,
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
		 * Base name (without path and without file ending) of the file to which the SMT solver script is 
		 * written.
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
	
	private static Settings constructSolverSettings(final String filename, 
			final SolverMode solverMode,
			final String commandExternalSolver, 
			final boolean dumpSmtScriptToFile,
			final String pathOfDumpedScript) throws AssertionError {
		final boolean useExternalSolver;

		final int timeoutSmtInterpol;
		final ExternalInterpolator externalInterpolator;
		switch (solverMode) {
		case External_DefaultMode:
		{
			useExternalSolver = true;
			timeoutSmtInterpol = -1;
			externalInterpolator = null;
		}
		break;
		case External_PrincessInterpolationMode:
		{
			useExternalSolver = true;
			timeoutSmtInterpol = -1;
			externalInterpolator = ExternalInterpolator.PRINCESS;
		}
		break;
		case External_SMTInterpolInterpolationMode:
		{
			useExternalSolver = true;
			timeoutSmtInterpol = -1;
			externalInterpolator = ExternalInterpolator.SMTINTERPOL;
		}
		break;
		case External_Z3InterpolationMode:
		{
			useExternalSolver = true;
			timeoutSmtInterpol = -1;
			externalInterpolator = ExternalInterpolator.IZ3;
		}
		break;
		case Internal_SMTInterpol:
		{
			useExternalSolver = false;
			timeoutSmtInterpol = 30 * 1000;
			externalInterpolator = null;
		}
		break;
		default:
			throw new AssertionError("unknown solver mode");
		}
		final Settings solverSettings = new Settings(useExternalSolver, 
				commandExternalSolver, timeoutSmtInterpol, externalInterpolator, 
				dumpSmtScriptToFile, pathOfDumpedScript, filename);
		return solverSettings;
	}
	
	
	public static Script buildAndInitializeSolver(IUltimateServiceProvider services, IToolchainStorage storage,
			String filename, SolverMode solverMode, final boolean dumpSmtScriptToFile, final String pathOfDumpedScript,
			final String commandExternalSolver, final boolean dumpUsatCoreTrackBenchmark,
			final boolean dumpMainTrackBenchmark, String logicForExternalSolver, String solverId) throws AssertionError {
		final Settings solverSettings = SolverBuilder.constructSolverSettings(
				filename, solverMode, commandExternalSolver, dumpSmtScriptToFile, pathOfDumpedScript);
		
		Script script = SolverBuilder.buildScript(services, storage, solverSettings);
		if (dumpUsatCoreTrackBenchmark) {
			script = new LoggingScriptForUnsatCoreBenchmarks(script, solverSettings.getBaseNameOfDumpedScript(), solverSettings.getPathOfDumpedScript());
		}
		if (dumpMainTrackBenchmark) {
			script = new LoggingScriptForMainTrackBenchmarks(script, solverSettings.getBaseNameOfDumpedScript(), solverSettings.getPathOfDumpedScript());
		}
		final Script result = script;
		

		result.setOption(":produce-models", true);
		switch (solverMode) {
		case External_DefaultMode:
			result.setOption(":produce-unsat-cores", true);
			result.setLogic(logicForExternalSolver);
		break;
		case External_PrincessInterpolationMode:
		case External_SMTInterpolInterpolationMode:
			result.setOption(":produce-interpolants", true);
			result.setLogic(logicForExternalSolver);
		break;
		case External_Z3InterpolationMode:
			result.setOption(":produce-interpolants", true);
			result.setLogic(logicForExternalSolver);
//			add array-ext function
//			Sort intSort = result.sort("Int");
//			Sort boolSort = result.sort("Bool");
//			Sort arraySort = result.sort("Array", intSort, boolSort);
//			result.declareFun("array-ext", new Sort[]{arraySort, arraySort}, intSort);
		break;
		case Internal_SMTInterpol:
			result.setOption(":produce-unsat-cores", true);
			result.setOption(":produce-interpolants", true);
			result.setOption(":interpolant-check-mode", true);
			result.setOption(":proof-transformation", "LU");
			// m_Script.setOption(":proof-transformation", "RPI");
			// m_Script.setOption(":proof-transformation", "LURPI");
			// m_Script.setOption(":proof-transformation", "RPILU");
			// m_Script.setOption(":verbosity", 0);
			result.setLogic("QF_AUFLIRA");
		break;
		default:
			throw new AssertionError("unknown solver");
		}

		String advertising = "|" + System.lineSeparator() + "    SMT script generated on " + 
				(new SimpleDateFormat("yyyy/MM/dd")).format(new Date()) + 
				" by Ultimate. http://ultimate.informatik.uni-freiburg.de/" + 
				System.lineSeparator() + "|";
		result.setInfo(":source", advertising);
		result.setInfo(":smt-lib-version", "2.0");
		result.setInfo(":category", new QuotedObject("industrial"));
		
		storage.putStorable(solverId, new IStorable() {

			final Script theScript = result;
			
			@Override
			public void destroy() {
				theScript.exit();
			}
		});
		return result;
	}
}
