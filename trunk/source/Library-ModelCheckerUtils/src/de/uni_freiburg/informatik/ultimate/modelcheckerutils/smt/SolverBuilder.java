package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.io.IOException;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.IProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.TerminationRequest;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.Scriptor;

/**
 * Wrapper that constructs SMTInterpol or an external solver.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class SolverBuilder {

	private static final String sSolverLoggerName = "SolverLogger";

	public static Script createSMTInterpol(IUltimateServiceProvider services, IToolchainStorage storage) {
		Logger solverLogger = services.getLoggingService().getLoggerForExternalTool(sSolverLoggerName);
		TerminationRequest termRequest = new SMTInterpolTerminationRequest(services.getProgressMonitorService());
		Script script = new SMTInterpol(solverLogger, false, termRequest);
		return script;
	}

	public static Script createExternalSolver(IUltimateServiceProvider services, IToolchainStorage storage,
			String command) throws IOException {
		Logger solverLogger = services.getLoggingService().getLoggerForExternalTool(sSolverLoggerName);
		Script script = new Scriptor(command, solverLogger, services, storage);
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

	// TODO: Set deadline for external solver
	// script.setOption(":timeout", String.valueOf(timeoutMilliseconds));

}
