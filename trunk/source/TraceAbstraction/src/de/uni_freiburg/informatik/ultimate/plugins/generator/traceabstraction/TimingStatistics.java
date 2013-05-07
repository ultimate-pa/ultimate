package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

public class TimingStatistics {
	private final SmtManager mSmtManager;
	private long differenceTotal = 0;
	private long differenceStartTime = 0;
	private long differenceSmtManager = 0;
	private long differenceSmtManagerStartTime = 0;
	private long differenceSmtSolver = 0;
	private long differenceSmtSolverStartTime = 0;
	
	private long traceCheck = 0;
	private long traceCheckStartTime = 0;
	private long traceCheckSat = 0;
	private long traceCheckSatStartTime = 0;
	private long traceCheckInterpolation = 0;
	private long traceCheckInterpolationStartTime = 0;
	
	private long automataMinimization = 0;
	private long automataMinimizationStartTime = 0;
	
	
	public TimingStatistics(SmtManager mSmtManager) {
		this.mSmtManager = mSmtManager;
	}

	public void startDifference() {
		differenceStartTime = System.nanoTime();
		differenceSmtManagerStartTime = mSmtManager.getCodeBlockAssertTime();
		differenceSmtSolverStartTime = mSmtManager.getCodeBlockCheckTime();
	}
	
	public void finishDifference() {
		differenceTotal += (System.nanoTime() - differenceStartTime);
		differenceStartTime = 0;
		differenceSmtManager += (mSmtManager.getCodeBlockAssertTime() - differenceSmtManagerStartTime);
		differenceSmtManager = 0;
		differenceSmtSolver += (mSmtManager.getCodeBlockCheckTime() - differenceSmtSolverStartTime);
		differenceSmtSolver = 0;
	}
	
	public void startTraceCheck() {
		traceCheckStartTime = System.nanoTime();
		traceCheckSatStartTime = mSmtManager.getTraceCheckTime();
		traceCheckInterpolationStartTime = mSmtManager.getInterpolQuriesTime();
	}
	
	public void finishTraceCheck() {
		differenceTotal += (System.nanoTime() - traceCheckStartTime);
		traceCheckStartTime = 0;
		traceCheckSat += (mSmtManager.getTraceCheckTime() - traceCheckSatStartTime);
		traceCheckSatStartTime = 0;
		traceCheckInterpolation += (mSmtManager.getInterpolQuriesTime() - traceCheckInterpolationStartTime);
		traceCheckInterpolationStartTime = 0;
	}
	
	public void startAutomataMinimization() {
		automataMinimizationStartTime = System.nanoTime();
	}
	
	public void finishAutomataMinimization() {
		automataMinimization += (System.nanoTime() - automataMinimizationStartTime);
		automataMinimizationStartTime = 0;
	}
	

}
