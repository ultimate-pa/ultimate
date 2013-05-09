package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

public class TimingStatistics {
	private final SmtManager mSmtManager;
	private long traceCheck = 0;
	private long traceCheckStartTime = 0;
	private long traceCheckSat = 0;
	private long traceCheckSatStartTime = 0;
	private long traceCheckInterpolation = 0;
	private long traceCheckInterpolationStartTime = 0;
	
	private long basicInterpolantAutomaton = 0;
	private long basicInterpolantAutomatonStartTime = 0;

	private long differenceTotal = 0;
	private long differenceStartTime = 0;
	private long differenceSmtManager = 0;
	private long differenceSmtManagerStartTime = 0;
	private long differenceSmtSolver = 0;
	private long differenceSmtSolverStartTime = 0;
	
	private long automataMinimization = 0;
	private long automataMinimizationStartTime = 0;
	
	
	public TimingStatistics(SmtManager mSmtManager) {
		this.mSmtManager = mSmtManager;
	}

	public void startTraceCheck() {
		traceCheckStartTime = System.nanoTime();
		traceCheckSatStartTime = mSmtManager.getSatCheckSolverTime();
		traceCheckInterpolationStartTime = mSmtManager.getInterpolQuriesTime();
	}
	
	public void finishTraceCheck() {
		traceCheck += (System.nanoTime() - traceCheckStartTime);
		traceCheckStartTime = 0;
		traceCheckSat += (mSmtManager.getSatCheckSolverTime() - traceCheckSatStartTime);
		traceCheckSatStartTime = 0;
		traceCheckInterpolation += (mSmtManager.getInterpolQuriesTime() - traceCheckInterpolationStartTime);
		traceCheckInterpolationStartTime = 0;
	}
	
	public void startBasicInterpolantAutomaton() {
		basicInterpolantAutomatonStartTime = System.nanoTime();
	}
	
	public void finishBasicInterpolantAutomaton() {
		basicInterpolantAutomaton += (System.nanoTime() - basicInterpolantAutomatonStartTime);
		basicInterpolantAutomatonStartTime = 0;
	}
	
	public void startDifference() {
		differenceStartTime = System.nanoTime();
		differenceSmtManagerStartTime = mSmtManager.getSatCheckTime();
		differenceSmtSolverStartTime = mSmtManager.getSatCheckSolverTime();
	}
	
	public void finishDifference() {
		differenceTotal += (System.nanoTime() - differenceStartTime);
		differenceStartTime = 0;
		differenceSmtManager += (mSmtManager.getSatCheckTime() - differenceSmtManagerStartTime);
		differenceSmtManagerStartTime = 0;
		differenceSmtSolver += (mSmtManager.getSatCheckSolverTime() - differenceSmtSolverStartTime);
		differenceSmtSolverStartTime = 0;
	}
	
	public void startAutomataMinimization() {
		automataMinimizationStartTime = System.nanoTime();
	}
	
	public void finishAutomataMinimization() {
		automataMinimization += (System.nanoTime() - automataMinimizationStartTime);
		automataMinimizationStartTime = 0;
	}
	
	public String printTimingStatistics() {
		StringBuilder sb  = new StringBuilder();
		sb.append("Statistics: ");
		sb.append("Determine feasibility of statement sequence: ");
		sb.append(prettyprintNanoseconds(traceCheck));
		sb.append(" (thereof: SMT solver sat check ");
		sb.append(prettyprintNanoseconds(traceCheckSat));
		sb.append(", SMT solver interpolation ");
		sb.append(prettyprintNanoseconds(traceCheckInterpolation));
		sb.append(") Construction basic interpolant automaton ");
		sb.append(prettyprintNanoseconds(basicInterpolantAutomaton));
		sb.append(" Automata difference operation ");
		sb.append(prettyprintNanoseconds(differenceTotal - differenceSmtManager));
		sb.append(" Checking validity of Hoare triples ");
		sb.append(prettyprintNanoseconds(differenceSmtManager));
		sb.append(" (thereof SMT solver ");
		sb.append(prettyprintNanoseconds(differenceSmtSolver));
		sb.append(") Automata minimization ");
		sb.append(prettyprintNanoseconds(automataMinimization));
		return sb.toString();
	}
	
	public static String prettyprintNanoseconds(long time) {
		long seconds = time/1000000000;
		long tenthDigit = (time/100000000) % 10;
		return seconds + "." + tenthDigit + "s";
	}
	

}
