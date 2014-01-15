package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

public class TraceAbstractionBenchmarks {
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
	
	// m_NumberOfQuantifierFreePredicates[0] : #quantified predicates of SP
	// m_NumberOfQuantifierFreePredicates[1] : #quantified predicates of FP
	// m_NumberOfQuantifierFreePredicates[2] : #quantified predicates of WP
	// m_NumberOfQuantifierFreePredicates[3] : #quantified predicates of BP
	private List<int[]> m_NumberOfQuantifiedPredicates;
	private List<int[]> m_SizeOfPredicatesFP;
	private List<int[]> m_SizeOfPredicatesBP;
	private long m_StartingTime;
	
	
	
	public TraceAbstractionBenchmarks(SmtManager mSmtManager) {
		this.mSmtManager = mSmtManager;
		m_StartingTime = System.currentTimeMillis();
		m_NumberOfQuantifiedPredicates = new ArrayList<int[]>();
		m_SizeOfPredicatesBP = new ArrayList<int[]>();
		m_SizeOfPredicatesFP = new ArrayList<int[]>();
	}
	
	public long getRuntime() {
		return System.currentTimeMillis() - m_StartingTime;
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
		sb.append("Trace Abstraction runtime: ");
		sb.append(prettyprintNanoseconds(getRuntime()));
		sb.append("Determine feasibility of statement sequence: ");
		sb.append(prettyprintNanoseconds(traceCheck));
		sb.append(" (thereof: SMT solver sat check ");
		sb.append(prettyprintNanoseconds(traceCheckSat));
		sb.append(", SMT solver interpolation ");
		sb.append(prettyprintNanoseconds(traceCheckInterpolation));
		sb.append(") Construction basic interpolant automaton: ");
		sb.append(prettyprintNanoseconds(basicInterpolantAutomaton));
		sb.append(" Automata difference operation: ");
		sb.append(prettyprintNanoseconds(differenceTotal - differenceSmtManager));
		sb.append(" Checking validity of Hoare triples: ");
		sb.append(prettyprintNanoseconds(differenceSmtManager));
		sb.append(" (thereof SMT solver ");
		sb.append(prettyprintNanoseconds(differenceSmtSolver));
		sb.append(") Automata minimization: ");
		sb.append(prettyprintNanoseconds(automataMinimization));
		return sb.toString();
	}
	
	public static String prettyprintNanoseconds(long time) {
		long seconds = time/1000000000;
		long tenthDigit = (time/100000000) % 10;
		return seconds + "." + tenthDigit + "s";
	}
	
	
	@Override
	public String toString() {
		return printTimingStatistics();
	}

	public List<int[]> getNumberOfQuantifiedPredicates() {
		return m_NumberOfQuantifiedPredicates;
	}

	public void addNumberOfQuantifiedPredicates(
			int[] numberOfQuantifiedPredicates) {
		this.m_NumberOfQuantifiedPredicates.add(numberOfQuantifiedPredicates);
	}

	public List<int[]> getSizeOfPredicatesFP() {
		return m_SizeOfPredicatesFP;
	}

	public void addSizeOfPredicatesFP(int[] sizeOfPredicatesFP) {
		this.m_SizeOfPredicatesFP.add(sizeOfPredicatesFP);
	}

	public List<int[]> getSizeOfPredicatesBP() {
		return m_SizeOfPredicatesBP;
	}

	public void addSizeOfPredicatesBP(int[] m_SizeOfPredicatesBP) {
		this.m_SizeOfPredicatesBP.add(m_SizeOfPredicatesBP);
	}

}
