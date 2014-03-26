package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.InCaReCounter;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EdgeChecker.EdgeCheckerBenchmark;
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
	
	// Contains for each trace, the sum of predicates computed for that trace.
	private List<Integer> m_totalNumberOfPredicates;
	private List<Integer> m_NumberOfQuantifiedPredicatesFP;
	private List<Integer> m_NumberOfQuantifiedPredicatesBP;
	private List<int[]> m_SizeOfPredicatesFP;
	private List<int[]> m_SizeOfPredicatesBP;
	private long m_StartingTime;
	private long m_StopTime;
	private boolean m_Finished = false;
	private boolean m_CounterExampleFeasible;
	
	private final EdgeCheckerBenchmark m_EdgeCheckerBenchmark;
	
	
	
	public TraceAbstractionBenchmarks(SmtManager mSmtManager) {
		this.mSmtManager = mSmtManager;
		m_StartingTime = System.nanoTime();
		m_SizeOfPredicatesBP = new ArrayList<int[]>();
		m_SizeOfPredicatesFP = new ArrayList<int[]>();
		m_CounterExampleFeasible = false;
		m_EdgeCheckerBenchmark = new EdgeCheckerBenchmark(new InCaReCounter(), 
				new InCaReCounter(), new InCaReCounter());
	}
	
	public void finishTraceAbstraction() {
		assert m_Finished == false;
		m_Finished = true;
		m_StopTime = System.nanoTime();
	}
	
	public EdgeCheckerBenchmark getEdgeCheckerBenchmark() {
		return m_EdgeCheckerBenchmark;
	}
	
	public long getRuntime() {
		return m_StopTime - m_StartingTime;
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
	
	
	public String timingResults() {
		assert m_Finished : "finish trace abstraction first";
		StringBuilder sb  = new StringBuilder();
		sb.append("Trace Abstraction runtime: ");
		sb.append(prettyprintNanoseconds(getRuntime()));
//		if (!m_CounterExampleFeasible) {
			sb.append(" Determine feasibility of statement sequence: ");
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
//		}
		return sb.toString();
	}
	
	
	public String printPredicateResults() {
		assert m_Finished : "finish trace abstraction first";
		StringBuilder sb  = new StringBuilder();
			if (m_totalNumberOfPredicates != null && !m_totalNumberOfPredicates.isEmpty()) {
				sb.append("Total num of predicates: " + getSumOfIntegerList(m_totalNumberOfPredicates));
			}
			if (m_NumberOfQuantifiedPredicatesFP != null && !m_NumberOfQuantifiedPredicatesFP.isEmpty()) {
				sb.append("\tNum of quantified predicates FP: " + getSumOfIntegerList(m_NumberOfQuantifiedPredicatesFP));
			}
			if (m_NumberOfQuantifiedPredicatesBP != null && !m_NumberOfQuantifiedPredicatesBP.isEmpty()) {
				sb.append("\tNum of quantified predicates BP: " + getSumOfIntegerList(m_NumberOfQuantifiedPredicatesBP));
			}
			if (m_SizeOfPredicatesFP != null && !m_SizeOfPredicatesFP.isEmpty()) {
				sb.append("\tSize of predicates FP: " + getSumOfIntegerArrays(m_SizeOfPredicatesFP));
			}
			if (m_SizeOfPredicatesBP != null && !m_SizeOfPredicatesBP.isEmpty()) {
				sb.append("\tSize of predicates BP: " + getSumOfIntegerArrays(m_SizeOfPredicatesBP));
			}
		return sb.toString();
	}
	
	
	
	public String printBenchmarkResults() {
		return timingResults() + " " + printPredicateResults();
	}
	
	public void setCounterExampleFeasible() {
		m_CounterExampleFeasible = true;
	}
	

	private int getSumOfIntegerArrays(List<int[]> list) {
		int sum = 0; 
		for (int i = 0; i < list.size(); i++) {
			sum += getSumOfIntArray(list.get(i));
		}
		return sum;
	}
	
	private int getSumOfIntegerList(List<Integer> list) {
		int sum = 0; 
		for (int i = 0; i < list.size(); i++) {
			sum += list.get(i);
		}
		return sum;
	}
	
	private int getSumOfIntArray(int[] arr) {
		int sum = 0; 
		for (int i = 0; i < arr.length; i++) {
			sum += arr[i];
		}
		return sum;
	}

	public static String prettyprintNanoseconds(long time) {
		long seconds = time/1000000000;
		long tenthDigit = (time/100000000) % 10;
		return seconds + "." + tenthDigit + "s";
	}
	
	
	@Override
	public String toString() {
		return timingResults() + "\n\t\t" + printPredicateResults();
	}

	public void addTotalNumberOfPredicates(Integer totalNumberOfPredicates) {
		if (m_totalNumberOfPredicates != null) {
			m_totalNumberOfPredicates.add(totalNumberOfPredicates);
		} else {
			m_totalNumberOfPredicates = new ArrayList<Integer>();
			m_totalNumberOfPredicates.add(totalNumberOfPredicates);
		}
	}

	public void addNumberOfQuantifiedPredicatesFP(Integer numberOfQuantifiedPredicatesFP) {
		if (m_NumberOfQuantifiedPredicatesFP != null) {
			m_NumberOfQuantifiedPredicatesFP.add(numberOfQuantifiedPredicatesFP);
		} else {
			m_NumberOfQuantifiedPredicatesFP = new ArrayList<Integer>();
			m_NumberOfQuantifiedPredicatesFP.add(numberOfQuantifiedPredicatesFP);
		}
	}

	public void addNumberOfQuantifiedPredicatesBP(Integer numberOfQuantifiedPredicatesBP) {
		if (m_NumberOfQuantifiedPredicatesBP != null) {
			m_NumberOfQuantifiedPredicatesBP.add(numberOfQuantifiedPredicatesBP);
		} else {
			m_NumberOfQuantifiedPredicatesBP = new ArrayList<Integer>();
			m_NumberOfQuantifiedPredicatesBP.add(numberOfQuantifiedPredicatesBP);
		}
	}



	public void addSizeOfPredicatesFP(int[] sizeOfPredicatesFP) {
		if (m_SizeOfPredicatesFP != null) {
			this.m_SizeOfPredicatesFP.add(sizeOfPredicatesFP);
		} else {
			m_SizeOfPredicatesFP = new ArrayList<int[]>();
			this.m_SizeOfPredicatesFP.add(sizeOfPredicatesFP);
		}
	}


	public void addSizeOfPredicatesBP(int[] m_SizeOfPredicatesBP) {
		if (this.m_SizeOfPredicatesBP != null) {
			this.m_SizeOfPredicatesBP.add(m_SizeOfPredicatesBP);
		} else {
			this.m_SizeOfPredicatesBP = new ArrayList<int[]>();
			this.m_SizeOfPredicatesBP.add(m_SizeOfPredicatesBP);
		}
		
	}
	
}
