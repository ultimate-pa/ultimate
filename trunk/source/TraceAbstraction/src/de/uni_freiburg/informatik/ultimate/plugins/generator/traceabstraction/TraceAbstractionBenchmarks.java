package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark.BenchmarkData;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker.TraceCheckerBenchmark;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;

public class TraceAbstractionBenchmarks implements ICsvProviderProvider<Double>{
	private final SmtManager mSmtManager;
	private long traceCheck = 0;
	private long traceCheckStartTime = 0;
	private long traceCheckSat = 0;
	private long traceCheckSatStartTime = 0;
	private long traceCheckInterpolation = 0;
	private long traceCheckInterpolationStartTime = 0;
	
	
	private TraceCheckerBenchmark m_TraceCheckerBenchmark;
	private BenchmarkData m_CegarLoopBenchmarkData;
	
	
	
	public TraceAbstractionBenchmarks(SmtManager mSmtManager) {
		this.mSmtManager = mSmtManager;
	}
	
	public void setCegarLoopBenchmarkGenerator(
			CegarLoopBenchmarkGenerator cegarLoopBenchmarkGenerator) {
		m_CegarLoopBenchmarkData = new BenchmarkData();
		m_CegarLoopBenchmarkData.aggregateBenchmarkData(cegarLoopBenchmarkGenerator);
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
	
	
	public String timingResults() {
//		assert m_Finished : "finish trace abstraction first";
		StringBuilder sb  = new StringBuilder();
//		sb.append("Trace Abstraction runtime: ");
//		sb.append(prettyprintNanoseconds(getRuntime()));
//		if (!m_CounterExampleFeasible) {
			sb.append(" Determine feasibility of statement sequence: ");
			sb.append(prettyprintNanoseconds(traceCheck));
			sb.append(" (thereof: SMT solver sat check ");
			sb.append(prettyprintNanoseconds(traceCheckSat));
			sb.append(", SMT solver interpolation ");
			sb.append(prettyprintNanoseconds(traceCheckInterpolation));
//			sb.append(") Construction basic interpolant automaton: ");
//			sb.append(prettyprintNanoseconds(basicInterpolantAutomaton));
//			sb.append(" Automata difference operation: ");
//			sb.append(prettyprintNanoseconds(differenceTotal - differenceSmtManager));
//			sb.append(" Checking validity of Hoare triples: ");
//			sb.append(prettyprintNanoseconds(differenceSmtManager));
//			sb.append(" (thereof SMT solver ");
//			sb.append(prettyprintNanoseconds(differenceSmtSolver));
			sb.append(") ");
//		}
		return sb.toString();
	}
	
	
	public String printTraceCheckerBenchmark() {
//		assert m_Finished : "finish trace abstraction first";
		if (m_TraceCheckerBenchmark == null) {
			return "no TraceCheckerBenchmark available";
		} else {
			return m_TraceCheckerBenchmark.toString();
		}
	}
	
	
	
	public String printBenchmarkResults() {
		return timingResults() + " " + printTraceCheckerBenchmark() + " " + m_CegarLoopBenchmarkData.toString();
	}
	
//	public void setCounterExampleFeasible() {
//		m_CounterExampleFeasible = true;
//	}
	


	public static String prettyprintNanoseconds(long time) {
		long seconds = time/1000000000;
		long tenthDigit = (time/100000000) % 10;
		return seconds + "." + tenthDigit + "s";
	}
	
	
	@Override
	public String toString() {
		return timingResults() + "\n\t\t" + printTraceCheckerBenchmark() + "\n\t\t" + m_CegarLoopBenchmarkData.toString();
	}

//	public void addTotalNumberOfPredicates(Integer totalNumberOfPredicates) {
//		if (m_totalNumberOfPredicates != null) {
//			m_totalNumberOfPredicates.add(totalNumberOfPredicates);
//		} else {
//			m_totalNumberOfPredicates = new ArrayList<Integer>();
//			m_totalNumberOfPredicates.add(totalNumberOfPredicates);
//		}
//	}



	public void setTraceCheckerBenchmarks(TraceCheckerBenchmark tcb) {
		m_TraceCheckerBenchmark = tcb;
	}



	@Override
	public ICsvProvider<Double> createCvsProvider() {
		SimpleCsvProvider<Double> rtr = new SimpleCsvProvider<>(new String[] { });
		return rtr;
	}
	
}
