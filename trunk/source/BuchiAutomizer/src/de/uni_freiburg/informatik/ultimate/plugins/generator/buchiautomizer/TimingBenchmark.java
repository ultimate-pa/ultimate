package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.text.DecimalFormat;
import java.util.concurrent.TimeUnit;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.util.Benchmark;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;

public class TimingBenchmark implements ICsvProviderProvider<Double>{
	private final Benchmark m_Benchmark = new Benchmark();
	private final static String s_LassoAnalysis = "LassoAnalysis";
	private final static String s_BuchiInclusion = "BuchiInclusion";
	private final static String s_Minimization = "Minimization";
	
	private long m_SmtSolverElapsedTimeDuringBuchiInclusion = 0;
	private long m_SmtSolverTimeBeforeBuchiInclusion = 0;
	private long m_SmtSolverTimeAfterBuchiInclusion = 0;
	private final SmtManager m_SmtManager;
	
	public TimingBenchmark(SmtManager smtManager) {
		m_SmtManager = smtManager;
		m_Benchmark.start(s_LassoAnalysis);
		m_Benchmark.pause(s_LassoAnalysis);
		m_Benchmark.start(s_BuchiInclusion);
		m_Benchmark.pause(s_BuchiInclusion);
		m_Benchmark.start(s_Minimization);
		m_Benchmark.pause(s_Minimization);
	}
	
	void startLassoAnalysis() {
		m_Benchmark.unpause(s_LassoAnalysis);
	}
	
	void stopLassoAnalysis() {
		m_Benchmark.pause(s_LassoAnalysis);
	}
	
	void startBuchiInclusion() {
		assert m_SmtSolverTimeBeforeBuchiInclusion == 0;
		assert m_SmtSolverTimeAfterBuchiInclusion == 0;
		m_SmtSolverTimeBeforeBuchiInclusion = m_SmtManager.getSatCheckTime();
		m_Benchmark.unpause(s_BuchiInclusion);
	}
	
	void stopBuchiInclusion() {
		m_Benchmark.pause(s_BuchiInclusion);
		m_SmtSolverTimeAfterBuchiInclusion = m_SmtManager.getSatCheckTime();
		assert m_SmtSolverTimeAfterBuchiInclusion >= m_SmtSolverTimeBeforeBuchiInclusion;
		long diff = (m_SmtSolverTimeAfterBuchiInclusion - m_SmtSolverTimeBeforeBuchiInclusion);
		m_SmtSolverElapsedTimeDuringBuchiInclusion += diff;
		m_SmtSolverTimeBeforeBuchiInclusion = 0;
		m_SmtSolverTimeAfterBuchiInclusion = 0;
	}
	
	void startMinimization() {
		m_Benchmark.unpause(s_Minimization);
	}
	
	void stopMinimization() {
		m_Benchmark.pause(s_Minimization);
	}
	
	@Override
	public String toString() {
		DecimalFormat twoDForm = new DecimalFormat("#0.00");
		StringBuilder sb = new StringBuilder();
		sb.append("Time for termination analysis of lassos ");
		sb.append(twoDForm.format(m_Benchmark.getElapsedTime(s_LassoAnalysis, TimeUnit.SECONDS)));
		sb.append("s. ");
		double buchiInclusionTotal = m_Benchmark.getElapsedTime(s_BuchiInclusion, TimeUnit.SECONDS);
		double buchiInclusionSolver = ((double) m_SmtSolverElapsedTimeDuringBuchiInclusion) / 1000000000;
		double buchiInclusionAutomata = buchiInclusionTotal - buchiInclusionSolver;
		sb.append("Time for construction of modules ");
		sb.append(twoDForm.format(buchiInclusionSolver));
		sb.append("s. ");
		sb.append("Time for Büchi inclusion check ");
		sb.append(twoDForm.format(buchiInclusionAutomata));
		sb.append("s. ");
		sb.append("Time for Büchi automata minimization ");
		sb.append(twoDForm.format(m_Benchmark.getElapsedTime(s_Minimization, TimeUnit.SECONDS)));
		sb.append("s.");
		return sb.toString();
	}

	@Override
	public ICsvProvider<Double> createCvsProvider() {
		SimpleCsvProvider<Double> rtr = new SimpleCsvProvider<>(new String[] { });

		return rtr;
	}
}
