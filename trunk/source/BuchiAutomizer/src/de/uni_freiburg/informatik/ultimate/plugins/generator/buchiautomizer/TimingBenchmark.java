package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.util.concurrent.TimeUnit;

import de.uni_freiburg.informatik.ultimate.util.Benchmark;;

public class TimingBenchmark {
	private final Benchmark m_Benchmark = new Benchmark();
	private final static String s_LassoAnalysis = "LassoAnalysis";
	private final static String s_BuchiInclusion = "BuchiInclusion";
	private final static String s_Minimization = "Minimization";
	
	void startLassoAnalysis() {
		m_Benchmark.start(s_LassoAnalysis);
	}
	
	void stopLassoAnalysis() {
		m_Benchmark.stop(s_LassoAnalysis);
	}
	
	void startBuchiInclusion() {
		m_Benchmark.start(s_BuchiInclusion);
	}
	
	void stopBuchiInclusion() {
		m_Benchmark.stop(s_BuchiInclusion);
	}
	
	void startMinimization() {
		m_Benchmark.start(s_Minimization);
	}
	
	void stopMinimization() {
		m_Benchmark.stop(s_Minimization);
	}
	
	@Override
	public String toString() {
		m_Benchmark.stop("myTest");
		StringBuilder sb = new StringBuilder();
		sb.append("Time for termination analysis of lassos ");
		sb.append(m_Benchmark.getElapsedTime(s_LassoAnalysis, TimeUnit.MILLISECONDS));
		sb.append(" ");
		sb.append("Time for Büchi inclusion ");
		sb.append(m_Benchmark.getElapsedTime(s_BuchiInclusion, TimeUnit.MILLISECONDS));
		sb.append(" ");
		sb.append("Time for automata minimization ");
		sb.append(m_Benchmark.getElapsedTime(s_Minimization, TimeUnit.MILLISECONDS));
		sb.append(" ");
		return sb.toString();
	}
}
