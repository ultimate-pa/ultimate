package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.benchmark;

import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.TimeUnit;

import de.uni_freiburg.informatik.ultimate.util.Benchmark;


/**
 * Superclass for benchmark generators that use stopwatches.
 * Takes care that
 * <li> no unregistered stopwatches are used
 * <li> we only take the time of stopwatches that have been stopped.
 * @author Matthias Heizmann
 *
 */
public abstract class BenchmarkGeneratorWithStopwatches {
	
	private final Map<String, Boolean> m_RunningStopwatches;
	private final Benchmark m_Benchmark;
	
	public abstract String[] getStopwatches();
	
	public BenchmarkGeneratorWithStopwatches() {
		m_RunningStopwatches = new HashMap<String, Boolean>(getStopwatches().length);
		m_Benchmark = new Benchmark();
		for (String name : getStopwatches()) {
			m_RunningStopwatches.put(name, false);
			m_Benchmark.register(name);
		}
	}
	
	public void start(String stopwatchName) {
		assert m_RunningStopwatches.containsKey(stopwatchName) : 
			"no such stopwatch " + stopwatchName;
		assert m_RunningStopwatches.get(stopwatchName) == false : 
			"already started " + stopwatchName;
		m_RunningStopwatches.put(stopwatchName, true);
		m_Benchmark.unpause(stopwatchName);
	}
	
	public void stop(String stopwatchName) {
		assert m_RunningStopwatches.containsKey(stopwatchName) : 
			"no such stopwatch " + stopwatchName;
		assert m_RunningStopwatches.get(stopwatchName) == true : 
			"not running "  + stopwatchName;
		m_RunningStopwatches.put(stopwatchName, false);
		m_Benchmark.pause(stopwatchName);
	}
	
	protected long getElapsedTime(String stopwatchName) throws StopwatchStillRunningException {
		assert m_RunningStopwatches.containsKey(stopwatchName) : 
			"no such stopwatch " + stopwatchName;
		if(m_RunningStopwatches.get(stopwatchName)) {
			throw new StopwatchStillRunningException();
		}
		return (long) m_Benchmark.getElapsedTime(stopwatchName, TimeUnit.NANOSECONDS);
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		for (String name : getStopwatches()) {
			sb.append(name);
			sb.append(": ");
			try {
				sb.append(prettyprintNanoseconds(getElapsedTime(name)));
			} catch (StopwatchStillRunningException e) {
				sb.append("clockStillRunning!");
			}
			if (m_RunningStopwatches.get(name)) {
				sb.append("stopwatch still running!!!");
			}
			sb.append(" ");
		}
		return sb.toString();
	}

	public static String prettyprintNanoseconds(long time) {
		long seconds = time/1000000000;
		long tenthDigit = (time/100000000) % 10;
		return seconds + "." + tenthDigit + "s";
	}
	
	
	public class StopwatchStillRunningException extends Exception {

		private static final long serialVersionUID = 47519007262609785L;
		
	}
	
}
