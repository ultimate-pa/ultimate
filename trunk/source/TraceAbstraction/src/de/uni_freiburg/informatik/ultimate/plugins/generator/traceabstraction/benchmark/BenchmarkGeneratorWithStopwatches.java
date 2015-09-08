/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission 
 * to convey the resulting work.
 */
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
