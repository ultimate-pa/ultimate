/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata;

public class InCaReTimer {
	
	private long m_Internal;
	private long m_Call;
	private long m_Return;
	
	private long m_StartTime;
	
	
	

	public InCaReTimer() {
		super();
		m_Internal = 0;
		m_Call = 0;
		m_Return = 0;
		m_StartTime = 0;
	}

	private void run() {
		assert m_StartTime == 0 : "timer already running";
		m_StartTime = System.nanoTime();
	}
	
	public void runIn() {
		run();
	}
	
	public void runCa() {
		run();
	}
	
	public void runRe() {
		run();
	}
	
	public void stopIn() {
		m_Internal += (System.nanoTime() - m_StartTime);
		m_StartTime = 0;
	}
	
	public void stopCa() {
		m_Internal += (System.nanoTime() - m_StartTime);
		m_StartTime = 0;
	}

	public void stopRe() {
		m_Internal += (System.nanoTime() - m_StartTime);
		m_StartTime = 0;
	}

	public long getInternal() {
		return m_Internal;
	}

	public long getCall() {
		return m_Call;
	}

	public long getReturn() {
		return m_Return;
	}
	
	public static String prettyprintNanoseconds(long time) {
		long seconds = time/1000000000;
		long tenthDigit = (time/100000000) % 10;
		return seconds + "." + tenthDigit + "s";
	}
	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append(prettyprintNanoseconds(m_Internal));
		sb.append("In");
		sb.append(prettyprintNanoseconds(m_Call));
		sb.append("Ca");
		sb.append(prettyprintNanoseconds(m_Return));
		sb.append("Re");
		return sb.toString();
	}
	
	

}
