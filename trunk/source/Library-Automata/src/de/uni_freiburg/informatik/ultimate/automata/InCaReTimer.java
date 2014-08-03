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
