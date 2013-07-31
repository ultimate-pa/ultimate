package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

public class FlaggedDoubleDecker<STATE> extends DoubleDecker<STATE> {

	private final boolean m_Flag;
	
	public FlaggedDoubleDecker(STATE down, STATE up, boolean flag) {
		super(down, up);
		m_Flag = flag;
	}
	
	public boolean getFlag() {
		return m_Flag;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = super.hashCode();
		result = prime * result + (m_Flag ? 1231 : 1237);
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (!super.equals(obj))
			return false;
		if (getClass() != obj.getClass())
			return false;
		FlaggedDoubleDecker other = (FlaggedDoubleDecker) obj;
		if (m_Flag != other.m_Flag)
			return false;
		return true;
	}


	
	
	

}
