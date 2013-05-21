package de.uni_freiburg.informatik.ultimate.automata;

public class AutomataLibraryException extends Exception {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1643349110083991967L;
	
	private final String m_Message;
	
	public AutomataLibraryException(String message) {
		m_Message = message;
	}
	
	@Override
	public String getMessage() {
		return m_Message;
	}

}
