package de.uni_freiburg.informatik.ultimate.automata;

public class OperationCanceledException extends AutomataLibraryException {

	/**
	 * 
	 */
	private static final long serialVersionUID = -1713238821191695165L;

	@Override
	public String getMessage() {
		return "Timeout";
	}

	
}
