package de.uni_freiburg.informatik.ultimate.result;


public interface IResultWithSeverity {

	/**
	 * Severity of a result determines how the result is visualized in a 
	 * front end.
	 */
	public enum Severity { ERROR, WARNING, INFO }
	
	public Severity getSeverity();
}
