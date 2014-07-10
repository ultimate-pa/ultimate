package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

/**
 * Enum for different types of termination and nontermination analysis
 */
public enum AnalysisType {
	/**
	 * Do not do any analysis (this is the fastest ^^).
	 */
	Disabled,
	
	/**
	 * Use only linear SMT solving. Fast but incomplete.
	 */
	Linear,
	
	/**
	 * Use linear SMT solving, but use a number of guesses for eigenvalues
	 * of the loop to retain more solution compared to plain linear SMT
	 * solving.
	 */
	Linear_with_guesses,
	
	/**
	 * Use nonlinear constraint solving.
	 * This is relatively complete but generally the slowest.
	 */
	Nonlinear;
	
	/**
	 * @return whether this requires a linear logic
	 */
	public boolean isLinear() {
		return this == Linear || this == Linear_with_guesses;
	}
	
	/**
	 * @return whether analysis is disabled
	 */
	public boolean isDisabled() {
		return this == Disabled;
	}
	
	/**
	 * @return whether eigenvalue guesses are required
	 */
	public boolean wantsGuesses() {
		return this == Linear_with_guesses;
	}
	
	/**
	 * @return a list of all possible choices
	 */
	public static AnalysisType[] allChoices() {
		return new AnalysisType[]
				{ Disabled, Linear, Linear_with_guesses, Nonlinear };
	}
}