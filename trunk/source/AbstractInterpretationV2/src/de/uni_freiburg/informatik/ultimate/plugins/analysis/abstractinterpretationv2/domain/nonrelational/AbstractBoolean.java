package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational;

public enum AbstractBoolean {
	/**
	 * Exactly true.
	 */
	TRUE,
	/**
	 * Exactly false.
	 */
	FALSE,
	/**
	 * Either true or false.
	 */
	TOP,
	/**
	 * Neither true nor false
	 */
	BOTTOM,
	/**
	 * Type error or some other error.
	 */
	INVALID
}