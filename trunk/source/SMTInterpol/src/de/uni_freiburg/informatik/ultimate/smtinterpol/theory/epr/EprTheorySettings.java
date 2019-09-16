package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

public class EprTheorySettings {

	/**
	 * If this is set to true, EprTheory just computes all groundings for a given quantified clause
	 * and returns them to the DPLLEngine.
	 */
	public static final boolean FullInstatiationMode = false;

	/**
	 *
	 */
	public static final boolean UseSimpleDawgLetters = true;

	/**
	 * If this is true, we use all constants declared before the first assert as
	 * the AllConstants set. We assume that no further constants are added
	 * later. If this is false, we dynamically update the AllConstants set by
	 * scanning all the clauses we encounter for constants.
	 *
	 * EDIT: this setting does not seem to make sense as Skolemization can always introduce
	 *  fresh constants that we need to track.
	 */
//	public static final boolean UseAndFreezeDeclaredConstants = true;

}
