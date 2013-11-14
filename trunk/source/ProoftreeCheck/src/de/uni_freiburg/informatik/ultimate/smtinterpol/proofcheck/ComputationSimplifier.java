package de.uni_freiburg.informatik.ultimate.smtinterpol.proofcheck;

/**
 * This class abstracts from the use of the simplifier for computations.
 * Currently it just returns 'simp'.
 * This can be extended.
 * 
 * @author Christian Schilling
 */
public class ComputationSimplifier {
	/**
	 * This method translates a computation simplification step.
	 * Currently it just returns 'simp'.
	 * 
	 * @return the proof rule string
	 */
	public String getRule() {
		return "simp";
	}
}