package local.stalin.smt.dpll;

import org.apache.log4j.Logger;

public interface Theory {
	/**
	 * Set a literal to true and try to derive new conflicts and propagations.
	 * The propagations should be cached until the DPLL engine asks for
	 * unit clauses.  A conflict clause should be returned immediately.
	 * @param literal  the literal which is set to true.
	 * @return a conflict clause, if setting the literal is in conflict.
	 */
	public Clause setLiteral(Literal literal);
	
	/**
	 * Remove the decision of a literal (set it to <em>undecided</em>).  
	 * This is always called in exactly the reverse order to setLiteral.
	 * @param literal the literal which is backtracked.
	 */
	public void backtrackLiteral(Literal literal);
	
	/**
	 * Generates a conflict clause that follows directly from the underlying
	 * theory. All literals in this clause must have been decided to false.
	 * 
	 * This function should do more sophisticated checks to generate conflicts
	 * and propagated literals.
	 * 
	 * @return a conflict clause, null iff there is no conflict.
	 */
	public Clause checkpoint();

	/**
	 * Generates a conflict clause that follows directly from the underlying
	 * theory. All literals in this clause must have been decided to false.
	 * 
	 * If this returns null, the theory is consistent with the set literals.
	 * 
	 * @return a conflict clause, null iff there is no conflict.
	 */
	public Clause computeConflictClause();
	
	/**
	 * Generates a conflict clause that follows directly from the underlying
	 * theory. All literals in this clause must have been decided to false.
	 * 
	 * A valid implementation may always return null.  This is just to
	 * speed-up the process if the theory has generated some knowledge
	 * it wants to share.
	 * 
	 * @return a conflict clause or null.
	 */
	public Clause getConflictClause();
	
	/**
	 * Computes a literal that follows from the other literals that
	 * have been decided before.
	 * 
	 * A valid implementation may always return null.  This is just to
	 * speed-up the process if the theory has generated some knowledge
	 * it wants to share.
	 * @return a "unit" literal, null if none available.
	 */
	public Literal getPropagatedLiteral();
	
	/**
	 * Generates the explanation clause for the given literals.
	 * The clause must be a tautology in the underlying theory.
	 * It must contain the literal and all other literals in 
	 * the clause must have been decided to false.
	 * This is only invoked for literals returned by 
	 * getPropagatedLiteral(), and the decided literals are the same
	 * at that moment (although there may be an equal number of 
	 * setLiteral/backtrackLiteral calls in between).
	 * 
	 * @return the explanation clause for literal.
	 */
	public Clause getUnitClause(Literal literal);

	/**
	 * Print statistics. 
	 */
	public void printStatistics(Logger logger);
	/**
	 * Dump current model.  Currently only used for debugging purposes. 
	 */
	public void dumpModel(Logger logger);
}
