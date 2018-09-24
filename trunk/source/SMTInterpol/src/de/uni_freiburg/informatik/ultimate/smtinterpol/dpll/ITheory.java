/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.dpll;


import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;

public interface ITheory {
	/**
	 * Notification of the start of a sat check. Called in response to a
	 * <code>check-sat</code> command.
	 * @return conflict clause if a conflict was found.
	 */
	public Clause startCheck();
	/** Notification of the end of a sat check. Called before the response of a
	 * <code>check-sat</code> command is delivered to the user.
	 */
	public void endCheck();
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
	 * @return a conflict clause or null iff there is no conflict.
	 */
	public Clause computeConflictClause();
	
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
	 * getPropagatedLiteral().  There may be more literals set between
	 * getPropagatedLiteral() and getUnitClause(), but they may 
	 * not be used in the explanation.
	 * 
	 * @return the explanation clause for literal.
	 */
	public Clause getUnitClause(Literal literal);

	/**
	 * Suggest a literal that should be decided. The literal must be known to
	 * the DPLL-Engine and undecided so far.
	 * @return Known, but undecided literal.
	 */
	public Literal getSuggestion();
	
	/**
	 * Print statistics. 
	 */
	public void printStatistics(LogProxy logger);
	/**
	 * Dump current model.  Currently only used for debugging purposes. 
	 */
	public void dumpModel(LogProxy logger);
	/**
	 * Notification that the DPLLEngine is about to make a new decision.
	 * @param currentDecideLevel Number of decisions of the engine.
	 */
	public void increasedDecideLevel(int currentDecideLevel);
	/**
	 * Notification that the DPLLEngine just backtracked a decision.
	 * @param currentDecideLevel Number of decisions of the engine.
	 */
	public void decreasedDecideLevel(int currentDecideLevel);
	
	/**
	 * Notification that a conflict was completely resolved.  The theory
	 * may perform cleanups.
	 * @return a conflict clause or null if no more obvious conflicts.  
	 */
	public Clause backtrackComplete();
	/**
	 * Notification of a restart of the DPLL Engine.
	 * @param iteration Number of the iteration.
	 */
	public void restart(int iteration);
	/**
	 * Called whenever an atom gets removed from the DPLL Engine.
	 * @param atom Atom to remove.
	 */
	public void removeAtom(DPLLAtom atom);
	/**
	 * Save data needed to restore the stack level.  This method is called
	 * during a push on the assertion stack and should return an object suitable
	 * to restore the current state. 
	 * @see #pop(Object)
	 * @return Description of the current state.
	 */
	public Object push();
	/**
	 * Restore the previous state of the assertion stack.  The parameter is the
	 * object returned by the corresponding call to {@link #push() push}.
	 * @param object 		Saved state.
	 * @param targetlevel	The target stacklevel
	 */
	public void pop(Object object, int targetlevel);
	/**
	 * Command used to implement the (get-info :all-statistics) command.  Solver
	 * should return an array containing an identification as keyword and an
	 * array of string-value pairs.
	 * @return Solver statistics
	 */
	public Object[] getStatistics();
}
