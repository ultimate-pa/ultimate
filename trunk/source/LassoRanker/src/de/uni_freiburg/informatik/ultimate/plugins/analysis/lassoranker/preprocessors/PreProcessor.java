package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.exceptions.TermException;


/**
 * A preprocessor performs some modifications to the input formulae for
 * stem and loop.
 * 
 * @author Jan Leike
 */
public interface PreProcessor {
	/**
	 * @return a description of the preprocessing
	 */
	public String getDescription();
	
	/**
	 * Apply the preprocessing step
	 * @param script the SMT script to use 
	 * @param term   the formula to be processed
	 * @return the processed formula
	 * @throws TermException if an error occurred while traversing the term
	 */
	public Term process(Script script, Term term) throws TermException;
}
