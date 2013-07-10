package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;


/**
 * A preprocessor performs some modifications to the input formulae for
 * stem and loop.
 * 
 * @author Jan Leike
 */
public interface PreProcessor {
	
	/**
	 * @return the name of this preprocessor
	 */
	public String getName();
	
	/**
	 * @return a description of the preprocessing
	 */
	public String getDescription();
	
	/**
	 * Apply the preprocessing step
	 * @param script the SMT script to use 
	 * @param term   the formula to be processed
	 * @return the processed formula
	 */
	public Term process(Script script, Term term);
}
