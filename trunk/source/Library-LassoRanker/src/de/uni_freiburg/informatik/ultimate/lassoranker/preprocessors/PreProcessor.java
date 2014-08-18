/*
 * Copyright (C) 2012-2014 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will
 * be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not,
 * see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by
 * linking or combining it with Eclipse RCP (or a modified version of
 * Eclipse RCP), containing parts covered by the terms of the Eclipse Public
 * License, the licensors of the ULTIMATE LassoRanker Library grant you
 * additional permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors;

import java.util.ArrayList;
import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.LassoBuilder;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.TransFormulaLR;
import de.uni_freiburg.informatik.ultimate.logic.Script;


/**
 * A preprocessor performs some modifications to the input formulae for
 * stem and loop.
 * 
 * @author Jan Leike
 */
public abstract class PreProcessor {
	/**
	 * The LassoBuilder that we are processing.
	 * Is null before process() has been called.
	 */
	protected LassoBuilder m_lassoBuilder = null;
	
	/**
	 * @return a description of the preprocessing
	 */
	public abstract String getDescription();
	
	/**
	 * Process a single transition (stem or loop) independently of the other
	 * @param script the script
	 * @param tf the transition formula
	 * @param stem is this a stem (as opposed to a loop) transition?
	 * @return a new (processed) transition formula
	 * @throws TermException if processing fails
	 */
	protected abstract TransFormulaLR processTransition(
			Script script, TransFormulaLR tf, boolean stem) throws TermException;
	
	/**
	 * Check if the processing was sound.
	 * 
	 * @param script the script
	 * @param oldTF the old TransFormulaLR
	 * @param newTF the new TransFormulaLR (after processing
	 * @return whether the result is ok
	 */
	protected boolean checkSoundness(Script script, TransFormulaLR oldTF,
			TransFormulaLR newTF) {
		return true; // check nothing
	}
	
	/**
	 * Apply the preprocessing step
	 * @param script the SMT script to use 
	 * @param lasso_builder the lasso builder object to perform the processing on
	 * @return the processed formula
	 * @throws TermException if an error occurred while traversing the term
	 */
	public void process(LassoBuilder lasso_builder)
			throws TermException {
		m_lassoBuilder = lasso_builder;
		Script script = lasso_builder.getScript();
		
		// Process stem
		{
			Collection<TransFormulaLR> old_stem_components =
					lasso_builder.getStemComponents();
			Collection<TransFormulaLR> new_stem_components =
					new ArrayList<TransFormulaLR>(old_stem_components.size());
			for (TransFormulaLR tf : old_stem_components) {
				TransFormulaLR new_tf =
						this.processTransition(script, tf, true);
				assert checkSoundness(script, tf, new_tf)
					: "Soundness check failed for preprocessor "
					+ this.getClass().getSimpleName();
				new_stem_components.add(new_tf);
			}
			lasso_builder.setStemComponents(new_stem_components);
		}
		
		// Process loop
		{
			Collection<TransFormulaLR> old_loop_components =
					lasso_builder.getLoopComponents();
			Collection<TransFormulaLR> new_loop_components =
					new ArrayList<TransFormulaLR>(old_loop_components.size());
			for (TransFormulaLR tf : old_loop_components) {
				TransFormulaLR new_tf =
						this.processTransition(script, tf, false);
				assert checkSoundness(script, tf, new_tf)
					: "Soundness check failed for preprocessor "
					+ this.getClass().getSimpleName();
				new_loop_components.add(new_tf);
			}
			lasso_builder.setLoopComponents(new_loop_components);
		}
	}
	
	public String toString() {
		return this.getDescription();
	}
}
