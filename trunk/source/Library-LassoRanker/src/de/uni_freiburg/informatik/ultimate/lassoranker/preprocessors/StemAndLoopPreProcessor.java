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
 * Preprocessor for lassos that takes a preprocessor for TransFormulaLR to
 * translate stem and loop.
 * 
 * @author Jan Leike, Matthias Heizmann
 */
public class StemAndLoopPreProcessor extends LassoPreProcessor {
	
	private final TransitionPreProcessor m_TransitionPreProcessor;
	
	
	public StemAndLoopPreProcessor(TransitionPreProcessor transitionPreProcessor) {
		super();
		m_TransitionPreProcessor = transitionPreProcessor;
	}
	
	private Collection<TransFormulaLR> processStemOrLoop(
			Collection<TransFormulaLR> old_components) throws TermException {
		Script script = m_lassoBuilder.getScript();
		Collection<TransFormulaLR> new_components =
				new ArrayList<TransFormulaLR>(old_components.size());
		for (TransFormulaLR tf : old_components) {
			TransFormulaLR new_tf =
					m_TransitionPreProcessor.process(script, tf);
			assert checkSoundness(script, tf, new_tf)
				: "Soundness check failed for preprocessor "
				+ this.getClass().getSimpleName();
			new_components.add(new_tf);
		}
		return new_components;
	}
	
	/**
	 * Apply the preprocessing step
	 * @param script the SMT script to use 
	 * @param lasso_builder the lasso builder object to perform the processing on
	 * @return the processed formula
	 * @throws TermException if an error occurred while traversing the term
	 */
	public void process(LassoBuilder lasso_builder) throws TermException {
		m_lassoBuilder = lasso_builder;
		
		// Process stem
		if (lasso_builder.isStemApproximated()) {
			lasso_builder.setStemComponentsTermination(
					processStemOrLoop(lasso_builder.getStemComponentsTermination()));
			lasso_builder.setStemComponentsNonTermination(
					processStemOrLoop(lasso_builder.getStemComponentsNonTermination()));
		} else {
			Collection<TransFormulaLR> components =
					processStemOrLoop(lasso_builder.getStemComponentsTermination());
			lasso_builder.setStemComponentsTermination(components);
			lasso_builder.setStemComponentsNonTermination(components);
		}
		
		// Process loop
		if (lasso_builder.isLoopApproximated()) {
			lasso_builder.setLoopComponentsTermination(
					processStemOrLoop(lasso_builder.getLoopComponentsTermination()));
			lasso_builder.setLoopComponentsNonTermination(
					processStemOrLoop(lasso_builder.getLoopComponentsNonTermination()));
		} else {
			Collection<TransFormulaLR> components =
					processStemOrLoop(lasso_builder.getLoopComponentsTermination());
			lasso_builder.setLoopComponentsTermination(components);
			lasso_builder.setLoopComponentsNonTermination(components);
		}
	}

	@Override
	public String getDescription() {
		return m_TransitionPreProcessor.getDescription();
	}
	
}
