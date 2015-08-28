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

import java.util.Collection;
import java.util.Collections;

import de.uni_freiburg.informatik.ultimate.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.LassoUnderConstruction;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.TransFormulaLR;
import de.uni_freiburg.informatik.ultimate.logic.Script;


/**
 * Preprocessor for lassos that takes a preprocessor for TransFormulaLR to
 * translate stem and loop.
 * 
 * @author Jan Leike, Matthias Heizmann
 */
public class StemAndLoopPreprocessor extends LassoPreprocessor {
	
	private final Script m_Script;
	private final TransitionPreprocessor m_TransitionPreprocessor;
	
	
	public StemAndLoopPreprocessor(Script script, TransitionPreprocessor transitionPreProcessor) {
		super();
		m_Script = script;
		m_TransitionPreprocessor = transitionPreProcessor;
	}
	
	@Override
	public String getDescription() {
		return m_TransitionPreprocessor.getDescription();
	}
	
	@Override
	public String getName() {
		return m_TransitionPreprocessor.getClass().getSimpleName();
	}


	/**
	 * {@inheritDoc}
	 */
	@Override
	public Collection<LassoUnderConstruction> process(
			LassoUnderConstruction lasso) throws TermException {
		TransFormulaLR newStem = m_TransitionPreprocessor.process(m_Script, lasso.getStem());
		assert m_TransitionPreprocessor.checkSoundness(m_Script, lasso.getStem(), newStem) : 
			"Soundness check failed for preprocessor " + this.getClass().getSimpleName();;
		TransFormulaLR newLoop = m_TransitionPreprocessor.process(m_Script, lasso.getLoop());
		LassoUnderConstruction newLasso = new LassoUnderConstruction(newStem, newLoop);
		assert m_TransitionPreprocessor.checkSoundness(m_Script, lasso.getLoop(), newLoop) : 
			"Soundness check failed for preprocessor " + this.getClass().getSimpleName();;
		return Collections.singleton(newLasso);
	}
	
	
	
}
