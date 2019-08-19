/*
 * Copyright (C) 2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE LassoRanker Library.
 * 
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.LassoPartitioneer;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.LassoUnderConstruction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;


/**
 * A preprocessor that transforms a {@link LassoUnderConstruction} into a
 * collection of {@link LassoUnderConstruction}s.
 * In most cases the result of the preprocessing is a singleton. The 
 * {@link LassoPartitioneer} returns a collection
 * 
 * 
 * @author Jan Leike 
 * @author Matthias Heizmann
 */
public abstract class LassoPreprocessor {
	
	/**
	 * Apply the preprocessing step
	 * @param lasso_builder the lasso builder object to perform the processing on
	 * @return the processed formula
	 * @throws TermException if an error occurred while traversing the term
	 */
	public abstract Collection<LassoUnderConstruction> process(LassoUnderConstruction lasso) throws TermException;
	
	/**
	 * @return name of the preprocessor, typically this is the name of the
	 * class that does the transformation
	 */
	public abstract String getName();
	
	/**
	 * @return a description of the preprocessing
	 */
	public abstract String getDescription();
	
	/**
	 * Check if the processing was sound.
	 * 
	 * @param script the script
	 * @param oldTF the old TransFormulaLR
	 * @param newTF the new TransFormulaLR (after processing
	 * @return whether the result is ok
	 */
	protected boolean checkSoundness(Script script, ModifiableTransFormula oldTF,
			ModifiableTransFormula newTF) {
		return true; // check nothing
	}
	
	@Override
	public String toString() {
		return getDescription();
	}
}
