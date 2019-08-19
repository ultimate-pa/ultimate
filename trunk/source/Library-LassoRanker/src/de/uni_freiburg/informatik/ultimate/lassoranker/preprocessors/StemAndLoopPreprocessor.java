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
import java.util.Collections;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.TermException;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.TransitionPreprocessor;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.LassoUnderConstruction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;


/**
 * Preprocessor for lassos that takes a preprocessor for TransFormulaLR to
 * translate stem and loop.
 * 
 * @author Jan Leike
 * @author Matthias Heizmann
 */
public class StemAndLoopPreprocessor extends LassoPreprocessor {
	
	private final ManagedScript mMgdScript;
	private final TransitionPreprocessor mTransitionPreprocessor;
	
	
	public StemAndLoopPreprocessor(final ManagedScript mgdScript, final TransitionPreprocessor transitionPreProcessor) {
		super();
		mMgdScript = mgdScript;
		mTransitionPreprocessor = transitionPreProcessor;
	}
	
	@Override
	public String getDescription() {
		return mTransitionPreprocessor.getDescription();
	}
	
	@Override
	public String getName() {
		return mTransitionPreprocessor.getClass().getSimpleName();
	}


	/**
	 * {@inheritDoc}
	 */
	@Override
	public Collection<LassoUnderConstruction> process(
			final LassoUnderConstruction lasso) throws TermException {
		final ModifiableTransFormula newStem = mTransitionPreprocessor.process(mMgdScript, lasso.getStem());
		assert mTransitionPreprocessor.checkSoundness(mMgdScript.getScript(), lasso.getStem(), newStem) :
			"Soundness check failed for preprocessor " + this.getClass().getSimpleName();
		final ModifiableTransFormula newLoop = mTransitionPreprocessor.process(mMgdScript, lasso.getLoop());
		final LassoUnderConstruction newLasso = new LassoUnderConstruction(newStem, newLoop);
		assert mTransitionPreprocessor.checkSoundness(mMgdScript.getScript(), lasso.getLoop(), newLoop) :
			"Soundness check failed for preprocessor " + this.getClass().getSimpleName();
		return Collections.singleton(newLasso);
	}
}
