/*
 * Copyright (C) 2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE IcfgTransformer library.
 * 
 * The ULTIMATE IcfgTransformer library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE IcfgTransformer library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Script;

/**
 * A preprocessor takes a {@link ModifiableTransFormula} and returns a {@link ModifiableTransFormula}.
 * 
 * @author Jan Leike
 * @author Matthias Heizmann
 */
public abstract class TransitionPreprocessor {

	/**
	 * @return a description of the preprocessing
	 */
	public abstract String getDescription();

	/**
	 * Process a single transition (stem or loop) independently of the other
	 * 
	 * @param mgdScript
	 *            the script
	 * @param tf
	 *            the transition formula
	 * @return a new (processed) transition formula
	 * @throws TermException
	 *             if processing fails
	 */
	public abstract ModifiableTransFormula process(ManagedScript mgdScript, ModifiableTransFormula tf)
			throws TermException;

	/**
	 * Check if the processing was sound.
	 * 
	 * @param script
	 *            the script
	 * @param oldTF
	 *            the old TransFormulaOLR
	 * @param newTF
	 *            the new TransFormulaLR (after processing
	 * @return whether the result is ok
	 */
	public boolean checkSoundness(final Script script, final ModifiableTransFormula oldTF,
			final ModifiableTransFormula newTF) {
		// check nothing per default
		return true;
	}

	@Override
	public String toString() {
		return getDescription();
	}
}
