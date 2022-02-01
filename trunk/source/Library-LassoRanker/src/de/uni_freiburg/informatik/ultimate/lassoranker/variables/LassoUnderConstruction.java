/*
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
package de.uni_freiburg.informatik.ultimate.lassoranker.variables;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;

/**
 * Container for stem and loop that is used while constructing a lasso that
 * is defined by linear inequalities from a lasso that is defined by 
 * TransFormulas.
 * Although this object itself is immutable, the stem and the loop may be
 * modifiable.
 * @author Matthias Heizmann
 *
 */
public class LassoUnderConstruction {
	private final ModifiableTransFormula mStem;
	private final ModifiableTransFormula mLoop;
	private final long mStemSize;
	private final long mLoopSize;
	public LassoUnderConstruction(final ModifiableTransFormula stem, final ModifiableTransFormula loop) {
		super();
		mStem = stem;
		mLoop = loop;
		mStemSize = (new DAGSize()).treesize(mStem.getFormula());
		mLoopSize = (new DAGSize()).treesize(mLoop.getFormula());
	}
	public ModifiableTransFormula getStem() {
		return mStem;
	}
	public ModifiableTransFormula getLoop() {
		return mLoop;
	}
//	public int getStemSize() {
//		return mStemSize;
//	}
//	public int getLoopSize() {
//		return mLoopSize;
//	}
	
	public long getFormulaSize() {
		return mStemSize + mLoopSize;
	}
	
	
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Stem:" + System.lineSeparator());
		sb.append(getStem());
		sb.append(System.lineSeparator());
		sb.append("Loop:" + System.lineSeparator());
		sb.append(getLoop());
		return sb.toString();
	}

	
	
	/**
	 * Check whether the stem of this lasso is feasible.
	 */
	public LBool checkStemFeasiblity(final Script script) {
		final Term term = mStem.getFormula();
		final LBool lbool = Util.checkSat(script, term);
		return lbool;
	}
	
}
