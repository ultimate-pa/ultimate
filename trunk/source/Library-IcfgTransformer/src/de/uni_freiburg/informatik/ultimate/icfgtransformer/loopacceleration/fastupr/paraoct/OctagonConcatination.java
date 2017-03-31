/*
 * Copyright (C) 2017 Jill Enke (enkei@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct;


import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct.OctagonTerm;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct.OneVarOctTerm;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct.TwoVarOctTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;


/**
*
* @author Jill Enke (enkei@informatik.uni-freiburg.de)
*
*/
public class OctagonConcatination {

	
	private final ArrayList<OctagonTerm> mTerms;
	private HashSet<TermVariable> mCachedVariables;
	
	public OctagonConcatination() {
		mTerms = new ArrayList<>();
		mCachedVariables = new HashSet<TermVariable>();
	}
	
	public String toString() {
		if (mTerms.size() == 0) return "";
		String result = "(" + mTerms.get(0).toString() + ")";
		for (int i = 1; i < mTerms.size(); i++) {
			result = result + " and (" + mTerms.get(i).toString() + ")";
		}
		return result;
	}
	
	public void addTerm(OctagonTerm octagonTerm) {
		mTerms.add(octagonTerm);
		mCachedVariables = null;
	}
	
	public ArrayList<OctagonTerm> getTerms() {
		return mTerms;
	}
	
	public int getVariableCount() {
		return getVariables().size();
	}
	
	private HashSet<TermVariable> getVariables() {
		HashSet<TermVariable> variables = new HashSet<>();
		for(OctagonTerm t : mTerms) {
			if (t instanceof OneVarOctTerm) {
				variables.add(t.getFirstVar());
			} else if (t instanceof TwoVarOctTerm) {
				variables.add(t.getFirstVar());
				variables.add(((TwoVarOctTerm) t).getSecondVar());
			}
		}
		mCachedVariables = variables;
		return variables;
	}
}
