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
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.FastUPRUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 *
 * @author Jill Enke (enkei@informatik.uni-freiburg.de)
 *
 */
public class OctagonConjunction {

	private final ArrayList<OctagonTerm> mTerms;
	private HashSet<TermVariable> mCachedVariables;

	public OctagonConjunction() {
		mTerms = new ArrayList<>();
		mCachedVariables = new HashSet<>();
	}

	public void addTerm(OctagonTerm octagonTerm) {
		if (octagonTerm.equals(null))
			return;
		mTerms.add(octagonTerm);
		mCachedVariables = null;
	}

	public void removeTerm(OctagonTerm octagonTerm) {
		mTerms.remove(octagonTerm);
		mCachedVariables = null;
	}

	public ArrayList<OctagonTerm> getTerms() {
		return mTerms;
	}

	public int getVariableCount() {
		return getVariables().size();
	}

	private HashSet<TermVariable> getVariables() {
		if (mCachedVariables != null)
			return mCachedVariables;
		final HashSet<TermVariable> variables = new HashSet<>();
		for (final OctagonTerm t : mTerms) {
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

	@Override
	public String toString() {
		if (mTerms.size() == 0)
			return "";
		String result = "(" + mTerms.get(0).toString() + ")";
		for (int i = 1; i < mTerms.size(); i++) {
			result = result + " and (" + mTerms.get(i).toString() + ")";
		}
		return result;
	}

	public Term toTerm(Script script, FastUPRUtils utils) {
		final ArrayList<Term> terms = new ArrayList<>();
		for (final OctagonTerm t : mTerms) {
			utils.debug("OctagonTerm: " + t.toString());
			terms.add(t.toTerm(script));
			utils.debug("Term: " + t.toTerm(script).toString());
		}
		Term[] termArray = new Term[terms.size()];
		termArray = terms.toArray(termArray);
		final Term result = script.term("and", termArray);
		utils.debug(result.toString());
		return result;
	}

	public Term toTerm(Script script) {
		final ArrayList<Term> terms = new ArrayList<>();
		for (final OctagonTerm t : mTerms) {
			terms.add(t.toTerm(script));
		}
		Term[] termArray = new Term[terms.size()];
		termArray = terms.toArray(termArray);
		return script.term("and", termArray);
	}
}
