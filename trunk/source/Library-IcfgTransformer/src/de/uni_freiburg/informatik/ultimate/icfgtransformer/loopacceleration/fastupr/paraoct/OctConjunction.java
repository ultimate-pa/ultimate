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
import java.util.List;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.FastUPRUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 *
 * @author Jill Enke (enkei@informatik.uni-freiburg.de)
 *
 */
public class OctConjunction {

	private final ArrayList<OctTerm> mTerms;
	private HashSet<TermVariable> mCachedVariables;

	/**
	 * Creates an empty OctConjunction
	 */
	public OctConjunction() {
		mTerms = new ArrayList<>();
		mCachedVariables = new HashSet<>();
	}

	/**
	 * Adds an OctagonTerm to the Conjunction
	 *
	 * @param octagonTerm
	 */
	public void addTerm(OctTerm octagonTerm) {
		if (octagonTerm == null) {
			return;
		}
		mTerms.add(octagonTerm);
		mCachedVariables = null;
	}

	/**
	 * Removes an OctTerm form the conjunction
	 *
	 * @param octagonTerm
	 *            Term to be removed.
	 */
	public void removeTerm(OctTerm octagonTerm) {
		mTerms.remove(octagonTerm);
		mCachedVariables = null;
	}

	public List<OctTerm> getTerms() {
		return mTerms;
	}

	public int getVariableCount() {
		return getVariables().size();
	}

	private HashSet<TermVariable> getVariables() {
		if (mCachedVariables != null) {
			return mCachedVariables;
		}
		final HashSet<TermVariable> variables = new HashSet<>();
		for (final OctTerm t : mTerms) {
			if (t.isOneVar()) {
				variables.add(t.getFirstVar());
			} else {
				variables.add(t.getFirstVar());
				variables.add(t.getSecondVar());
			}
		}
		mCachedVariables = variables;
		return variables;
	}

	@Override
	public String toString() {
		if (mTerms.isEmpty()) {
			return "";
		}
		final StringBuilder sb = new StringBuilder("(" + mTerms.get(0).toString() + ")");
		for (int i = 1; i < mTerms.size(); i++) {
			sb.append(" and (" + mTerms.get(i).toString() + ")");
		}
		return sb.toString();
	}

	/**
	 * Converts the conjunction to a Term
	 *
	 * @param script
	 *            Script to build a term
	 * @param utils
	 *            Utils for Debug output
	 * @return fresh Term representing the conjunction
	 */
	public Term toTerm(Script script, FastUPRUtils utils) {
		if (isEmpty()) {
			return script.term("true");
		}
		final ArrayList<Term> terms = new ArrayList<>();
		for (final OctTerm t : mTerms) {
			utils.debug("OctTerm: " + t.toString());
			terms.add(t.toTerm(script));
			utils.debug("Term: " + t.toTerm(script).toString());
		}
		Term[] termArray = new Term[terms.size()];
		termArray = terms.toArray(termArray);
		final Term result = script.term("and", termArray);
		utils.debug(result.toString());
		return result;
	}

	/**
	 * Converts the conjunction to a Term
	 *
	 * @param script
	 *            Script to build a term
	 * @return fresh Term representing the conjunction
	 */
	public Term toTerm(Script script) {
		final ArrayList<Term> terms = new ArrayList<>();
		for (final OctTerm t : mTerms) {
			terms.add(t.toTerm(script));
		}
		Term[] termArray = new Term[terms.size()];
		termArray = terms.toArray(termArray);
		if (termArray.length == 1) {
			return termArray[0];
		}
		return script.term("and", termArray);
	}

	public boolean isEmpty() {
		return mTerms.isEmpty();
	}
}
