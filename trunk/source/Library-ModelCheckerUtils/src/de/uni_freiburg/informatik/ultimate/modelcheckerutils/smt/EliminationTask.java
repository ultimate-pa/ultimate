/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 * 
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 * 
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;


/**
 * Represents a task for quantifier elimination without quantifier alternation.
 * I.e., there in only a single kind of quantifier.
 * This class is very similar to ({@link QuantifiedFormula} but we want to have
 * this class to make its purpose more explicit
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class EliminationTask {
	private static final boolean DEBUG_USE_TO_STRING_DIRECT = false;
	
	private final int mQuantifier;
	private final LinkedHashSet<TermVariable> mEliminatees;
	private final Term mTerm;

	public EliminationTask(final int quantifier, final Set<TermVariable> eliminatees, final Term term) {
		super();
		assert (quantifier == QuantifiedFormula.EXISTS || quantifier == QuantifiedFormula.FORALL);
		mQuantifier = quantifier;
		mEliminatees = new LinkedHashSet<>();
		for (final TermVariable freeVar : term.getFreeVars()) {
			if (eliminatees.contains(freeVar)) {
				mEliminatees.add(freeVar);
			}
		}
		mTerm = term;
	}
	
	public int getQuantifier() {
		return mQuantifier;
	}

	public Set<TermVariable> getEliminatees() {
		return Collections.unmodifiableSet(mEliminatees);
	}

	public Term getTerm() {
		return mTerm;
	}
	
	public Term toTerm(final Script script) {
		if (mEliminatees.isEmpty()) {
			return mTerm;
		} else {
			return script.quantifier(mQuantifier, mEliminatees.toArray(new TermVariable[mEliminatees.size()]), mTerm);
		}
	}
	
	
	@Override
	public String toString() {
		final String quantifier = (getQuantifier() == QuantifiedFormula.EXISTS ? "∃" : "∀");
		final String vars = getEliminatees().toString();
		final String term = (DEBUG_USE_TO_STRING_DIRECT ? getTerm().toStringDirect() : getTerm().toString());
		return quantifier + " " + vars + ". " + term;
	}
	

	/**
	 * Check if the terms of two {@link EliminationTasks} can be disjoint.
	 * Return sat if disjoint, unsat if equivalent.
	 */
	public static LBool areDistinct(final Script script, final EliminationTask et1, final EliminationTask et2) {
		final Term espTerm = et1.toTerm(script);
		final Term sosTerm = et2.toTerm(script);
		final LBool sat = Util.checkSat(script, script.term("distinct", espTerm, sosTerm));
		return sat;
	}

}