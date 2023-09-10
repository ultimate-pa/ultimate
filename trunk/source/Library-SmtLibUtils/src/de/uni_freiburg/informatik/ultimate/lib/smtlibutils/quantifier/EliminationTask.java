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
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Auxiliary class that we use in our quantifier elimination. Objects of this
 * class define which quantified variables we will try to eliminate in the next
 * of the elimination algorithm. (We call quantified variables that we try to
 * eliminate <em> eliminatees </em>.) Note that this class can be see as
 * {@link QuantifiedFormula} that additionally has a {@link Context}. Our
 * quantifier elimination algorithms consider a formula as a tree and traverse
 * that tree. If such an algorithm processes a node in the tree, the
 * {@link Context} provides information about ancestors, siblings of ancestors,
 * and descendants of siblings of ancestors.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class EliminationTask {
	private static final boolean DEBUG_USE_TO_STRING_DIRECT = false;

	private final int mQuantifier;
	private final LinkedHashSet<TermVariable> mEliminatees;
	private final Term mTerm;
	private final Context mContext;

	public EliminationTask(final int quantifier, final Set<TermVariable> eliminatees, final Term term,
			final Context context) {
		assert (quantifier == QuantifiedFormula.EXISTS || quantifier == QuantifiedFormula.FORALL);
		mQuantifier = quantifier;
		mEliminatees = QuantifierUtils.projectToFreeVars(eliminatees, term);
		mTerm = term;
		mContext = context;
	}

	public EliminationTask(final QuantifiedFormula quantifiedFormula, final Context context) {
		mQuantifier = quantifiedFormula.getQuantifier();
		mEliminatees = QuantifierUtils.projectToFreeVars(Arrays.asList(quantifiedFormula.getVariables()),
				quantifiedFormula.getSubformula());
		mTerm = quantifiedFormula.getSubformula();
		mContext = context;
	}

	public int getQuantifier() {
		return mQuantifier;
	}

	public Set<TermVariable> getEliminatees() {
		return Collections.unmodifiableSet(mEliminatees);
	}

	/**
	 * @return The term in which we are going to eliminate quantifiers. Note that
	 *         this NOT the term that this {@link EliminationTask} represents.
	 */
	public Term getTerm() {
		return mTerm;
	}

	/**
	 * @return The term represented by this {@link EliminationTask}. I.e., the
	 *         {@link QuantifiedFormula} whose variable are the eliminatees and
	 *         whose subformula is the formula in which we want to try to eliminate
	 *         the quantified variables.
	 */
	public Term toTerm(final Script script) {
		if (mEliminatees.isEmpty()) {
			return mTerm;
		} else {
			return script.quantifier(mQuantifier, mEliminatees.toArray(new TermVariable[mEliminatees.size()]), mTerm);
		}
	}

	public Context getContext() {
		return mContext;
	}

	/**
	 * @return An {@link EliminationTask} with additional eliminatees. Ignore all
	 *         additional eliminatees that do not occur in the subformula.
	 */
	public EliminationTask integrateNewEliminatees(final Collection<TermVariable> additionalEliminatees) {
		final Set<TermVariable> additionalOccuringEliminatees = QuantifierUtils.projectToFreeVars(additionalEliminatees,
				getTerm());
		final Set<TermVariable> resultEliminatees = new HashSet<TermVariable>(getEliminatees());
		final boolean modified = resultEliminatees.addAll(additionalOccuringEliminatees);
		if (modified) {
			return new EliminationTask(getQuantifier(), resultEliminatees, getTerm(), mContext);
		} else {
			return this;
		}
	}

	public EliminationTask update(final Set<TermVariable> newEliminatees, final Term term) {
		return new EliminationTask(getQuantifier(), newEliminatees, term, mContext);
	}

	public EliminationTask update(final Term term) {
		return new EliminationTask(getQuantifier(), getEliminatees(), term, mContext);
	}

	public Pair<Term, EliminationTask> makeTight(final IUltimateServiceProvider services,
			final ManagedScript mgdScript) {
		final Term[] dualJuncts = QuantifierUtils.getDualFiniteJuncts(getQuantifier(), getTerm());
		final List<Term> dualJunctsWithEliminatee = new ArrayList<>();
		final List<Term> dualJunctsWithoutEliminatee = new ArrayList<>();
		for (final Term dualJunct : dualJuncts) {
			if (DataStructureUtils.haveEmptyIntersection(getEliminatees(),
					new HashSet<>(Arrays.asList(dualJunct.getFreeVars())))) {
				dualJunctsWithoutEliminatee.add(dualJunct);
			} else {
				dualJunctsWithEliminatee.add(dualJunct);
			}
		}
		if (dualJunctsWithoutEliminatee.isEmpty()) {
			return null;
		} else {
			final Term dualJunctionWithoutEliminatee = QuantifierUtils.applyDualFiniteConnective(mgdScript.getScript(),
					getQuantifier(), dualJunctsWithoutEliminatee);
			final Term dualJunctionWithEliminatee = QuantifierUtils.applyDualFiniteConnective(mgdScript.getScript(),
					getQuantifier(), dualJunctsWithEliminatee);

			final Context newContext = getContext().constructChildContextForConDis(services, mgdScript,
					((ApplicationTerm) getTerm()).getFunction(), dualJunctsWithoutEliminatee);
			return new Pair<>(dualJunctionWithoutEliminatee,
					new EliminationTask(getQuantifier(), getEliminatees(), dualJunctionWithEliminatee, newContext));
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
	 * Check if the terms of two {@link EliminationTasks} can be disjoint. Return
	 * sat if disjoint, unsat if equivalent.
	 */
	public static LBool areDistinct(final Script script, final EliminationTask et1, final EliminationTask et2) {
		final Term espTerm = et1.toTerm(script);
		final Term sosTerm = et2.toTerm(script);
		final LBool sat = Util.checkSat(script, script.term("distinct", espTerm, sosTerm));
		return sat;
	}

}