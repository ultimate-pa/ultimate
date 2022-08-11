/*
 * Copyright (C) 2016-2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgState;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class ClauseEprQuantifiedLiteral extends ClauseEprLiteral {

	private final EprQuantifiedPredicateAtom mAtom;

	/**
	 * stores variable identities between different quantified literals in the same clause
	 * (for example would remember that in the clause {P(x, y), Q(y, z)} the second position of
	 *  the P-literal and the first position of the Q-literal have the same variable)
	 *
	 *  Once we have filled this map, we can forget the concrete TermVariables.
	 */
	Map<Integer, Map<ClauseEprQuantifiedLiteral, Set<Integer>>> identicalVariablePositionsInOtherClauseLiterals =
			new HashMap<Integer, Map<ClauseEprQuantifiedLiteral,Set<Integer>>>();

	/**
	 * The Dawg signature for the representation of points wrt this Clause literal.
	 * Note that this signature may be shorter than the list mArgumentTermVariables if
	 *  that list contains repetitions and/or constants
	 */
	private final SortedSet<TermVariable> mDawgSignature;

	/**
	 * Translates the EprPredicates signature to the signature that this ClauseLit has.
	 * I.e. translates mAtom.getEprPredicate().getArguments() to mArgumentTermVariables.
	 * In effect, we use this translation for the unification/natural join with the
	 * decide stack literals, which have a canonical signature from their EprPredicate.
	 */
	private final ApplicationTerm[] mGroundArguments;
	/**
	 * For each argument gives the position of the corresponding term variable in the EprClause. This is -1 for ground
	 * argument, or the variable position for other arguments.
	 */
	private final int[] mVariableArguments;


	/**
	 * Roughly the reverse of mVariableArguments. Translates from the variable position of the EprClause to the position
	 * in the epr predicate. Used for translating from unit clause representation as a dawg over the clause signature to
	 * a Dawg over the predicate's signature.
	 *
	 * EDIT: reversing it, seems more useful
	 *
	 * EDIT: undid the reversing, using BinaryRelation instead
	 *
	 * maps from dsl signature colname to clause signature colname
	 */
	final int[] mClauseToPredPosition;

	public ClauseEprQuantifiedLiteral(final boolean polarity, final EprQuantifiedPredicateAtom atom,
			final EprClause clause, final EprTheory eprTheory) {
		super(polarity, atom, clause, eprTheory);
		mAtom = atom;

		// compute the signature of a dawg that describes points where this literal has some state
		final SortedSet<TermVariable> vars = new TreeSet<TermVariable>(EprHelpers.getColumnNamesComparator());
		for (final Term arg : atom.getArguments()) {
			if (arg instanceof TermVariable) {
				vars.add((TermVariable) arg);
			}
		}
		mDawgSignature = vars;

//		Pair<Map<TermVariable, Object>, Map<TermVariable, TermVariable>> p = computeDawgSignatureTranslations();
//		assert p.first != null;
//		assert p.second != null;
//		mTranslationForClause = p.first;
//		mTranslationForEprPredicate = p.second;

		mGroundArguments = new ApplicationTerm[mArgumentTerms.size()];
		mVariableArguments = new int[mArgumentTerms.size()];
		mClauseToPredPosition = new int[mEprClause.getVariables().size()];
		for (int i = 0; i < mClauseToPredPosition.length; i++) {
			mClauseToPredPosition[i] = -1;
		}
		for (int i = 0; i < mArgumentTerms.size(); i++) {
			final Term atomT = mArgumentTerms.get(i);
			if (atomT instanceof ApplicationTerm) {
				mGroundArguments[i] = (ApplicationTerm) atomT;
				mVariableArguments[i] = -1;
			} else {
				int clausePos = mEprClause.getVariablePos((TermVariable) atomT);
				mGroundArguments[i] = null;
				mVariableArguments[i] = clausePos;
				mClauseToPredPosition[clausePos] = i;
			}
		}
	}

	@Override
	/**
	 * Collect the points for this literal for each of the three values (fulfilled, fulfillable, refuted).
	 *
	 * Note:
	 *  the dawgs we are computing for those sets
	 *  - already have the signature of the predicate in the clause
	 *  - are immediately selected upon according to the atoms constants, i.e., if we have P(a, x, b), we
	 *    only take points that start with a and end with b
	 *  - are immediately selected upon upon to the atoms repetitions of variables, i.e., if we have
	 *    P(x, x, y), and the predicate signature is P(u, v, w) we only take points that where the entries
	 *    for u and v are equal.
	 *
	 *  @param decideStackBorder when determining the state we only look at decide stack literals below the given one
	 *                   (we look at all when decideStackBorder is null)
	 */
	public DawgState<ApplicationTerm, EprTheory.TriBool> computeDawg() {
		DawgState<ApplicationTerm, EprTheory.TriBool> dawg = mEprPredicateAtom.mEprPredicate.getDawg();
		if (!mPolarity) {
			dawg = mDawgFactory.createMapped(dawg, t -> t.negate());
		}
		return litDawg2clauseDawg(dawg);
	}

//	/**
//	 * Yields a translation that translates the column names of the epr predicate this clauseLiteral is talking about
//	 * to the column names of the clause that this ClauseLiteral belongs to.
//	 * @return map : predicateColumnNames -> clauseColumnNames
//	 */
//	private Pair<Map<TermVariable, Object>, Map<TermVariable, TermVariable>> computeDawgSignatureTranslations() {
//
//		Map<TermVariable, TermVariable> clauseToPred =
//				new HashMap<TermVariable, TermVariable>();
//		Map<TermVariable, Object> predToClause =
//				new HashMap<TermVariable, Object>();
//		Iterator<TermVariable> predTermVarIt = mAtom.getEprPredicate().getTermVariablesForArguments().iterator();
//		for (int i = 0; i < mArgumentTerms.size(); i++) {
//			Term atomT = mArgumentTerms.get(i);
//			TermVariable tv = predTermVarIt.next();
//			predToClause.put(tv, atomT);
//			if (atomT instanceof TermVariable) {
//				clauseToPred.put(tv, (TermVariable) atomT);
//			}
//		}
//
//		return new Pair<Map<TermVariable, Object>, Map<TermVariable, TermVariable>>(predToClause, clauseToPred);
//	}

	@Override
	public boolean isDisjointFrom(final DawgState<ApplicationTerm, Boolean> dawg) {
		return DawgFactory.isEmpty(mDawgFactory.projectWithMap(dawg, mGroundArguments));
	}

	@Override
	public ApplicationTerm[] getInstantiatedArguments(ApplicationTerm[] clauseGrounding) {
		ApplicationTerm[] args = new ApplicationTerm[getArguments().size()];
		for (int i = 0; i < args.length; i++) {
			if (mGroundArguments[i] != null) {
				args[i] = mGroundArguments[i];
			} else {
				args[i] = clauseGrounding[mVariableArguments[i]];
			}
		}
		return args;
	}

	@Override
	public Clause getGroundingForGroundLiteral(final DawgState<ApplicationTerm, Boolean> dawg,
			final Literal groundLiteral) {
		final ApplicationTerm term = (ApplicationTerm) groundLiteral.getAtom().getSMTFormula(mEprTheory.getTheory());
		final List<ApplicationTerm> args = EprHelpers.convertTermArrayToConstantList(term.getParameters());

		final Map<TermVariable, ApplicationTerm> selectMap = new HashMap<TermVariable, ApplicationTerm>();
		for (int i = 0; i < this.getArguments().size(); i ++) {
			if (this.getArguments().get(i) instanceof TermVariable) {
				selectMap.put((TermVariable) this.getArguments().get(i), args.get(i));
			} else {
				assert this.getArguments().get(i) == args.get(i);
			}
		}
		final DawgState<ApplicationTerm, Boolean> selDawg =
				mDawgFactory.createIntersection(dawg,
						mDawgFactory.createFromSelectMap(mEprClause.getVariables(), selectMap));
		final Set<Clause> groundings = getClause().getGroundings(selDawg);
		return groundings.iterator().next();
	}

	public EprQuantifiedPredicateAtom getAtom() {
		return mAtom;
	}

	public boolean isEqualityLiteral() {
		return mAtom instanceof EprQuantifiedEqualityAtom;
	}

	@Override
	public <V> DawgState<ApplicationTerm, V> litDawg2clauseDawg(DawgState<ApplicationTerm, V> litDawg) {
		DawgState<ApplicationTerm, V> dawg = mDawgFactory.projectWithMap(litDawg, mGroundArguments);
		dawg = mDawgFactory.remap(dawg, mVariableArguments, mEprClause.getVariables());
		return dawg;
	}

	@Override
	public DawgState<ApplicationTerm, Boolean> clauseDawg2litDawg(DawgState<ApplicationTerm, Boolean> clauseDawg) {
		return mDawgFactory.translateClauseSigToPredSig(clauseDawg, mClauseToPredPosition, mGroundArguments,
				getEprPredicate().getTermVariablesForArguments());
	}
}
