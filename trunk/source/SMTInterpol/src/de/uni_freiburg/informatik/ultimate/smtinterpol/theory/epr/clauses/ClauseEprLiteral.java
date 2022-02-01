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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgState;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public abstract class ClauseEprLiteral extends ClauseLiteral {

	/**
	 * Flag is set if the fields that are used to determine the state (fulfilled/fulfillable/refuted points)
	 * of this ClauseLiteral have been changed since the last computation of that state.
	 */
	private DawgState<ApplicationTerm, EprTheory.TriBool> mLastState;

	protected final EprPredicateAtom mEprPredicateAtom;

	/**
	 * The current status of the literal according to the decide stack. This is already translated into the signature of
	 * the clause.
	 */
	private DawgState<ApplicationTerm, EprTheory.TriBool> mCachedDawg;

	/**
	 * The TermVariables (EDIT and constants) that this clauseLiterals's atom's arguments have in the clause
	 * this literal belongs to.
	 * (typically the same as mAtom.getArguments(), except that constants there have been
	 *  replaced by fresh TermVariables
	 *  EDIT: now we are just keeping the constants here, so this list is practically identical
	 *   to mAtom.getArguments()
	 *   We deal with repetitions and constants through mTranslationForClause)
	 */
	protected final List<Term> mArgumentTerms;

	protected final List<ApplicationTerm> mArgumentTermsAsAppTerm;

	public ClauseEprLiteral(final boolean polarity, final EprPredicateAtom atom, final EprClause clause, final EprTheory eprTheory) {
		super(polarity, atom, clause, eprTheory);
		mEprPredicateAtom = atom;
		mArgumentTerms = Collections.unmodifiableList(Arrays.asList(atom.getArguments()));

		final List<ApplicationTerm> l = new ArrayList<>();
		for (final Term at : mArgumentTerms) {
			if (at instanceof ApplicationTerm) {
				l.add((ApplicationTerm) at);
			} else {
				assert at instanceof TermVariable;
				l.add(null);
			}
		}
		mArgumentTermsAsAppTerm = Collections.unmodifiableList(l);
	}

	public EprPredicate getEprPredicate()  {
		return  mEprPredicateAtom.getEprPredicate();
	}

	/**
	 * notifies the clause about the beginning of a push/pop scope
	 */
	public void beginScope() {
	}

	/**
	 * notifies the clause about the ending of a push/pop scope
	 */
	public void endScope() {
	}

	public List<Term> getArguments() {
		return mArgumentTerms;
	}

	/**
	 * Returns the same as getArguments, only in a list of objects
	 * @return
	 */
	public List<ApplicationTerm> getArgumentsAsAppTerm() {
		return mArgumentTermsAsAppTerm;
	}

	protected abstract DawgState<ApplicationTerm, EprTheory.TriBool> computeDawg();

	@Override
	protected boolean isDirty() {
		return mLastState != getEprPredicate().getDawg();
	}

	@Override
	/**
	 * Get the dawg describing the points for the clause variable where the literal is true, false, or currently
	 * undefined.
	 */
	public DawgState<ApplicationTerm, EprTheory.TriBool> getDawg() {
		if (mLastState != getEprPredicate().getDawg()) {
			mLastState = getEprPredicate().getDawg();
			mCachedDawg = computeDawg();
		}
		return mCachedDawg;
	}

	public abstract ApplicationTerm[] getInstantiatedArguments(ApplicationTerm[] clauseGrounding);

	/**
	 * Determines if the point(s) this epr literal talks about have an empty intersection
	 * with the points in the given dawg, i.e., if setting a decide stack literal with the
	 * given dawg influences the fulfillment state of this clauseLiteral or not.
	 * @param dawg
	 * @return true iff the dawg and this literal don't talk about at least one common point.
	 */
	public abstract boolean isDisjointFrom(DawgState<ApplicationTerm, Boolean> dawg);

	public abstract <V> DawgState<ApplicationTerm, V> litDawg2clauseDawg(DawgState<ApplicationTerm, V> litDawg);

	public abstract DawgState<ApplicationTerm, Boolean> clauseDawg2litDawg(
			DawgState<ApplicationTerm, Boolean> clauseDawg);


	public abstract Clause getGroundingForGroundLiteral(DawgState<ApplicationTerm, Boolean> dawg,
			Literal groundLiteral);
}
