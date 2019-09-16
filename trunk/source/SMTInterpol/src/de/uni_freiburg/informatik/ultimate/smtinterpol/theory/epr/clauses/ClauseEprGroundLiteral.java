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

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory.TriBool;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgState;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class ClauseEprGroundLiteral extends ClauseEprLiteral {


	public ClauseEprGroundLiteral(final boolean polarity, final EprGroundPredicateAtom atom,
			final EprClause clause, final EprTheory eprTheory) {
		super(polarity, atom, clause, eprTheory);
	}

	@Override
	protected DawgState<ApplicationTerm, TriBool> computeDawg() {
		final EprTheory.TriBool status =
				mEprPredicateAtom.mEprPredicate.getDawg()
						.getValue(((EprGroundPredicateAtom) mEprPredicateAtom).getArgumentsAsWord());

//				mAtom.getDecideStatus() == null ? EprTheory.TriBool.UNKNOWN
//				: (mAtom.getDecideStatus() == mAtom) == mPolarity ? EprTheory.TriBool.TRUE : EprTheory.TriBool.FALSE;
		return mEprTheory.getDawgFactory().createConstantDawg(mEprClause.getVariables(), status);
	}

	@Override
	public boolean isDisjointFrom(final DawgState<ApplicationTerm, Boolean> dawg) {
		return !dawg.getValue(EprHelpers.convertTermListToConstantList(mArgumentTerms));
	}

	public ApplicationTerm[] getInstantiatedArguments(ApplicationTerm[] clauseGrounding) {
		Term[] args = mEprPredicateAtom.getArguments();
		ApplicationTerm[] appTermArgs = new ApplicationTerm[args.length];
		System.arraycopy(args, 0, appTermArgs, 0, args.length);
		return appTermArgs;
	}

	@Override
	public Clause getGroundingForGroundLiteral(final DawgState<ApplicationTerm, Boolean> dawg,
			final Literal groundLiteral) {
//		ApplicationTerm term = (ApplicationTerm) groundLiteral.getAtom().getSMTFormula(mEprTheory.getTheory());
//		List<ApplicationTerm> args = EprHelpers.convertTermArrayToConstantList(term.getParameters());
		// the groundings have nothing to do with the arguments of the ground literal in the sense that
		//  there is no unification or so --> because we have a clause literal that is ground!
		// --> any grounding should work
		final Set<Clause> groundings = getClause().getGroundings(dawg);
		assert !groundings.isEmpty();
		return groundings.iterator().next();
	}

	@Override
	public <V> DawgState<ApplicationTerm, V> litDawg2clauseDawg(DawgState<ApplicationTerm, V> litDawg) {
		return mDawgFactory.createConstantDawg(mEprClause.getVariables(),
				litDawg.getValue(getArgumentsAsAppTerm()));
	}

	@Override
	public DawgState<ApplicationTerm, Boolean> clauseDawg2litDawg(DawgState<ApplicationTerm, Boolean> clauseDawg) {
		return mDawgFactory.createSingletonSet(mEprPredicateAtom.getEprPredicate().getTermVariablesForArguments(),
				getArgumentsAsAppTerm());
	}
}
