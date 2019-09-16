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

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashSet;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class EprClauseManager {

	private final ScopedHashSet<EprClause> mEprClauses = new ScopedHashSet<EprClause>();

	/**
	 * Remembers for each DPLLAtom in which EprClauses it occurs (if any).
	 */
	ScopedHashMap<DPLLAtom, HashSet<EprClause>> mDPLLAtomToClauses =
			new ScopedHashMap<DPLLAtom, HashSet<EprClause>>();

	private final EprTheory mEprTheory;

	public EprClauseManager(final EprTheory eprTheory) {
		mEprTheory = eprTheory;
	}

	public void push() {
		mEprClauses.beginScope();
		mDPLLAtomToClauses.beginScope();
	}

	public void pop() {
		for (final EprClause ec : mEprClauses.currentScope()) {
			ec.disposeOfClause();
		}
		mEprClauses.endScope();
		mDPLLAtomToClauses.endScope();
	}

	public Iterable<EprClause> getAllClauses() {
		return mEprClauses;
	}

	public void updateAtomToClauses(final DPLLAtom atom, final EprClause c) {
		HashSet<EprClause> clauses = mDPLLAtomToClauses.get(atom);
		if (clauses == null) {
			clauses = new HashSet<EprClause>();
			mDPLLAtomToClauses.put(atom, clauses);
		}
		clauses.add(c);
	}

	/**
	 * Add a clause coming from the input script.
	 * @return A ground conflict if adding the given clause directly leads to one.
	 */
	public Clause createEprClause(final Set<Literal> literals) {
		final EprClause newClause = mEprTheory.getEprClauseFactory().getEprClause(literals);

		mEprTheory.getLogger().debug("EPRDEBUG: (EprClauseManager) creating new EprClause: " + newClause);

		registerEprClause(newClause);

		return null;
	}

	/**
	 * Register an eprClause (coming from input or learned) in the corresponding stores.
	 */
	public void registerEprClause(final EprClause newClause) {
		mEprClauses.add(newClause);

		for (final ClauseLiteral cl : newClause.getLiterals()) {
			updateAtomToClauses(cl.getLiteral().getAtom(), newClause);
		}
	}

//	/**
//	 * catches the epr clause for equality reflexivity, so it cna
//	 * @param singleton
//	 * @return
//	 */
//	public Clause createEqualityReflexivityEprClause(Set<Literal> singleton) {
//		EprClause newClause = mEprTheory.getEprClauseFactory().getEprClause(singleton);
//
//		return createEprClause(singleton);
//	}
//
//	public EprClause getEqualityReflexivityClause(EprGroundEqualityAtom atom) {
//		// TODO Auto-generated method stub
//		return null;
//	}

	@Override
	public String toString() {
		return "EprClauseManager, Clauses: " + mEprClauses;
	}
}
