/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE CHC Library.
 *
 * The ULTIMATE CHC Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CHC Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CHC Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CHC Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CHC Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.chc;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * A derivation showing unsatisfiability of a CHC system.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 */
public class Derivation {
	private final HcPredicateSymbol mPredicate;
	private final List<Term> mArguments;
	private final HornClause mClause;
	private final List<Derivation> mChildren;

	public Derivation(final HcPredicateSymbol predicate, final List<Term> args, final HornClause clause,
			final List<Derivation> children) {
		mPredicate = predicate;
		mArguments = args;
		mClause = clause;
		mChildren = children;
	}

	public HcPredicateSymbol getPredicate() {
		return mPredicate;
	}

	public List<Term> getArguments() {
		return mArguments;
	}

	public HornClause getClause() {
		return mClause;
	}

	public List<Derivation> getChildren() {
		return mChildren;
	}
}