/*
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.errorabstraction;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;

/**
 * A class that helps fast enabling/disabling of predicate unification. It will unify iff the flag is enabled.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public class PredicateUnificationMechanism {
	private final IPredicateUnifier mPredicateUnifier;
	private final boolean mUnifyPredicates;

	/**
	 * @param predicateUnifier
	 *            Predicate unifier (must not be {@code null}; needed for True and False predicate generation).
	 * @param unifyPredicates
	 *            {@code true} iff predicates shall be unified
	 */
	public PredicateUnificationMechanism(final IPredicateUnifier predicateUnifier, final boolean unifyPredicates) {
		mPredicateUnifier = predicateUnifier;
		mUnifyPredicates = unifyPredicates;
	}

	public IPredicateUnifier getPredicateUnifier() {
		return mPredicateUnifier;
	}

	public IPredicate getTruePredicate() {
		return mPredicateUnifier.getTruePredicate();
	}

	public IPredicate getFalsePredicate() {
		return mPredicateUnifier.getFalsePredicate();
	}

	/**
	 * @param predicate
	 *            Predicate.
	 * @return original or unified predicate
	 */
	public IPredicate getOrConstructPredicate(final IPredicate predicate) {
		return mUnifyPredicates ? mPredicateUnifier.getOrConstructPredicate(predicate) : predicate;
	}
}
