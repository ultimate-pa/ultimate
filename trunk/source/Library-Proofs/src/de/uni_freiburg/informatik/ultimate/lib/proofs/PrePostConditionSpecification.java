/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.proofs;

import java.util.Collection;
import java.util.Objects;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;

public class PrePostConditionSpecification<S> implements ISpecification {
	private final Collection<S> mInitialStates;
	private final Predicate<S> mIsFinalState;

	private final IPredicate mPrecondition;
	private final IPredicate mPostcondition;

	public PrePostConditionSpecification(final Collection<S> initialStates, final Predicate<S> isFinalState,
			final IPredicate precondition, final IPredicate postcondition) {
		mInitialStates = initialStates;
		mIsFinalState = isFinalState;
		mPrecondition = Objects.requireNonNull(precondition);
		mPostcondition = Objects.requireNonNull(postcondition);
	}

	public static <LOC extends IcfgLocation> PrePostConditionSpecification<LOC> forIcfg(final IIcfg<LOC> icfg,
			final IPredicateUnifier unifier) {
		return forIcfg(icfg, unifier.getTruePredicate(), unifier.getFalsePredicate());
	}

	public static <LOC extends IcfgLocation> PrePostConditionSpecification<LOC> forIcfg(final IIcfg<LOC> icfg,
			final IPredicate precondition, final IPredicate postcondition) {
		return new PrePostConditionSpecification<>(icfg.getInitialNodes(), l -> IcfgUtils.isErrorLocation(icfg, l),
				precondition, postcondition);
	}

	public Collection<S> getInitialStates() {
		return mInitialStates;
	}

	public boolean isFinalState(final S state) {
		return mIsFinalState.test(state);
	}

	public IPredicate getPrecondition() {
		return mPrecondition;
	}

	public IPredicate getPostcondition() {
		return mPostcondition;
	}
}
