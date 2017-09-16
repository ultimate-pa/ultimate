/*
 * Copyright (C) 2016-2017 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates;

import java.util.Collections;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Visualizable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;

/**
 * Representation of an abstract state predicate that contains an abstract state from abstract interpretation.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 * @param <STATE>
 * @param <ACTION>
 * @param <VARDECL>
 */
public class AbsIntPredicate<STATE extends IAbstractState<STATE>> extends BasicPredicate {

	private static final long serialVersionUID = 1L;

	private final Set<STATE> mAbstractStates;
	private final IPredicate mPredicate;

	/**
	 * Default constructor of an abstract state predicate, constructed from an abstract state and a matching IPredicate.
	 *
	 */
	public AbsIntPredicate(final IPredicate classicPredicate, final STATE abstractState) {
		this(classicPredicate, Collections.singleton(abstractState));
	}

	public AbsIntPredicate(final IPredicate classicPredicate, final Set<STATE> abstractState) {
		super(classicPredicate.hashCode(), classicPredicate.getProcedures(), classicPredicate.getFormula(),
				classicPredicate.getVars(), classicPredicate.getClosedFormula());
		mAbstractStates = Objects.requireNonNull(abstractState);
		mPredicate = Objects.requireNonNull(classicPredicate);
		assert !mAbstractStates.isEmpty();
		assert !(mPredicate instanceof AbsIntPredicate<?>);
	}

	@Visualizable
	public Set<STATE> getAbstractStates() {
		return Collections.unmodifiableSet(mAbstractStates);
	}

	@Visualizable
	public IPredicate getBackingPredicate() {
		return mPredicate;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(mPredicate.toString()).append(" (");
		return sb.append(mAbstractStates.stream().map(STATE::toLogString).collect(Collectors.toSet())).append(")")
				.toString();
	}
}
