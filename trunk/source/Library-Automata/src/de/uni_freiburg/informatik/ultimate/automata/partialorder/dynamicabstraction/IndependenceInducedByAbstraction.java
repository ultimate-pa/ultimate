/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.partialorder.dynamicabstraction;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.abstraction.IAbstraction;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.abstraction.IndependenceRelationWithAbstraction;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.ILattice;

public class IndependenceInducedByAbstraction<S, L, H> implements IIndependenceInducedByAbstraction<S, L, H> {

	private final IAbstraction<H, L> mAbstraction;
	private final IIndependenceRelation<S, L> mUnderlying;

	public IndependenceInducedByAbstraction(final IIndependenceRelation<S, L> underlying,
			final IAbstraction<H, L> abstraction) {
		mAbstraction = abstraction;
		mUnderlying = underlying;
	}

	@Override
	public IIndependenceRelation<S, L> getInducedIndependence(final H freeVariables) {
		return new IndependenceRelationWithAbstraction<>(mUnderlying, mAbstraction, freeVariables);
	}

	@Override
	public ILattice<H> getAbstractionLattice() {
		return mAbstraction.getHierarchy();
	}
}
