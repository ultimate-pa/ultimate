/*
 * Copyright (C) 2021 Jonas Werner (wernerj@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.qvasr;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * This class represents a rational vector addition system with resets that model the relations of input and output
 * variables of transition formulas. They consist of a set of tuples of vectors called transformer. The first vector is
 * a binary reset vector indicating a reset to a variable, while the second vector represents an addition to a variable.
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de)
 *
 */
public class Qvasr {
	private final Set<Pair<Term[], Term[]>> mTransformer;

	/**
	 * Construct a new Q-Vasr using a single transformer
	 *
	 * @param initialTransformer
	 */
	public Qvasr(final Term[] resetVector, final Term[] additionVector) {
		final Pair<Term[], Term[]> initialTransformer = new Pair<>(resetVector, additionVector);
		final Set<Pair<Term[], Term[]>> initialTransformerSet = new HashSet<>();
		initialTransformerSet.add(initialTransformer);
		mTransformer = initialTransformerSet;
	}

	/**
	 * Construct a new Q-Vasr using a single transformer
	 *
	 * @param initialTransformer
	 */
	public Qvasr(final Set<Pair<Term[], Term[]>> initialTransformer) {
		mTransformer = initialTransformer;
	}

	public Set<Pair<Term[], Term[]>> getQvasrTransformer() {
		return mTransformer;
	}

	public void addTransformer(final Pair<Term[], Term[]> transformer) {
		mTransformer.add(transformer);
	}

	@Override
	public String toString() {
		return mTransformer.toString();
	}
}
