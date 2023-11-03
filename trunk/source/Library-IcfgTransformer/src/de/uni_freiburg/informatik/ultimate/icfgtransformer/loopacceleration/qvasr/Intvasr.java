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

import java.util.LinkedHashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * This class represents an Integer vector addition system with resets that model the relations of input and output
 * variables of transition formulas. They consist of a set of tuples of vectors called transformer. The first vector is
 * a binary reset vector indicating a reset to a variable, while the second vector represents an addition to a variable.
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de)
 *
 */
public class Intvasr implements IVasr<Integer> {
	private final Set<Pair<Integer[], Integer[]>> mTransformer;
	private Integer mDimension;

	/**
	 * Construct a new IntVasr using a single initial transformer consisting of a reset and addition vector.
	 *
	 * @param resetVector
	 *            The initial reset vector. A reset vector is binary, containing only 0s for reset and 1s for no reset.
	 *
	 * @param additionVector
	 *            The initial addition vector. An addition vector contains Integer numbers.
	 */
	public Intvasr(final Integer[] resetVector, final Integer[] additionVector) {
		final Pair<Integer[], Integer[]> initialTransformer = new Pair<>(resetVector, additionVector);
		final Set<Pair<Integer[], Integer[]>> initialTransformerSet = new LinkedHashSet<>();
		initialTransformerSet.add(initialTransformer);
		mDimension = resetVector.length;
		mTransformer = initialTransformerSet;
	}

	/**
	 * Construct an empty Int-Vasr using a single initial transformer consiting of a reset and addition vector.
	 */
	public Intvasr() {
		mDimension = 0;
		mTransformer = new LinkedHashSet<>();
	}

	@Override
	public int getDimension() {
		return mDimension;
	}

	/**
	 * get all reset, addition vector pairs.
	 *
	 * @return
	 */
	@Override
	public Set<Pair<Integer[], Integer[]>> getTransformer() {
		return mTransformer;
	}

	/**
	 * Add a new reset, addition vector pair to the qvasr.
	 *
	 * @param transformer
	 *            The reset and addition vector to be added.
	 */
	@Override
	public void addTransformer(final Pair<Integer[], Integer[]> transformer) {
		mDimension = transformer.getFirst().length;
		mTransformer.add(transformer);
	}

	/**
	 * Beautify textual output.
	 */
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		for (final Pair<Integer[], Integer[]> transformer : mTransformer) {
			sb.append("  R  A  \n");
			for (int i = 0; i < transformer.getFirst().length; i++) {
				sb.append("[ " + transformer.getFirst()[i].toString() + "  " + transformer.getSecond()[i].toString()
						+ " ]");
				sb.append("\n");
			}
		}
		return sb.toString();
	}
}
