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

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Interface for a vector addition system (Vasr).
 *
 * @author Jonas Werner <wernerj@informatik.uni-freiburg.de>
 *
 * @param <S>
 *            The sort of the vasr, eg Rational or Integer
 */
public interface IVasr<S> {
	/**
	 * Return the dimension, meaning size of each transformer.
	 */
	int getDimension();

	/**
	 * Return all reset and addition vector pairs.
	 *
	 * @return A set of all reset and addition vector pairs.
	 */
	Set<Pair<S[], S[]>> getTransformer();

	/**
	 * Add a new reset addition vector pair to the vasr.
	 *
	 * @param transformer
	 *            a pair of reset and addition vector in the sort of the vasr, eg Rational or Integer.
	 */
	void addTransformer(final Pair<S[], S[]> transformer);
}
