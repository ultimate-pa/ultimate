/*
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections;

import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Implementation of a {@link ScopedTransitivityGenerator} with {@link Pair}s.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <C>
 *            content type; a user uses {@link Doubleton}s of {@link C} elements.
 */
public class ScopedTransitivityGeneratorPair<C> extends ScopedTransitivityGenerator<Pair<C, C>, C> {
	/**
	 * Constructor.
	 * 
	 * @param compressPaths
	 *            true iff paths should be compressed
	 */
	public ScopedTransitivityGeneratorPair(final boolean compressPaths) {
		super(compressPaths);
	}

	@Override
	protected Pair<C, C> createPair(final C content1, final C content2) {
		return new Pair<>(content1, content2);
	}

	@Override
	protected C getFirst(final Pair<C, C> pair) {
		return pair.getFirst();
	}

	@Override
	protected C getSecond(final Pair<C, C> pair) {
		return pair.getSecond();
	}

	@Override
	public boolean hasContent(final Pair<C, C> pair) {
		return mContent2node.containsKey(pair.getFirst()) && mContent2node.containsKey(pair.getSecond());
	}
}
