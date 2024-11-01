/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE ViewAbstraction plug-in.
 *
 * The ULTIMATE ViewAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ViewAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ViewAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ViewAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ViewAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs;

import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableList;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class RendezVous<S> implements IRule<Configuration<S>> {
	private final ImmutableList<Pair<S, S>> mTransitions;

	public RendezVous(final S s1, final S s1next, final S s2, final S s2next) {
		mTransitions = new ImmutableList<>(new Pair<>(s1, s1next), ImmutableList.singleton(new Pair<>(s2, s2next)));
	}

	@Override
	public Stream<TransitionProvider<Configuration<S>>> outgoingTransitions(final Configuration<S> configuration) {
		throw new UnsupportedOperationException("not yet implemented");
	}

	@Override
	public int extensionSize() {
		return mTransitions.size() - 1;
	}
}
