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
package de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.por;

import java.util.List;
import java.util.stream.IntStream;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.IPersistentSetChoice;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.IRule;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.IThreadBasedConfiguration;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class PersistentRule<T, C extends IThreadBasedConfiguration<T, C>> implements IRule<C> {
	private final IRule<C> mUnderlying;
	private final IPersistentSetChoice<Pair<IRule<C>, Integer>, C> mPersistentSets;

	public PersistentRule(final IRule<C> underlying,
			final IPersistentSetChoice<Pair<IRule<C>, Integer>, C> persistentSets) {
		mUnderlying = underlying;
		mPersistentSets = persistentSets;
	}

	@Override
	public boolean isApplicable(final C config) {
		if (!mUnderlying.isApplicable(config)) {
			return false;
		}
		// TODO check if all instantiations of the rule are blocked by the persistent set or not
		throw new UnsupportedOperationException("not yet implemented");
	}

	@Override
	public List<C> successors(final C config) {
		final var successors = mUnderlying.successors(config);

		// TODO filter successors that are blocked by the persistent set
		throw new UnsupportedOperationException("not yet implemented");
	}

	@Override
	public int extensionSize() {
		return mUnderlying.extensionSize();
	}

	private static <C extends IThreadBasedConfiguration<?, C>> IntStream active(final C original, final C succ) {
		return IntStream.range(0, original.numberOfThreads()).filter(i -> original.getThread(i) != succ.getThread(i));
	}
}
