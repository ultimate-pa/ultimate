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

import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.IPersistentSetChoice;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.IRule;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.IThreadBasedConfiguration;

public class PersistentRule<T, C extends IThreadBasedConfiguration<T, C>> implements IRule<C> {
	private final IRule<C> mUnderlying;
	private final IPersistentSetChoice<RuleInstance<C>, C> mPersistentSets;

	public PersistentRule(final IRule<C> underlying, final IPersistentSetChoice<RuleInstance<C>, C> persistentSets) {
		mUnderlying = underlying;
		mPersistentSets = persistentSets;
	}

	@Override
	public Stream<TransitionProvider<C>> outgoingTransitions(final C configuration) {
		final var persistentSet = mPersistentSets.persistentSet(configuration);
		if (persistentSet == null) {
			return mUnderlying.outgoingTransitions(configuration);
		}
		return mUnderlying.outgoingTransitions(configuration)
				.filter(tp -> persistentSet.contains(new RuleInstance<>(mUnderlying, tp.getThreads())));
	}

	@Override
	public int extensionSize() {
		return mUnderlying.extensionSize();
	}
}
