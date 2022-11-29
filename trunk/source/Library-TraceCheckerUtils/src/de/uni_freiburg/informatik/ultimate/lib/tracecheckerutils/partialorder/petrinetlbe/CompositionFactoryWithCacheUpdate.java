/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.petrinetlbe;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.ICompositionFactory;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.CachedIndependenceRelation.IIndependenceCache;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;

/**
 * A composition factory that updates an {@link IIndependenceCache}, to transfer known independence information from
 * individual letters to their composition.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters
 */
public class CompositionFactoryWithCacheUpdate<L extends IAction> implements ICompositionFactory<L> {

	private final ICompositionFactory<L> mUnderlying;
	private final IIndependenceCache<?, L> mCache;

	public CompositionFactoryWithCacheUpdate(final ICompositionFactory<L> underlying,
			final IIndependenceCache<?, L> cache) {
		mUnderlying = underlying;
		mCache = cache;
	}

	@Override
	public boolean isSequentiallyComposable(final L l1, final L l2) {
		return mUnderlying.isSequentiallyComposable(l1, l2);
	}

	@Override
	public boolean isParallelyComposable(final List<L> letters) {
		return mUnderlying.isParallelyComposable(letters);
	}

	@Override
	public L composeSequential(final L first, final L second) {
		final var composed = mUnderlying.composeSequential(first, second);
		mCache.mergeIndependencies(List.of(first, second), composed);
		return composed;
	}

	@Override
	public L composeParallel(final List<L> letters) {
		final var composed = mUnderlying.composeParallel(letters);
		mCache.mergeIndependencies(letters, composed);
		return composed;
	}
}
