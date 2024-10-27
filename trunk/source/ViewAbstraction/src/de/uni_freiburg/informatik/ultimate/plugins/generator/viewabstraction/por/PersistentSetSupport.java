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

import de.uni_freiburg.informatik.ultimate.automata.partialorder.CachedPersistentSetChoice;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IPersistentSetChoice;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.ITranslator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgPetrifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.ThreadBasedPersistentSets;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class PersistentSetSupport {
	private final IUltimateServiceProvider mServices;
	private final BoogieIcfgContainer mIcfg;
	private final IIndependenceRelation<?, ? super CodeBlock> mIndependence;
	private final int mThreadInstanceCount;

	// TODO preference order used by sleep sets, if applicable
	private final IDfsOrder<IcfgEdge, ?> mDfsOrder = null;

	private final IcfgPetrifier mPetrifier;

	public PersistentSetSupport(final IUltimateServiceProvider services, final BoogieIcfgContainer icfg,
			final IIndependenceRelation<?, ? super CodeBlock> independence, final int threadInstanceCount) {
		mServices = services;
		mIcfg = icfg;
		mIndependence = independence;
		mThreadInstanceCount = threadInstanceCount;

		mPetrifier = new IcfgPetrifier(services, icfg, threadInstanceCount, false);
	}

	public <S> IIndependenceRelation<S, IcfgEdge> petrifiedIndependence() {
		return new PetrifiedIndependence<>(mIndependence, mPetrifier.getBacktranslator());
	}

	public IPersistentSetChoice<IcfgEdge, IPredicate> getPersistentSets() {
		// TODO see if we need to analyse thread-by-thread and pass a subset of error locations
		return new CachedPersistentSetChoice<>(new ThreadBasedPersistentSets<>(mServices, mIcfg,
				petrifiedIndependence(), null, IcfgUtils.getErrorLocations(mIcfg)), null);
	}

	private static class PetrifiedIndependence<S> implements IIndependenceRelation<S, IcfgEdge> {
		private final IIndependenceRelation<?, ? super CodeBlock> mUnderlying;
		private final ITranslator<IIcfgTransition<IcfgLocation>, IIcfgTransition<IcfgLocation>, ?, ?, ?, ?, ?> mTranslator;

		public PetrifiedIndependence(final IIndependenceRelation<?, ? super CodeBlock> underlying,
				final ITranslator<IIcfgTransition<IcfgLocation>, IIcfgTransition<IcfgLocation>, ?, ?, ?, ?, ?> translator) {
			mUnderlying = underlying;
			mTranslator = translator;
		}

		@Override
		public boolean isSymmetric() {
			return mUnderlying.isSymmetric();
		}

		@Override
		public boolean isConditional() {
			return false;
		}

		@Override
		public Dependence isIndependent(final Object state, final IcfgEdge a, final IcfgEdge b) {
			final var originals = mTranslator.translateTrace(List.of(a, b));
			assert originals.size() == 2;
			final var originalA = (CodeBlock) originals.get(0);
			final var originalB = (CodeBlock) originals.get(1);
			return mUnderlying.isIndependent(null, originalA, originalB);
		}
	}
}
