/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.poorman;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;

/**
 * Widening operator fot the {@link PoormanAbstractDomain}.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 * @param <BACKING>
 *            The type of the backing abstract states of the poorman domain.
 */
public class PoormanAbstractWideningOperator<BACKING extends IAbstractState<BACKING>>
		implements IAbstractStateBinaryOperator<PoormanAbstractState<BACKING>> {

	private final IUltimateServiceProvider mServices;
	private final IAbstractDomain<BACKING, IcfgEdge> mBackingDomain;
	private final IAbstractStateBinaryOperator<BACKING> mBackingWideningOperator;

	protected PoormanAbstractWideningOperator(final IUltimateServiceProvider services,
			final IAbstractDomain<BACKING, IcfgEdge> backingDomain) {
		mServices = services;
		mBackingDomain = backingDomain;
		mBackingWideningOperator = mBackingDomain.getWideningOperator();
	}

	@Override
	public PoormanAbstractState<BACKING> apply(final PoormanAbstractState<BACKING> first,
			final PoormanAbstractState<BACKING> second) {
		final BACKING widenedBackingState =
				mBackingWideningOperator.apply(first.getBackingState(), second.getBackingState());

		return new PoormanAbstractState<>(mServices, mBackingDomain, widenedBackingState);
	}

}
