/*
 * Copyright (C) 2017 Ben Biesenbach (ben.biesenbach@gmx.de)
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
package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.biesenbach;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IBacktranslationTracker;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

public class IcfgLoopAcceleration<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>
		implements IIcfgTransformer<OUTLOC> {

	private final IIcfg<OUTLOC> mResultIcfg;

	public IcfgLoopAcceleration(final IIcfg<INLOC> originalIcfg, final ILocationFactory<INLOC, OUTLOC> funLocFac,
			final IBacktranslationTracker backtranslationTracker, final Class<OUTLOC> outLocationClass,
			final String newIcfgIdentifier, final ITransformulaTransformer transformer,
			final IUltimateServiceProvider services) {

		mResultIcfg = new LoopDetectionBB<INLOC, OUTLOC>(null, originalIcfg, outLocationClass, funLocFac,
				newIcfgIdentifier, transformer, backtranslationTracker, services).getResult();
	}

	@Override
	public IIcfg<OUTLOC> getResult() {
		return mResultIcfg;
	}
}