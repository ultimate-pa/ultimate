/*
 * Copyright (C) 2019 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgToChc plug-in.
 *
 * The ULTIMATE IcfgToChc plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgToChc plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgToChc plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgToChc plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgToChc plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.icfgtochc;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

/**
 *
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class IcfgToChcObserver implements IUnmanagedObserver {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
//	private final XnfConversionTechnique mXnfConversionTechnique;
//	private final SimplificationTechnique mSimplificationTechnique;

//	private IIcfg<?> mResult;
	private IElement mResult;

	public IcfgToChcObserver(final ILogger logger, final IUltimateServiceProvider services) {
//			final ITranslator backtranslator, final SimplificationTechnique simplTech,
//			final XnfConversionTechnique xnfConvTech) {
		mLogger = logger;
		mServices = services;
//		mSimplificationTechnique = simplTech;
//		mXnfConversionTechnique = xnfConvTech;
//		mResult = null;
	}

	@Override
	public void init(final ModelType modelType, final int currentModelIndex, final int numberOfModels) {
		// no initialization needed
	}

	@Override
	public void finish() throws Throwable {
		// not needed
	}

	@Override
	public boolean performedChanges() {
		return false;
	}

	public IElement getModel() {
		return mResult;
	}

	@Override
	public boolean process(final IElement root) throws Exception {
		if (root instanceof IIcfg) {
			processIcfg((IIcfg<?>) root);
			return false;
		}
		return true;
	}

	@SuppressWarnings("unchecked")
	private <INLOC extends IcfgLocation> void processIcfg(final IIcfg<INLOC> icfg) {
//		final IBacktranslationTracker backtranslationTracker = (oldTransition, newTransition) -> mBacktranslator
//				.mapEdges((IcfgEdge) newTransition, (IcfgEdge) oldTransition);

//		if (icfg.getLocationClass().equals(BoogieIcfgLocation.class)) {
//			mResult = createTransformer((IIcfg<BoogieIcfgLocation>) icfg, createBoogieLocationFactory(),
//					BoogieIcfgLocation.class, backtranslationTracker);
//		} else {
//			mResult = createTransformer(icfg, createIcfgLocationFactory(), IcfgLocation.class, backtranslationTracker);
//		}
	}


}
