/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * Copyright (C) 2013-2015 Vincent Langenfeld (langenfv@informatik.uni-freiburg.de)
 *
 * This file is part of the ULTIMATE BlockEncodingV2 plug-in.
 *
 * The ULTIMATE BlockEncodingV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BlockEncodingV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BlockEncodingV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BlockEncodingV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BlockEncodingV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.icfgtransformation;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IcfgTransformer.IBacktranslationTracker;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IcfgTransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class IcfgTransformationObserver implements IUnmanagedObserver {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final IcfgTransformationBacktranslator mBacktranslator;
	private final XnfConversionTechnique mXnfConversionTechnique;
	private final SimplificationTechnique mSimplificationTechnique;

	private IIcfg<?> mResult;

	public IcfgTransformationObserver(final ILogger logger, final IUltimateServiceProvider services,
			final IcfgTransformationBacktranslator backtranslator, final SimplificationTechnique simplTech,
			final XnfConversionTechnique xnfConvTech) {
		mLogger = logger;
		mServices = services;
		mBacktranslator = backtranslator;
		mSimplificationTechnique = simplTech;
		mXnfConversionTechnique = xnfConvTech;
		mResult = null;
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
		final IBacktranslationTracker backtranslationTracker = (oldTransition, newTransition) -> mBacktranslator
				.mapEdges((IcfgEdge) newTransition, (IcfgEdge) oldTransition);

		final IcfgTransformer<?, ?> icfgTransformer;
		if (icfg.getLocationClass().equals(BoogieIcfgLocation.class)) {
			icfgTransformer = createTransformer((IIcfg<BoogieIcfgLocation>) icfg, createBoogieLocationFactory(),
					BoogieIcfgLocation.class, backtranslationTracker);
		} else {
			icfgTransformer =
					createTransformer(icfg, createIcfgLocationFactory(), IcfgLocation.class, backtranslationTracker);
		}
		mResult = icfgTransformer.getResult();
	}

	private <INLOC extends IcfgLocation, OUTLOC extends IcfgLocation> IcfgTransformer<INLOC, OUTLOC> createTransformer(
			final IIcfg<INLOC> icfg, final ILocationFactory<INLOC, OUTLOC> locFac, final Class<OUTLOC> outlocClass,
			final IBacktranslationTracker backtranslationTracker) {
		return new IcfgTransformer<>(mLogger, icfg, locFac, backtranslationTracker, outlocClass, "TransformedIcfg");
	}

	private static ILocationFactory<BoogieIcfgLocation, BoogieIcfgLocation> createBoogieLocationFactory() {
		return (oldLocation, debugIdentifier, procedure) -> {
			final BoogieIcfgLocation rtr = new BoogieIcfgLocation(debugIdentifier, procedure,
					oldLocation.isErrorLocation(), oldLocation.getBoogieASTNode());
			ModelUtils.copyAnnotations(oldLocation, rtr);
			return rtr;
		};
	}

	private static <INLOC extends IcfgLocation> ILocationFactory<INLOC, IcfgLocation> createIcfgLocationFactory() {
		return (oldLocation, debugIdentifier, procedure) -> {
			final IcfgLocation rtr = new IcfgLocation(debugIdentifier, procedure);
			ModelUtils.copyAnnotations(oldLocation, rtr);
			return rtr;
		};
	}

}
