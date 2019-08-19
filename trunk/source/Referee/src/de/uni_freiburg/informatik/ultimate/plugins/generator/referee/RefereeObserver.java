/*
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Referee plug-in.
 *
 * The ULTIMATE Referee plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Referee plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Referee plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Referee plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Referee plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.referee;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

/**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class RefereeObserver implements IUnmanagedObserver {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	private final List<IIcfg<?>> mIcfgs;
	private IElement mRootOfNewModel;
	private boolean mLastModel;
	private ModelType mCurrentGraphType;

	public RefereeObserver(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mLastModel = false;
		mIcfgs = new ArrayList<>();
	}

	@Override
	public boolean process(final IElement root) {
		if (root instanceof IIcfg<?>) {
			mIcfgs.add((IIcfg<?>) root);
		}
		return false;
	}

	@Override
	public void finish() {
		if (mLastModel) {
			@SuppressWarnings("unchecked")
			final IIcfg<IcfgLocation> rcfgRootNode = (IIcfg<IcfgLocation>) mIcfgs.stream()
					.filter(a -> IcfgLocation.class.isAssignableFrom(a.getLocationClass())).reduce((a, b) -> b)
					.orElseThrow(UnsupportedOperationException::new);

			if (rcfgRootNode == null) {
				throw new UnsupportedOperationException("Referee needs an RCFG");
			}
			mLogger.info("Analyzing ICFG " + rcfgRootNode.getIdentifier());
			final RefereeStarter tas = new RefereeStarter(mServices, rcfgRootNode);
			mRootOfNewModel = tas.getRootOfNewModel();
		}
	}

	/**
	 * @return the root of the CFG.
	 */
	public IElement getRootOfNewModel() {
		return mRootOfNewModel;
	}

	@Override
	public void init(final ModelType modelType, final int currentModelIndex, final int numberOfModels) {
		mCurrentGraphType = modelType;
		if (currentModelIndex == numberOfModels - 1) {
			mLastModel = true;
		}
	}

	@Override
	public boolean performedChanges() {
		return false;
	}

}
