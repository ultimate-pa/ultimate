/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2;

import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbsIntPrefInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.AbstractInterpreter;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class AbstractInterpretationRcfgObserver extends BaseObserver {

	private final IUltimateServiceProvider mServices;

	public AbstractInterpretationRcfgObserver(final IUltimateServiceProvider services) {
		mServices = services;
	}

	@Override
	public boolean process(final IElement elem) throws Throwable {
		if (!(elem instanceof BoogieIcfgContainer)) {
			throw new IllegalArgumentException("You cannot use this observer for " + elem.getClass().getSimpleName());
		}
		final BoogieIcfgContainer root = (BoogieIcfgContainer) elem;
		final IPreferenceProvider ups = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		final IProgressAwareTimer timer;
		if (ups.getBoolean(AbsIntPrefInitializer.LABEL_RUN_AS_PRE_ANALYSIS)) {
			timer = mServices.getProgressMonitorService().getChildTimer(0.2);
		} else {
			timer = mServices.getProgressMonitorService();
		}

		if (ups.getBoolean(AbsIntPrefInitializer.LABEL_USE_FUTURE_RCFG)) {
			AbstractInterpreter.runFuture(root, timer, mServices, false);
		} else {
			AbstractInterpreter.run(root, timer, mServices);
		}

		// do not descend, this is already the root
		return false;
	}
}
