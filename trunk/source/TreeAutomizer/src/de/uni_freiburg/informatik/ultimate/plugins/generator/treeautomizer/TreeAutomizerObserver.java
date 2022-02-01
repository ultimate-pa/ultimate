/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE HornClauseGraphBuilder plug-in.
 *
 * The ULTIMATE HornClauseGraphBuilder plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE HornClauseGraphBuilder plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE HornClauseGraphBuilder plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE HornClauseGraphBuilder plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE HornClauseGraphBuilder plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer;

import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.graph.TreeAutomizerCEGAR;

/**
 * Auto-Generated Stub for the plug-in's Observer
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * @author Mostafa M.A. (mostafa.amin93@gmail.com)
 *
 */
public class TreeAutomizerObserver extends BaseObserver {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final TAPreferences taPrefs;

	public TreeAutomizerObserver(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		taPrefs = new TAPreferences(mServices);
	}

	@Override
	public boolean process(final IElement root) throws Throwable {

		final HornAnnot annot = HornAnnot.getAnnotation(root);
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("HornAnnot as passed to TreeAutomizer:");
			mLogger.debug(annot);
		}

		final TreeAutomizerCEGAR cegar = new TreeAutomizerCEGAR(mServices, annot, taPrefs, mLogger);
		final IResult result = cegar.iterate();
		mServices.getResultService().reportResult(Activator.PLUGIN_ID, result);
		return false;
	}

}
