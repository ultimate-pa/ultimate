/*
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE SwtVisualization plug-in.
 *
 * The ULTIMATE SwtVisualization plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE SwtVisualization plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SwtVisualization plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SwtVisualization plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE SwtVisualization plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.output.swtvisualization;

import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.IOutput;
import de.uni_freiburg.informatik.ultimate.core.model.ITool.ModelQuery;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IObserver;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.output.swtvisualization.preferences.SwtPreferenceInitializer;

/**
 * IOutput implementation for the SWT-based graph visualization.
 */
public class SwtVisualization implements IOutput {

	public static final String PLUGIN_ID = Activator.PLUGIN_ID;

	private ILogger mLogger;
	private ModelType mGraphType;
	private IUltimateServiceProvider mServices;

	@Override
	public List<String> getDesiredToolIds() {
		return Collections.emptyList();
	}

	@Override
	public List<IObserver> getObservers() {
		return Collections
				.singletonList((IObserver) new SwtVisualizationObserver(mLogger, mGraphType, mServices));
	}

	@Override
	public ModelQuery getModelQuery() {
		final IPreferenceProvider ups = mServices.getPreferenceProvider(getPluginID());
		return ups.getEnum(SwtPreferenceInitializer.KEY_WHICH_MODEL, ModelQuery.class);
	}

	@Override
	public void setInputDefinition(final ModelType graphType) {
		mGraphType = graphType;
	}

	@Override
	public String getPluginName() {
		return Activator.PLUGIN_NAME;
	}

	@Override
	public String getPluginID() {
		return PLUGIN_ID;
	}

	@Override
	public void init() {
		// not needed
	}

	@Override
	public boolean isGuiRequired() {
		return true;
	}

	@Override
	public IPreferenceInitializer getPreferences() {
		return new SwtPreferenceInitializer();
	}

	@Override
	public void setServices(final IUltimateServiceProvider services) {
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mServices = services;
	}

	@Override
	public void finish() {
		// not needed
	}
}
