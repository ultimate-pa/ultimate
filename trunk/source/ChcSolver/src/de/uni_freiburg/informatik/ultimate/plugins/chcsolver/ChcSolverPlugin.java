/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE ChcSolver plug-in.
 *
 * The ULTIMATE ChcSolver plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ChcSolver plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ChcSolver plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ChcSolver plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ChcSolver plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.chcsolver;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.IGenerator;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IObserver;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.chcsolver.preferences.ChcSolverPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.chcsolver.preferences.ChcSolverPreferences;

/**
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public class ChcSolverPlugin implements IGenerator {

	private ILogger mLogger;
	private ChcSolverObserver mObserver;
	private IUltimateServiceProvider mServices;
	private ModelType mOldGraphType;

	@Override
	public ModelType getOutputDefinition() {
		return new ModelType(Activator.PLUGIN_ID, ModelType.Type.OTHER, mOldGraphType.getFileNames());
	}

	@Override
	public boolean isGuiRequired() {
		return false;
	}

	@Override
	public ModelQuery getModelQuery() {
		return ModelQuery.LAST;
	}

	@Override
	public void setInputDefinition(final ModelType graphType) {
		mOldGraphType = graphType;
	}

	@Override
	public List<IObserver> getObservers() {
		final List<IObserver> observers = new ArrayList<>();
		final var prefs = new ChcSolverPreferences(mServices.getPreferenceProvider(Activator.PLUGIN_ID));
		mObserver = new ChcSolverObserver(mServices, mLogger, prefs);
		observers.add(mObserver);
		return observers;
	}

	@Override
	public void init() {
		// not needed
	}

	@Override
	public String getPluginName() {
		return Activator.PLUGIN_NAME;
	}

	@Override
	public String getPluginID() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public IElement getModel() {
		return mObserver.getSolution();
	}

	@Override
	public List<String> getDesiredToolIds() {
		return Collections.emptyList();
	}

	@Override
	public IPreferenceInitializer getPreferences() {
		return new ChcSolverPreferenceInitializer();
	}

	@Override
	public void setServices(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public void finish() {
		// not needed
	}
}
