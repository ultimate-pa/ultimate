/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.IGenerator;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IObserver;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.referee.preferences.RefereePreferenceInitializer;

/**
 * Main class of Plug-In Referee
 *
 */
public class Referee implements IGenerator {

	private static final String PLUGIN_NAME = Activator.PLUGIN_NAME;
	private static final String PLUGIN_ID = Activator.PLUGIN_ID;

	private RefereeObserver mObserver;
	private List<IObserver> mObservers;
	private ModelType mInputDefinition;
	private IToolchainStorage mStorage;
	private IUltimateServiceProvider mServices;

	@Override
	public String getPluginName() {
		return PLUGIN_NAME;
	}

	@Override
	public String getPluginID() {
		return PLUGIN_ID;
	}

	@Override
	public void init() {
		mObserver = new RefereeObserver(mServices, mStorage);
		mObservers = Collections.singletonList((IObserver) mObserver);
	}

	@Override
	public ModelQuery getModelQuery() {
		return ModelQuery.ALL;
	}

	@Override
	public List<String> getDesiredToolIds() {
		return Collections.emptyList();
	}

	@Override
	public void setInputDefinition(final ModelType graphType) {
		mInputDefinition = graphType;
	}

	@Override
	public List<IObserver> getObservers() {
		return mObservers;
	}

	@Override
	public ModelType getOutputDefinition() {
		return new ModelType(Activator.PLUGIN_ID, mInputDefinition.getType(), mInputDefinition.getFileNames());
	}

	@Override
	public IElement getModel() {
		return mObserver.getRootOfNewModel();
	}

	@Override
	public boolean isGuiRequired() {
		return false;
	}

	@Override
	public IPreferenceInitializer getPreferences() {
		return new RefereePreferenceInitializer();
	}

	@Override
	public void setToolchainStorage(final IToolchainStorage storage) {
		mStorage = storage;
	}

	@Override
	public void setServices(final IUltimateServiceProvider services) {
		mServices = services;
	}

	@Override
	public void finish() {
		// not needed
	}
}
