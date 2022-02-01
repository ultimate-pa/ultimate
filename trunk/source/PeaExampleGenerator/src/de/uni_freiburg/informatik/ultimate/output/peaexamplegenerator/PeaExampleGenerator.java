/*
 * Copyright (C) 2020 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE PeaExampleGenerator plug-in.
 *
 * The ULTIMATE PeaExampleGenerator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE PeaExampleGenerator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PeaExampleGenerator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PeaExampleGenerator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE PeaExampleGenerator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.output.peaexamplegenerator;

import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.IOutput;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IObserver;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.output.peaexamplegenerator.preferences.PeaExampleGeneratorPreferenceInitializer;

/**
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class PeaExampleGenerator implements IOutput {

	private PeaExampleGeneratorObserver mObserver;
	private IUltimateServiceProvider mServices;

	@Override
	public String getPluginName() {
		return Activator.PLUGIN_NAME;
	}

	@Override
	public String getPluginID() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public void init() {
		// no init needed
	}

	@Override
	public ModelQuery getModelQuery() {
		return ModelQuery.LAST;
	}

	@Override
	public List<String> getDesiredToolIds() {
		return null;
	}

	/**
	 * Getter for GraphType.
	 *
	 * @return the graph type.
	 */
	public ModelType getOutputDefinition() {
		return null;
	}

	@Override
	public void setInputDefinition(final ModelType graphType) {
		// not required
	}

	@Override
	public List<IObserver> getObservers() {
		mObserver = new PeaExampleGeneratorObserver(mServices);
		return Collections.singletonList(mObserver);
	}

	@Override
	public boolean isGuiRequired() {
		return false;
	}

	@Override
	public IPreferenceInitializer getPreferences() {
		return new PeaExampleGeneratorPreferenceInitializer();
	}

	@Override
	public void setServices(final IUltimateServiceProvider services) {
		mServices = services;
	}

	@Override
	public void finish() {
		// no finish needed
	}
}
