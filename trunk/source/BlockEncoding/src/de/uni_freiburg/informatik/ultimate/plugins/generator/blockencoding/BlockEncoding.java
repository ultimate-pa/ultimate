/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE BlockEncoding plug-in.
 *
 * The ULTIMATE BlockEncoding plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BlockEncoding plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BlockEncoding plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BlockEncoding plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BlockEncoding plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.blockencoding;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.IGenerator;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IObserver;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.blockencoding.preferences.PreferenceInitializer;

/**
 * Main class of Plug-In BlockEndcoding
 *
 *
 * TODO: refine comments
 *
 */
public class BlockEncoding implements IGenerator {

	private BlockEncodingObserver mBlockEncodingObserver;
	private ModelType mInputDefinition;
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
		final ILogger logger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mBlockEncodingObserver = new BlockEncodingObserver(logger, mServices);
	}

	@Override
	public ModelQuery getModelQuery() {
		return ModelQuery.LAST;
	}

	@Override
	public List<String> getDesiredToolID() {
		return null;
	}

	@Override
	public void setInputDefinition(final ModelType graphType) {
		mInputDefinition = graphType;
	}

	@Override
	public List<IObserver> getObservers() {
		final ArrayList<IObserver> observers = new ArrayList<>();
		observers.add(mBlockEncodingObserver);
		return observers;
	}

	@Override
	public ModelType getOutputDefinition() {
		return new ModelType(Activator.PLUGIN_ID, mInputDefinition.getType(), mInputDefinition.getFileNames());
	}

	@Override
	public IElement getModel() {
		return mBlockEncodingObserver.getRoot();
	}

	@Override
	public boolean isGuiRequired() {
		return false;
	}

	@Override
	public IPreferenceInitializer getPreferences() {
		return new PreferenceInitializer();
	}

	@Override
	public void setToolchainStorage(final IToolchainStorage services) {
		// not needed
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
