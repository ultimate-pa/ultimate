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

import de.uni_freiburg.informatik.ultimate.core.services.model.ILogger;

import de.uni_freiburg.informatik.ultimate.core.model.IGenerator;
import de.uni_freiburg.informatik.ultimate.core.model.IObserver;
import de.uni_freiburg.informatik.ultimate.core.model.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.services.model.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.models.IElement;
import de.uni_freiburg.informatik.ultimate.models.ModelType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.blockencoding.preferences.PreferenceInitializer;

/**
 * Main class of Plug-In BlockEndcoding
 * 
 * 
 * TODO: refine comments
 * 
 */
public class BlockEncoding implements IGenerator {

	private static final String s_PLUGIN_NAME = Activator.s_PLUGIN_NAME;
	private static final String s_PLUGIN_ID = Activator.s_PLUGIN_ID;

	private MinModelConversionObserver mConversionObserver;
	private BlockEncodingObserver mBlockEncodingObserver;
	private ModelType m_InputDefinition;
	private IUltimateServiceProvider mServices;

	@Override
	public String getPluginName() {
		return s_PLUGIN_NAME;
	}

	@Override
	public String getPluginID() {
		return s_PLUGIN_ID;
	}

	@Override
	public void init() {
		ILogger logger = mServices.getLoggingService().getLogger(s_PLUGIN_ID);
		mConversionObserver = new MinModelConversionObserver(mServices);
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
	public void setInputDefinition(ModelType graphType) {
		this.m_InputDefinition = graphType;
	}

	@Override
	public List<IObserver> getObservers() {
		ArrayList<IObserver> observers = new ArrayList<IObserver>();
		observers.add(mBlockEncodingObserver);
		observers.add(mConversionObserver);
		return observers;
	}

	public ModelType getOutputDefinition() {
		if (mConversionObserver.getRoot() == null) {
			return new ModelType("BlockEncodedModel", m_InputDefinition.getType(), m_InputDefinition.getFileNames());
		}
		return new ModelType(Activator.s_PLUGIN_ID, m_InputDefinition.getType(), m_InputDefinition.getFileNames());
	}

	@Override
	public IElement getModel() {
		if (mConversionObserver.getRoot() == null) {
			return mBlockEncodingObserver.getRoot();
		}
		return this.mConversionObserver.getRoot();
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
	public void setToolchainStorage(IToolchainStorage services) {

	}

	@Override
	public void setServices(IUltimateServiceProvider services) {
		mServices = services;
	}

	@Override
	public void finish() {
		// TODO Auto-generated method stub
		
	}
}
