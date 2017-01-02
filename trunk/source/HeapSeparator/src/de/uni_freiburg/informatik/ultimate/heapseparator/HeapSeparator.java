/*
 * Copyright (C) 2016 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE HeapSeparator plug-in.
 *
 * The ULTIMATE HeapSeparator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE HeapSeparator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE HeapSeparator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE HeapSeparator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE HeapSeparator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.heapseparator;

import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.IGenerator;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IObserver;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.heapseparator.preferences.PreferenceInitializer;

/**
 * 
 * 
 * @author nutz
 * 
 * 
 */
public class HeapSeparator implements IGenerator {

	private ILogger mlogger;
	private IToolchainStorage mstorage;
	private HeapSeparatorObserver mobserver;
	private IUltimateServiceProvider mservices;

	@Override
	public ModelType getOutputDefinition() {
		// TODO Auto-generated method stub
		return null;
	}
	@Override
	public boolean isGuiRequired() {
		return false;
	}
	@Override
	public ModelQuery getModelQuery() {
		// TODO is this the right setting??
		return ModelQuery.LAST;
	}
	@Override
	public List<String> getDesiredToolIds() {
		// TODO Auto-generated method stub
		return null;
	}
	@Override
	public void setInputDefinition(ModelType graphType) {
		// TODO Auto-generated method stub
		
	}
	@Override
	public List<IObserver> getObservers() {
		mobserver = new HeapSeparatorObserver(mservices);
		return Collections.singletonList(mobserver);
	}
	@Override
	public void setToolchainStorage(IToolchainStorage storage) {
		// TODO Auto-generated method stub
		
	}
	@Override
	public void setServices(IUltimateServiceProvider services) {
		mservices = services;
	}

	@Override
	public void init() {
		// TODO Auto-generated method stub
		
	}
	@Override
	public void finish() {
		// TODO Auto-generated method stub
		
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
	public IPreferenceInitializer getPreferences() {
		return new PreferenceInitializer();
	}
	@Override
	public IElement getModel() {
		return mobserver.getModel();
	}

}
