/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * Copyright (C) 2013-2015 Vincent Langenfeld (langenfv@informatik.uni-freiburg.de)
 * 
 * This file is part of the ULTIMATE BuchiProgramProduct plug-in.
 * 
 * The ULTIMATE BuchiProgramProduct plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BuchiProgramProduct plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BuchiProgramProduct plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BuchiProgramProduct plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE BuchiProgramProduct plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.heapseparator;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.model.IGenerator;
import de.uni_freiburg.informatik.ultimate.core.model.IObserver;
import de.uni_freiburg.informatik.ultimate.core.model.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.services.model.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.heapseparator.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.models.IElement;
import de.uni_freiburg.informatik.ultimate.models.ModelType;

/**
 * 
 * 
 * @author nutz
 * 
 * 
 */
public class HeapSeparator implements IGenerator {

	private Logger m_logger;
	private IToolchainStorage m_storage;
	private HeapSeparatorObserver m_observer;
	private IUltimateServiceProvider m_services;

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
	public List<String> getDesiredToolID() {
		// TODO Auto-generated method stub
		return null;
	}
	@Override
	public void setInputDefinition(ModelType graphType) {
		// TODO Auto-generated method stub
		
	}
	@Override
	public List<IObserver> getObservers() {
		m_observer = new HeapSeparatorObserver(m_services);
		return Collections.singletonList(m_observer);
	}
	@Override
	public void setToolchainStorage(IToolchainStorage storage) {
		// TODO Auto-generated method stub
		
	}
	@Override
	public void setServices(IUltimateServiceProvider services) {
		m_services = services;
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
		return m_observer.getModel();
	}

}
