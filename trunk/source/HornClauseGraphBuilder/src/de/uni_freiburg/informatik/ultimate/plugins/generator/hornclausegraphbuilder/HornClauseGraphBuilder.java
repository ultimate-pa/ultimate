/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
 * If you modify the ULTIMATE RCFGBuilder plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE HornClauseGraphBuilder plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.hornclausegraphbuilder;

import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.IGenerator;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IObserver;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.hornclausegraphbuilder.preferences.HornClauseGraphBuilderPreferenceInitializer;

public class HornClauseGraphBuilder implements IGenerator {
	
	private static final String s_PLUGIN_NAME = Activator.PLUGIN_NAME;
	public static final String s_PLUGIN_ID = Activator.PLUGIN_ID;
	
	
	private HornClauseGraphBuilderObserver m_Observer;
//	private ModelType m_InputDefinition;

	private IUltimateServiceProvider m_Services;
	private IToolchainStorage m_ToolchainStorage;
	private List<IObserver> m_Observers;

	@Override
	public ModelType getOutputDefinition() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean isGuiRequired() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public ModelQuery getModelQuery() {
		// TODO Auto-generated method stub
		return null;
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
		return m_Observers;
	}

	@Override
	public void setToolchainStorage(IToolchainStorage storage) {
		m_ToolchainStorage = storage;
	}

	@Override
	public void setServices(IUltimateServiceProvider services) {
		m_Services = services;
	}

	@Override
	public void init() {
		m_Observer = new HornClauseGraphBuilderObserver();
		m_Observers = Collections.singletonList(m_Observer);
	}

	@Override
	public void finish() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public String getPluginName() {
		return s_PLUGIN_NAME;
	}

	@Override
	public String getPluginID() {
		return s_PLUGIN_ID;
	}

	@Override
	public IPreferenceInitializer getPreferences() {
		return new HornClauseGraphBuilderPreferenceInitializer();
	}

	@Override
	public IElement getModel() {
		// TODO Auto-generated method stub
		return null;
	}

}
