/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Cookiefy plug-in.
 * 
 * The ULTIMATE Cookiefy plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Cookiefy plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Cookiefy plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Cookiefy plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Cookiefy plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cookiefy;

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

public class CookiefyPlugin implements IGenerator {

	private static final String s_PLUGIN_NAME = "Cookiefy";
	private static final String s_PLUGIN_ID = Activator.PLUGIN_ID;

	private CookiefyAlgorithm m_CookiefyAlgorithm;
	private ModelType m_InputType;
	private ILogger mLogger;

	@Override
	public ModelType getOutputDefinition() {
		try {
			return new ModelType(getPluginID(), ModelType.Type.AST, m_InputType.getFileNames());
		} catch (Exception e) {
			return null;
		}
	}

	@Override
	public IElement getModel() {
		return this.m_CookiefyAlgorithm.getRoot();
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
	public List<String> getDesiredToolID() {
		// don't need a special tool
		return null;
	}

	@Override
	public void setInputDefinition(ModelType graphType) {
		this.m_InputType = graphType;
	}

	@Override
	public List<IObserver> getObservers() {
		ArrayList<IObserver> observers = new ArrayList<IObserver>();
		// Attention: Every observer here operates on the input
		// model given to the plugin - not the resulting model
		// of the Cookiefy algorithm, even if the observer follows the
		// m_CookiefyAlgorithm observer!
		// If you want to print the AST use the BoogiePrinter in the
		// toolchain.
		m_CookiefyAlgorithm = new CookiefyAlgorithm(mLogger);
		observers.add(m_CookiefyAlgorithm);
		return observers;
	}

	@Override
	public void init() {
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
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void setToolchainStorage(IToolchainStorage services) {
		// TODO Auto-generated method stub

	}

	@Override
	public void setServices(IUltimateServiceProvider services) {
		mLogger = services.getLoggingService().getLogger(s_PLUGIN_ID);

	}

	@Override
	public void finish() {
		// TODO Auto-generated method stub
		
	}

}
