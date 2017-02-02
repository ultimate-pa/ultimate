/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 Sergio Feo Arenis (arenis@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE DSInvariantASTTransformer plug-in.
 * 
 * The ULTIMATE DSInvariantASTTransformer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE DSInvariantASTTransformer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE DSInvariantASTTransformer plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE DSInvariantASTTransformer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE DSInvariantASTTransformer plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.dsitransformer;

import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.IGenerator;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IObserver;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

/**
 * This Class transforms a Boogie AST into a new one to generate data structure invariants
 * 
 * @author arenis
 * 
 */

public class DSITransformer implements IGenerator {

	private DSITransformerObserver mObserver;
	private ModelType mInputType;
	private IUltimateServiceProvider mServices;

	/**
	 * I don't need a special tool
	 */
	@Override
	public List<String> getDesiredToolIds() {
		return null;
	}

	@Override
	public IElement getModel() {
		return mObserver.getRoot();
	}

	@Override
	public String getPluginName() {
		return "DSITransformer";
	}

	@Override
	public List<IObserver> getObservers() {
		mObserver = new DSITransformerObserver(mServices.getLoggingService().getLogger(Activator.PLUGIN_ID), mServices);
		return Collections.singletonList((IObserver) mObserver);
	}

	@Override
	public ModelType getOutputDefinition() {
		try {
			return new ModelType(getPluginID(), ModelType.Type.AST, mInputType.getFileNames());
		} catch (final Exception e) {
			return null;
		}
	}

	@Override
	public String getPluginID() {
		return Activator.PLUGIN_ID;
	}

	/**
	 * I give you every model.
	 */
	@Override
	public ModelQuery getModelQuery() {
		return ModelQuery.LAST;
	}

	@Override
	public void init() {
	}

	@Override
	public boolean isGuiRequired() {
		return false;
	}

	@Override
	public void setInputDefinition(ModelType graphType) {
		mInputType = graphType;
	}

	@Override
	public IPreferenceInitializer getPreferences() {
		// TODO Auto-generated method stub
		return null;
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
