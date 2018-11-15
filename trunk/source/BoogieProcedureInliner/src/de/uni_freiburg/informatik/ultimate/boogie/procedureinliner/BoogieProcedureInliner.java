/*
 * Copyright (C) 2014-2015 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE BoogieProcedureInliner plug-in.
 *
 * The ULTIMATE BoogieProcedureInliner plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BoogieProcedureInliner plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogieProcedureInliner plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogieProcedureInliner plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BoogieProcedureInliner plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.preprocessor.TypeChecker;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.IAnalysis;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IObserver;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

/**
 * Tool for inlining Boogie procedures.
 *
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class BoogieProcedureInliner implements IAnalysis {

	private IUltimateServiceProvider mServices;

	@Override
	public ModelType getOutputDefinition() {
		return null;
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
	public List<String> getDesiredToolIds() {
		return null;
	}

	@Override
	public void setInputDefinition(final ModelType graphType) {
		// not necessary
	}

	@Override
	public List<IObserver> getObservers() {
		final ArrayList<IObserver> observers = new ArrayList<>();
		observers.add(new TypeChecker(mServices));
		observers.add(new Inliner(mServices));
		return observers;
	}

	@Override
	public void setToolchainStorage(final IToolchainStorage storage) {
		// not necessary
	}

	@Override
	public void setServices(final IUltimateServiceProvider services) {
		mServices = services;
	}

	@Override
	public void init() {
		// not necessary
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
	public void finish() {
		// not necessary
	}
}
