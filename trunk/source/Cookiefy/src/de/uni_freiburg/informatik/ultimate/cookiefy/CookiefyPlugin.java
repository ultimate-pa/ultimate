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

import de.uni_freiburg.informatik.ultimate.core.model.IGenerator;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IObserver;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

public class CookiefyPlugin implements IGenerator {

	private CookiefyAlgorithm mCookiefyAlgorithm;
	private ModelType mInputType;
	private ILogger mLogger;

	@Override
	public ModelType getOutputDefinition() {
		try {
			return new ModelType(getPluginID(), ModelType.Type.AST, mInputType.getFileNames());
		} catch (final Exception e) {
			return null;
		}
	}

	@Override
	public IElement getModel() {
		return mCookiefyAlgorithm.getRoot();
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
		// don't need a special tool
		return null;
	}

	@Override
	public void setInputDefinition(final ModelType graphType) {
		mInputType = graphType;
	}

	@Override
	public List<IObserver> getObservers() {
		final ArrayList<IObserver> observers = new ArrayList<>();
		// Attention: Every observer here operates on the input
		// model given to the plugin - not the resulting model
		// of the Cookiefy algorithm, even if the observer follows the
		// mCookiefyAlgorithm observer!
		// If you want to print the AST use the BoogiePrinter in the
		// toolchain.
		mCookiefyAlgorithm = new CookiefyAlgorithm(mLogger);
		observers.add(mCookiefyAlgorithm);
		return observers;
	}

	@Override
	public void init() {
		// not needed
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
		return null;
	}

	@Override
	public void setToolchainStorage(final IToolchainStorage services) {
		// not needed
	}

	@Override
	public void setServices(final IUltimateServiceProvider services) {
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);

	}

	@Override
	public void finish() {
		// not needed
	}
}
