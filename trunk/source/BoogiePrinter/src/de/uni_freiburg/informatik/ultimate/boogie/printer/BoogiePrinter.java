/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2008-2015 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BoogiePrinter plug-in.
 * 
 * The ULTIMATE BoogiePrinter plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BoogiePrinter plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogiePrinter plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogiePrinter plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE BoogiePrinter plug-in grant you additional permission 
 * to convey the resulting work.
 */
/**
 * Boogie printer.
 */
package de.uni_freiburg.informatik.ultimate.boogie.printer;

import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.printer.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.IOutput;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IObserver;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

/**
 * @author hoenicke
 */
public class BoogiePrinter implements IOutput {
	/**
	 * Holds the plugin's name.
	 */
	private static final String sPLUGIN_NAME = "BoogiePrinter";
	/**
	 * Holds the plugin's ID.
	 */
	private static final String sPLUGIN_ID = Activator.s_PLUGIN_ID;
	/**
	 * The observer for this instance.
	 */
	private BoogiePrinterObserver mObserver;
	private IUltimateServiceProvider mServices;

	@Override
	public String getPluginName() {
		return sPLUGIN_NAME;
	}

	@Override
	public String getPluginID() {
		return sPLUGIN_ID;
	}

	@Override
	public void init() {
	}

	@Override
	public ModelQuery getModelQuery() {
		return ModelQuery.LAST;
	}

	@Override
	public List<String> getDesiredToolID() {
		// no special tool needed.
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
	public void setInputDefinition(ModelType graphType) {
		// not required
	}

	@Override
	public List<IObserver> getObservers() {
		mObserver = new BoogiePrinterObserver(mServices.getLoggingService().getLogger(sPLUGIN_ID));
		return Collections.singletonList((IObserver) this.mObserver);
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
		// TODO Auto-generated method stub
		
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
