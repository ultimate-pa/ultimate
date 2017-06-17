/*
 * Copyright (C) 2008-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BoogiePreprocessor plug-in.
 * 
 * The ULTIMATE BoogiePreprocessor plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BoogiePreprocessor plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogiePreprocessor plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogiePreprocessor plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BoogiePreprocessor plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.preprocessor;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTableConstructor;
import de.uni_freiburg.informatik.ultimate.core.model.IAnalysis;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IObserver;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

/**
 * This class initializes the boogie preprocessor.
 * 
 * @author hoenicke
 * @author dietsch@informatik.uni-freiburg.de (for backtranslation)
 * 
 */
public class BoogiePreprocessor implements IAnalysis {

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
		// not needed
	}

	/**
	 * I give you every model.
	 */
	@Override
	public ModelQuery getModelQuery() {
		return ModelQuery.LAST;
	}

	/**
	 * I don't need a special tool
	 */
	@Override
	public List<String> getDesiredToolIds() {
		return Collections.emptyList();
	}

	@Override
	public ModelType getOutputDefinition() {
		/* use old graph type definition */
		return null;
	}

	@Override
	public void setInputDefinition(final ModelType graphType) {
		// not required.
	}

	// @Override
	@Override
	public List<IObserver> getObservers() {
		final BoogiePreprocessorBacktranslator backTranslator = new BoogiePreprocessorBacktranslator(mServices);
		mServices.getBacktranslationService().addTranslator(backTranslator);

		final ILogger logger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);

		final BoogieSymbolTableConstructor symb = new BoogieSymbolTableConstructor(logger);
		backTranslator.setSymbolTable(symb.getSymbolTable());

		final ArrayList<IObserver> observers = new ArrayList<>();
		observers.add(new EnsureBoogieModelObserver());
		// You can use the DebugObserver here if needed
		observers.add(new TypeChecker(mServices));
		observers.add(new ConstExpander(backTranslator));
		observers.add(new StructExpander(backTranslator, logger));
		observers.add(new UnstructureCode(backTranslator));
		observers.add(new FunctionInliner());
		observers.add(symb);
		return observers;
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
	public void setToolchainStorage(final IToolchainStorage storage) {
		// storage is not used by this plugin
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
