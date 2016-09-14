/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE IRSDependencies plug-in.
 * 
 * The ULTIMATE IRSDependencies plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE IRSDependencies plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IRSDependencies plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IRSDependencies plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IRSDependencies plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies;

import java.util.LinkedList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.IAnalysis;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IObserver;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector.RCFGLoopDetectorObserver;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.preferences.IRSDependenciesPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.preferences.IRSDependenciesPreferenceInitializer.Mode;

public class IrsDependencies implements IAnalysis {

	private ILogger mLogger;
	private final List<IObserver> mObservers;
	private IUltimateServiceProvider mServices;

	public IrsDependencies() {
		mObservers = new LinkedList<IObserver>();
	}

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
		return ModelQuery.ALL;
	}

	@Override
	public List<String> getDesiredToolID() {
		return null;
	}

	@Override
	public void setInputDefinition(final ModelType graphType) {
		mLogger.info("Receiving input definition " + graphType.toString());
		mObservers.clear();

		final IRSDependenciesPreferenceInitializer.Mode mode = mServices.getPreferenceProvider(Activator.PLUGIN_ID)
				.getEnum(IRSDependenciesPreferenceInitializer.MODE, Mode.class);

		switch (mode) {
		case Default:
			setInputDefinitionModeDefault(graphType);
			break;
		default:
			final String errorMsg = "Unknown mode: " + mode;
			mLogger.fatal(errorMsg);
			throw new IllegalArgumentException(errorMsg);
		}
	}

	private void setInputDefinitionModeDefault(final ModelType graphType) {
		final String creator = graphType.getCreator();
		switch (creator) {
		case "de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder":
			mLogger.info("Preparing to process RCFG...");
			mObservers.add(new RCFGLoopDetectorObserver(mServices));

			break;
		// case "BoogiePLCupParser":
		// sLogger.debug("bpl");
		// mObservers.add(mSymbolTableCreator);
		// mObservers.add(new ASTDependencyFinder(mSymbolTableCreator
		// .getSymbolTable(),1));
		// break;
		default:
			mLogger.warn("Ignoring input definition " + creator);
			break;
		}
	}

	@Override
	public List<IObserver> getObservers() {
		return mObservers;
	}

	@Override
	public void init() {
		// no init needed
	}

	@Override
	public String getPluginName() {
		return "IRS Dependencies";
	}

	@Override
	public String getPluginID() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public IPreferenceInitializer getPreferences() {
		return new IRSDependenciesPreferenceInitializer();
	}

	@Override
	public void setToolchainStorage(final IToolchainStorage services) {
		// no storage needed
	}

	@Override
	public void setServices(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public void finish() {
		// no finish needed
	}

}
