package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies;

import java.util.LinkedList;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IAnalysis;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector.LoopDetector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.observers.DependencyFinder;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.preferences.IRSDependenciesPreferenceInitializer;

public class IrsDependencies implements IAnalysis {

	protected Logger mLogger;
	protected final List<IObserver> mObservers;
	private IUltimateServiceProvider mServices;

	public IrsDependencies() {
		mObservers = new LinkedList<IObserver>();
	}

	@Override
	public GraphType getOutputDefinition() {
		return null;
	}

	@Override
	public boolean isGuiRequired() {
		return false;
	}

	@Override
	public QueryKeyword getQueryKeyword() {
		return QueryKeyword.ALL;
	}

	@Override
	public List<String> getDesiredToolID() {
		return null;
	}

	@Override
	public void setInputDefinition(GraphType graphType) {
		mLogger.info("Receiving input definition " + graphType.toString());
		mObservers.clear();

		IRSDependenciesPreferenceInitializer.Mode mode = IRSDependenciesPreferenceInitializer.getMode();

		switch (mode) {
		case Default:
			setInputDefinitionModeDefault(graphType);
			break;
		default:
			String errorMsg = "Unknown mode: " + mode;
			mLogger.fatal(errorMsg);
			throw new IllegalArgumentException(errorMsg);
		}
	}

	private void setInputDefinitionModeDefault(GraphType graphType) {
		String creator = graphType.getCreator();
		switch (creator) {
		case "de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder":
			mLogger.info("Preparing to process RCFG...");
			mObservers.add(new LoopDetector(mServices));

			break;
		// case "BoogiePLCupParser":
		// sLogger.debug("bpl");
		// mObservers.add(mSymbolTableCreator);
		// mObservers.add(new ASTDependencyFinder(mSymbolTableCreator
		// .getSymbolTable(),1));
		// break;
		default:
			mLogger.warn("Ignoring input definition " + creator);
		}
	}

	@Override
	public List<IObserver> getObservers() {
		return mObservers;
	}

	@Override
	public void init() {
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
	public UltimatePreferenceInitializer getPreferences() {
		return new IRSDependenciesPreferenceInitializer();
	}

	@Override
	public void setToolchainStorage(IToolchainStorage services) {
		// TODO Auto-generated method stub

	}

	@Override
	public void setServices(IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public void finish() {
		// TODO Auto-generated method stub
		
	}

}
