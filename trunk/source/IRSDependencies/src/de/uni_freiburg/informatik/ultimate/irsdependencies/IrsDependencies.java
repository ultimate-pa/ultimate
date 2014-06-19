package de.uni_freiburg.informatik.ultimate.irsdependencies;

import java.util.LinkedList;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IAnalysis;
import de.uni_freiburg.informatik.ultimate.irsdependencies.observers.DependencyFinder;
import de.uni_freiburg.informatik.ultimate.irsdependencies.observers.SymbolTableCreator;
import de.uni_freiburg.informatik.ultimate.irsdependencies.preferences.IRSDependenciesPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.model.GraphType;

public class IrsDependencies implements IAnalysis {

	protected final static Logger sLogger = UltimateServices.getInstance()
			.getLogger(Activator.PLUGIN_ID);
	protected final List<IObserver> mObservers;
	protected final SymbolTableCreator mSymbolTableCreator;

	public IrsDependencies() {
		mObservers = new LinkedList<IObserver>();
		mSymbolTableCreator = new SymbolTableCreator();
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
		sLogger.info("Receiving input definition " + graphType.toString());
		mObservers.clear();
	
		IRSDependenciesPreferenceInitializer.Mode mode = IRSDependenciesPreferenceInitializer.getMode();
		
		switch(mode){
		case Default:
			setInputDefinitionModeDefault(graphType);
			break;
		default:
			String errorMsg = "Unknown mode: "+mode; 
			sLogger.fatal(errorMsg);
			throw new IllegalArgumentException(errorMsg);
		}
	}
	
	private void setInputDefinitionModeDefault(GraphType graphType){
		switch (graphType.getCreator()) {
		case "RCFGBuilder":
			sLogger.info("Preparing to process RCFG...");
			mObservers.add(new DependencyFinder());
			
			break;
//		case "BoogiePLCupParser":
//			sLogger.debug("bpl");
//			mObservers.add(mSymbolTableCreator);
//			mObservers.add(new ASTDependencyFinder(mSymbolTableCreator
//					.getSymbolTable(),1));
//			break;
		default:
			sLogger.warn("Ignoring input definition");
		}
	}

	@Override
	public List<IObserver> getObservers() {
		return mObservers;
	}

	@Override
	public int init() {
		return 0;
	}

	@Override
	public String getName() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public String getPluginID() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		return new IRSDependenciesPreferenceInitializer();
	}

}
