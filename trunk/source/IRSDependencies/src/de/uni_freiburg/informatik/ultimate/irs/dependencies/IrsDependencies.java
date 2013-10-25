package de.uni_freiburg.informatik.ultimate.irs.dependencies;

import java.util.LinkedList;
import java.util.List;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.IScopeContext;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IAnalysis;
import de.uni_freiburg.informatik.ultimate.irs.dependencies.observers.ASTDependencyFinder;
import de.uni_freiburg.informatik.ultimate.irs.dependencies.observers.DependencyFinder;
import de.uni_freiburg.informatik.ultimate.irs.dependencies.observers.SymbolTableCreator;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.MarkedTrace;
import de.uni_freiburg.informatik.ultimate.model.TokenMap;

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
	public List<MarkedTrace> getMarkedTraces() {
		return null;
	}

	@Override
	public boolean isGuiRequired() {
		return false;
	}

	@Override
	public void setTokenMap(TokenMap tokenMap) {

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
	public IEclipsePreferences[] getPreferences(IScopeContext cs,
			IScopeContext is) {
		return null;
	}

	@Override
	public int init(Object params) {
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

}
