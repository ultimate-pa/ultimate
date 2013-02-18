package local.stalin.plugins.output.nodecounter;

import java.util.Collections;
import java.util.List;

import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.IScopeContext;

import local.stalin.access.IObserver;
import local.stalin.ep.interfaces.IOutput;
import local.stalin.model.GraphType;
import local.stalin.model.MarkedTrace;
import local.stalin.model.TokenMap;

public class NodeCounter implements IOutput {
	
	public final static String PLUGIN_ID = Activator.PLUGIN_ID;

	private NodeCounterObserver mobserver;
	
	@Override
	public List<String> getDesiredToolID() {
		// Never called
		return null;
	}

	@Override
	public List<IObserver> getObservers() {
		return Collections.singletonList((IObserver)mobserver);
	}

	@Override
	public QueryKeyword getQueryKeyword() {
		// Use last model
		return QueryKeyword.LAST;
	}

	@Override
	public void setInputDefinition(GraphType graphType) {
		mobserver.setLoopCheck(graphType.isCyclic());
	}

	@Override
	public void setTokenMap(TokenMap tokenMap) {
		// Don't need a token map
	}

	@Override
	public String getName() {
		return "Node Counter";
	}

	@Override
	public String getPluginID() {
		return PLUGIN_ID;
	}

	@Override
	public int init(Object params) {
		mobserver = new NodeCounterObserver();
		return 0;
	}

	@Override
	public void setMarkedTraces(List<MarkedTrace> traces) {
		// Marking does not make any sence if we count nodes...
	}

	@Override
	public boolean isGuiRequired() {
		// We print to logger. This does not need any GUI stuff!
		return false;
	}

	@Override
	public IEclipsePreferences[] getPreferences(IScopeContext cs, IScopeContext is) {
		return null;
	}

}
