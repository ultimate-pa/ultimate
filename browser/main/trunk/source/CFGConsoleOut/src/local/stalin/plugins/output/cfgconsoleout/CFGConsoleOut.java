package local.stalin.plugins.output.cfgconsoleout;

import java.util.Collections;
import java.util.List;

import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.IScopeContext;

import local.stalin.access.IObserver;
import local.stalin.ep.interfaces.IOutput;
import local.stalin.model.GraphType;
import local.stalin.model.MarkedTrace;
import local.stalin.model.TokenMap;

public class CFGConsoleOut implements IOutput {
	
	public final static String PLUGIN_ID = Activator.s_PLUGIN_ID;

	private IObserver mobserver;

	private List<MarkedTrace> m_Traces;
	
	@Override
	public List<String> getDesiredToolID() {
		// Never called
		return null;
	}

	@Override
	public List<IObserver> getObservers() {
		return Collections.singletonList(mobserver);
	}

	@Override
	public QueryKeyword getQueryKeyword() {
		// Use last model
		return QueryKeyword.LAST;
	}

	@Override
	public void setInputDefinition(GraphType graphType) {
		// Do not need this information
	}

	@Override
	public void setTokenMap(TokenMap tokenMap) {
		// Don't need a token map
	}

	@Override
	public String getName() {
		return "CFG Console Output Generator";
	}

	@Override
	public String getPluginID() {
		return PLUGIN_ID;
	}

	@Override
	public int init(Object params) {
		mobserver = new CFGConsoleOutObserver();
		return 0;
	}

	@Override
	public boolean isGuiRequired() {
		return false;
	}

	@Override
	public void setMarkedTraces(List<MarkedTrace> traces) {
		this.m_Traces = traces;
	}

	@Override
	public IEclipsePreferences[] getPreferences(IScopeContext cs, IScopeContext is) {
		return null;
	}

}
