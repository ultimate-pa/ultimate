package local.stalin.boogie.printer;

import java.util.Collections;
import java.util.List;

import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.IScopeContext;

import local.stalin.access.IObserver;
import local.stalin.ep.interfaces.IOutput;
import local.stalin.model.GraphType;
import local.stalin.model.MarkedTrace;
import local.stalin.model.TokenMap;

public class BoogiePrinter  implements IOutput {

	private static final String s_PLUGIN_NAME = "BoogiePrinter";
	private static final String s_PLUGIN_ID = Activator.s_PLUGIN_ID;
	
	private BoogiePrinterObserver m_Observer;

	
    public String getName() {
        return s_PLUGIN_NAME;
    }

    public String getPluginID() {
        return s_PLUGIN_ID;
    }

    public int init(Object param) {
    	m_Observer = new BoogiePrinterObserver();
    	return 0;
    }

	/**
	 * I give you every model.
	 */
	public QueryKeyword getQueryKeyword() {
		return QueryKeyword.USER;
	}

	/**
	 * I don't need a special tool
	 */
	public List<String> getDesiredToolID() {
		return null;
	}

	/**
	 * I don't use the TokenMap right now.
	 */
	public void setTokenMap(TokenMap tokenMap) {
	}

	public GraphType getOutputDefinition() {
		return null;
	}

	public void setInputDefinition(GraphType graphType) {
	}

	//@Override
	public List<IObserver> getObservers() {
		return Collections.singletonList((IObserver) m_Observer);
	}

	@Override
	public void setMarkedTraces(List<MarkedTrace> traces) {
		/* ignore marked traces */
		return;
	}

	@Override
	public boolean isGuiRequired() {
		return false;
	}

	@Override
	public IEclipsePreferences[] getPreferences(IScopeContext cs, IScopeContext is) {
		return null;
	}
}
