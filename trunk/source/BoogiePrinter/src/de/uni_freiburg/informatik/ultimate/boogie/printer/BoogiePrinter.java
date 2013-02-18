/**
 * Boogie printer.
 */
package de.uni_freiburg.informatik.ultimate.boogie.printer;

import java.util.Collections;
import java.util.List;

import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.IScopeContext;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IOutput;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.MarkedTrace;
import de.uni_freiburg.informatik.ultimate.model.TokenMap;

/**
 * @author hoenicke
 */
public class BoogiePrinter implements IOutput {
	/**
	 * Holds the plugin's name.
	 */
	private static final String s_PLUGIN_NAME = "BoogiePrinter";
	/**
	 * Holds the plugin's ID.
	 */
	private static final String s_PLUGIN_ID = Activator.s_PLUGIN_ID;
	/**
	 * The observer for this instance.
	 */
	private BoogiePrinterObserver m_Observer;

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.ep.interfaces.IRCPPlugin#getName()
	 */
	@Override
	public String getName() {
		return s_PLUGIN_NAME;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.ep.interfaces.IRCPPlugin#getPluginID
	 * ()
	 */
	@Override
	public String getPluginID() {
		return s_PLUGIN_ID;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.ep.interfaces.IRCPPlugin#init(java
	 * .lang.Object)
	 */
	@Override
	public int init(Object param) {
		this.m_Observer = new BoogiePrinterObserver();
		return 0;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool#getQueryKeyword()
	 */
	@Override
	public QueryKeyword getQueryKeyword() {
		return QueryKeyword.LAST;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool#getDesiredToolID
	 * ()
	 */
	@Override
	public List<String> getDesiredToolID() {
		// no special tool needed.
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool#setTokenMap(de
	 * .uni_freiburg.informatik.ultimate.model.TokenMap)
	 */
	@Override
	public void setTokenMap(TokenMap tokenMap) {
		// not required | not used right now
	}

	/**
	 * Getter for GraphType.
	 * 
	 * @return the graph type.
	 */
	public GraphType getOutputDefinition() {
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool#setInputDefinition
	 * (de.uni_freiburg.informatik.ultimate.model.GraphType)
	 */
	@Override
	public void setInputDefinition(GraphType graphType) {
		// not required
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool#getObservers()
	 */
	@Override
	public List<IObserver> getObservers() {
		return Collections.singletonList((IObserver) this.m_Observer);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.ep.interfaces.IOutput#setMarkedTraces
	 * (java.util.List)
	 */
	@Override
	public void setMarkedTraces(List<MarkedTrace> traces) {
		/* ignore marked traces */
		return;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool#isGuiRequired()
	 */
	@Override
	public boolean isGuiRequired() {
		return false;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool#getPreferences
	 * (org.eclipse.core.runtime.preferences.IScopeContext,
	 * org.eclipse.core.runtime.preferences.IScopeContext)
	 */
	@Override
	public IEclipsePreferences[] getPreferences(IScopeContext cs,
			IScopeContext is) {
		return null;
	}
}
