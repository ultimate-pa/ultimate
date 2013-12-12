/**
 * Boogie printer.
 */
package de.uni_freiburg.informatik.ultimate.boogie.printer;

import java.util.Collections;
import java.util.List;


import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.boogie.printer.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IOutput;
import de.uni_freiburg.informatik.ultimate.model.GraphType;

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
	 * de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool#isGuiRequired()
	 */
	@Override
	public boolean isGuiRequired() {
		return false;
	}

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		return new PreferenceInitializer();
	}
}
