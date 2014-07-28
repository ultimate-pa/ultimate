/**
 * Boogie printer.
 */
package de.uni_freiburg.informatik.ultimate.boogie.printer;

import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.boogie.printer.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IOutput;
import de.uni_freiburg.informatik.ultimate.model.GraphType;

/**
 * @author hoenicke
 */
public class BoogiePrinter implements IOutput {
	/**
	 * Holds the plugin's name.
	 */
	private static final String sPLUGIN_NAME = "BoogiePrinter";
	/**
	 * Holds the plugin's ID.
	 */
	private static final String sPLUGIN_ID = Activator.s_PLUGIN_ID;
	/**
	 * The observer for this instance.
	 */
	private BoogiePrinterObserver mObserver;
	private IUltimateServiceProvider mServices;

	@Override
	public String getPluginName() {
		return sPLUGIN_NAME;
	}

	@Override
	public String getPluginID() {
		return sPLUGIN_ID;
	}

	@Override
	public int init() {
		return 0;
	}

	@Override
	public QueryKeyword getQueryKeyword() {
		return QueryKeyword.LAST;
	}

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

	@Override
	public void setInputDefinition(GraphType graphType) {
		// not required
	}

	@Override
	public List<IObserver> getObservers() {
		mObserver = new BoogiePrinterObserver(mServices.getLoggingService().getLogger(sPLUGIN_ID));
		return Collections.singletonList((IObserver) this.mObserver);
	}

	@Override
	public boolean isGuiRequired() {
		return false;
	}

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		return new PreferenceInitializer();
	}

	@Override
	public void setToolchainStorage(IToolchainStorage services) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setServices(IUltimateServiceProvider services) {
		mServices = services;
	}
}
