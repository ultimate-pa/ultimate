/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.blockencoding;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.blockencoding.converter.MinModelConverter;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

/**
 * This Observer starts the conversion from our minimized model back to a RCFG.
 * On this generated minimized RCFG the existing model checker, are able to work
 * with.
 * 
 * @author Stefan Wissert
 * 
 */
public class MinModelConversionObserver implements IUnmanagedObserver {

	private IElement mRoot;
	private final Logger mLogger;
	private final IUltimateServiceProvider mServices;

	public MinModelConversionObserver(IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
	}

	@Override
	public void init() {
	}

	@Override
	public void finish() {
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		return null;
	}

	@Override
	public boolean performedChanges() {
		return false;
	}

	@Override
	public boolean process(IElement root) {
		long time = System.currentTimeMillis();
		RootNode rootNode = (RootNode) root;
		mRoot = new MinModelConverter(mServices).startConversion(rootNode);
		mLogger.info("Time (in ms) spend in MinModelConversion: " + (System.currentTimeMillis() - time));
		return false;
	}

	/**
	 * @return the root
	 */
	public IElement getRoot() {
		return mRoot;
	}

}
