/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.blockendcoding;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.blockencoding.converter.MinModelConverter;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
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

	private IElement root;

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.access.IObserver#init()
	 */
	@Override
	public void init() {
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.access.IObserver#finish()
	 */
	@Override
	public void finish() {
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.access.IObserver#getWalkerOptions()
	 */
	@Override
	public WalkerOptions getWalkerOptions() {
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.access.IObserver#performedChanges()
	 */
	@Override
	public boolean performedChanges() {
		return false;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver#process
	 * (de.uni_freiburg.informatik.ultimate.model.IElement)
	 */
	@Override
	public boolean process(IElement root) {
		Logger logger = UltimateServices.getInstance().getLogger(
				Activator.s_PLUGIN_ID);
		long time = System.currentTimeMillis();
		RootNode rootNode = (RootNode) root;
		this.root = new MinModelConverter().startConversion(rootNode);
		logger.info("Time (in ms) spend in MinModelConversion: "
				+ (System.currentTimeMillis() - time));
		return false;
	}

	/**
	 * @return the root
	 */
	public IElement getRoot() {
		return root;
	}

}
