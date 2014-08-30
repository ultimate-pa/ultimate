package de.uni_freiburg.informatik.ultimate.plugins.generator.blockencoding;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.blockencoding.algorithm.BlockEncoder;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

/**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class BlockEncodingObserver implements IUnmanagedObserver {

	private IElement mRoot;
	private Logger mLogger;

	public BlockEncodingObserver(Logger logger) {
		mLogger = logger;
	}

	@Override
	public boolean process(IElement root) {
		long time = System.currentTimeMillis();
		RootNode rootNode = (RootNode) root;
		new BlockEncoder(mLogger).startMinimization(rootNode);
		mLogger.info("Time (in ms) spend in BlockEncoding: " + (System.currentTimeMillis() - time));
		this.mRoot = root;
		return false;
	}

	@Override
	public void init() {
		// not required
	}

	@Override
	public void finish() {
		// not required
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		return null;
	}

	@Override
	public boolean performedChanges() {
		return false;
	}

	/**
	 * @return the root
	 */
	public IElement getRoot() {
		return mRoot;
	}

}
