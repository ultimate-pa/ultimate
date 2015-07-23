package de.uni_freiburg.informatik.ultimate.plugins.generator.blockencoding;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.blockencoding.algorithm.BlockEncoder;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

/**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class BlockEncodingObserver implements IUnmanagedObserver {

	private IElement mRoot;
	private final Logger mLogger;
	private final IUltimateServiceProvider m_Services;

	public BlockEncodingObserver(Logger logger, IUltimateServiceProvider services) {
		mLogger = logger;
		m_Services = services;
	}

	@Override
	public boolean process(IElement root) {
		long time = System.currentTimeMillis();
		RootNode rootNode = (RootNode) root;
		new BlockEncoder(mLogger, m_Services).startMinimization(rootNode);
		mLogger.info("Time (in ms) spend in BlockEncoding: " + (System.currentTimeMillis() - time));
		this.mRoot = root;
		return false;
	}

	@Override
	public void init(GraphType modelType, int currentModelIndex, int numberOfModels) {
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
