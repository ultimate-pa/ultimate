package de.uni_freiburg.informatik.ultimate.plugins.generator.blockendcoding;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.blockencoding.algorithm.BlockEncoder;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.metrics.RatingFactory.RatingStrategy;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.blockendcoding.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

/**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class BlockEncodingObserver implements IUnmanagedObserver {

	private IElement root;

	@Override
	public boolean process(IElement root) {
		Logger logger = UltimateServices.getInstance().getLogger(
				Activator.s_PLUGIN_ID);
		long time = System.currentTimeMillis();
		RootNode rootNode = (RootNode) root;
		new BlockEncoder().startMinimization(rootNode);
		logger.info("Time (in ms) spend in BlockEncoding: "
				+ (System.currentTimeMillis() - time));
		this.root = root;
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
		return root;
	}

}
