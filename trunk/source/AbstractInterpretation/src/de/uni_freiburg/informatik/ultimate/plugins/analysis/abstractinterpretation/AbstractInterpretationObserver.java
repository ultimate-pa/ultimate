package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

public class AbstractInterpretationObserver implements IUnmanagedObserver {

	private final Logger m_logger;
	private final IUltimateServiceProvider mServices;

	public AbstractInterpretationObserver(IUltimateServiceProvider services) {
		mServices = services;
		m_logger = services.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
	}

	@Override
	public void init() throws Throwable {
		// TODO Auto-generated method stub

	}

	@Override
	public void finish() throws Throwable {
		// TODO Auto-generated method stub

	}

	@Override
	public WalkerOptions getWalkerOptions() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean performedChanges() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean process(IElement root) throws Throwable {
		if (root instanceof RootNode) {
			processRootNode((RootNode) root);
			return false;
		}
		return true;
	}

	private void processRootNode(RootNode root) {
		// TODO: Actual stuff ;)
		m_logger.info("Processing a root node...");

		AbstractInterpreter abstractInterpreter = new AbstractInterpreter(mServices);
		abstractInterpreter.processRcfg(root);
	}
}
