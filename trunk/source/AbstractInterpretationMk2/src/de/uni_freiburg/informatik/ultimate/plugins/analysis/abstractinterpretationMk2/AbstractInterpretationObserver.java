package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

public class AbstractInterpretationObserver implements IUnmanagedObserver {

	private final IUltimateServiceProvider mServices;
	private final Logger mLogger;

	public AbstractInterpretationObserver(IUltimateServiceProvider services) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(AIActivator.PLUGIN_ID);
	}

	@Override
	public void init(GraphType modelType, int currentModelIndex, int numberOfModels) throws Throwable {

	}

	@Override
	public void finish() throws Throwable {

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
	public boolean process(IElement root) throws Throwable {
		if (root instanceof RootNode) {
			final AbstractInterpreter abstractInterpreter = new AbstractInterpreter(mServices);
//			try {
				abstractInterpreter.processRcfg((RootNode) root);
//			} catch (OutOfMemoryError oom) {
//				throw oom;
//			} catch (Throwable t) {
//				mLogger.fatal("Exception during AIMK2 run: " + t.getMessage());
//			}
			return false;
		}
		return true;
	}
}
