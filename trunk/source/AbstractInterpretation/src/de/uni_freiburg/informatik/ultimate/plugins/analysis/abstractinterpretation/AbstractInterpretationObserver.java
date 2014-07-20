package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.result.NoResult;

public class AbstractInterpretationObserver implements IUnmanagedObserver {

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
		AbstractInterpreter.getLogger().info("Processing a root node...");
		
		AbstractInterpreter abstractInterpreter = new AbstractInterpreter();
		abstractInterpreter.processRcfg(root);

		UltimateServices.getInstance().reportResult(Activator.s_PLUGIN_ID,
				new NoResult<IElement>(root, Activator.s_PLUGIN_ID,
						UltimateServices.getInstance().getTranslatorSequence()));
	}
}
