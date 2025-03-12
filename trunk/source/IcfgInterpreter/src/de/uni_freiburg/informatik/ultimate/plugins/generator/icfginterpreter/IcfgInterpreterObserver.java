package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;

public class IcfgInterpreterObserver extends BaseObserver {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private IIcfg<?> mIcfg;

	public IcfgInterpreterObserver(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public boolean process(final IElement root) throws Throwable {
		if (root instanceof final IIcfg<?> icfg) {
			if (mIcfg != null) {
				throw new UnsupportedOperationException("Multiple CFGs are not supported.");
			}
			mIcfg = icfg;
		}
		return false;
	}

	@Override
	public void finish() {
		// TODO: Extract executions from mIcfg (mServices will be also needed for some operations)
		// This should be probably moved to a separate class

		// Useful methods:
		// * mIcfg.getCfgSmtToolkit().getManagedScript()
		// (also .getScript() if the Script instead of the ManagedScript is needed)
		// * mIcfg.getInitialNodes()
		// * TransFormulaUtils.computeGuard
		// * SmtUtils.getConjuncts
		// * mLogger can be used for output (e.g., for debugging)
	}

	public IElement getRootOfNewModel() {
		// TODO: We want to return executions instead (for now we can also just log them, but e.g., to give the
		// execution to other plugins)
		return mIcfg;
	}
}
