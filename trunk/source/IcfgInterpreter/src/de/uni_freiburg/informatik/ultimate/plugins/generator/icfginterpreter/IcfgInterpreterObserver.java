package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

public class IcfgInterpreterObserver extends BaseObserver {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private IIcfg<? extends IcfgLocation> mIcfg;
	private static IcfgInterpreterObserver instance = null;

	public IcfgInterpreterObserver(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		instance = this;
	}

	public static ILogger getLogger() {
		return instance == null ? null : instance.mLogger;
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
		if (mIcfg == null) {
			return;
		}
		// TODO: Extract executions from mIcfg (mServices will be also needed for some operations)
		// This should be probably moved to a separate class

		// Useful methods:
		// * mIcfg.getCfgSmtToolkit().getManagedScript()
		// (also .getScript() if the Script instead of the ManagedScript is needed)
		// * mIcfg.getInitialNodes()
		// * TransFormulaUtils.computeGuard
		// * SmtUtils.getConjuncts
		// * SmtUtils.toDnf
		// * mLogger can be used for output (e.g., for debugging)

		ExecutionProducer.makeExecutions(mIcfg, mServices, mLogger);
	}

	public IElement getRootOfNewModel() {
		// TODO: We want to return executions instead (for now we can also just log them, but e.g., to give the
		// execution to other plugins)
		return mIcfg;
	}
}
