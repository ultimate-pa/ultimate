package de.uni_freiburg.informatik.ultimate.plugins.generator.hornverifier;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.hornverifier.algorithm.HornVerifierStarter;

/**
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class HornVerifierObserver implements IUnmanagedObserver {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	private final List<IIcfg<?>> mIcfgs;
	private IElement mRootOfNewModel;
	private boolean mLastModel;

	public HornVerifierObserver(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mLastModel = false;
		mIcfgs = new ArrayList<>();
	}

	@Override
	public boolean process(final IElement root) {
		if (root instanceof IIcfg<?>) {
			mIcfgs.add((IIcfg<?>) root);
		}
		return false;
	}

	@Override
	public void finish() {
		if (!mLastModel) {
			return;
		}

		if (mIcfgs.isEmpty()) {
			throw new IllegalArgumentException("No ICFG present, Horn Verifier cannot run");
		}
		@SuppressWarnings("unchecked")
		final IIcfg<IcfgLocation> rcfgRootNode = (IIcfg<IcfgLocation>) mIcfgs.stream()
				.filter(a -> IcfgLocation.class.isAssignableFrom(a.getLocationClass())).reduce((a, b) -> b)
				.orElseThrow(UnsupportedOperationException::new);
		if (rcfgRootNode == null) {
			throw new UnsupportedOperationException("Horn Verifier needs an RCFG");
		}
		mLogger.info("Analyzing ICFG " + rcfgRootNode.getIdentifier());
		final HornVerifierStarter starter = new HornVerifierStarter(rcfgRootNode, mServices, mLogger);
		// TODO: Get a model from starter
		mRootOfNewModel = null;
	}

	/**
	 * @return the root of the CFG.
	 */
	public IElement getRootOfNewModel() {
		return mRootOfNewModel;
	}

	@Override
	public void init(final ModelType modelType, final int currentModelIndex, final int numberOfModels) {
		if (currentModelIndex == numberOfModels - 1) {
			mLastModel = true;
		}
	}

	@Override
	public boolean performedChanges() {
		return false;
	}

}
