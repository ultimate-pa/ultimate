package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.biesenbach;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IBacktranslationTracker;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

public class IcfgLoopAcceleration<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>
		implements IIcfgTransformer<OUTLOC> {

	private final IIcfg<OUTLOC> mResultIcfg;

	public IcfgLoopAcceleration(final IIcfg<INLOC> originalIcfg, final ILocationFactory<INLOC, OUTLOC> funLocFac,
			final IBacktranslationTracker backtranslationTracker, final Class<OUTLOC> outLocationClass,
			final String newIcfgIdentifier, final ITransformulaTransformer transformer,
			final IUltimateServiceProvider services) {

		mResultIcfg = new LoopDetectionBB<INLOC, OUTLOC>(null, originalIcfg, outLocationClass, funLocFac,
				newIcfgIdentifier, transformer, backtranslationTracker, services).getResult();
	}

	private void createMatrix(final Script script, final IIcfg<OUTLOC> loop) {
		script.assertTerm(mResultIcfg.getInitialNodes().iterator().next().getOutgoingEdges().iterator().next()
				.getTransformula().getFormula());
		
	}

	@Override
	public IIcfg<OUTLOC> getResult() {
		return mResultIcfg;
	}
}