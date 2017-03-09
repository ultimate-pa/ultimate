package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.biesenbach;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.IBacktranslationTracker;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

public class IcfgLoopAcceleration<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation> implements IIcfgTransformer<OUTLOC> {

	private final IIcfg<OUTLOC> mResultIcfg;
	
	public IcfgLoopAcceleration(final IIcfg<INLOC> originalIcfg, final ILocationFactory<INLOC, OUTLOC> funLocFac,
		final IBacktranslationTracker backtranslationTracker, final Class<OUTLOC> outLocationClass,
		final String newIcfgIdentifier, final ITransformulaTransformer transformer) {
		
		mResultIcfg = new LoopDetectionBB<INLOC, OUTLOC>(null, originalIcfg, outLocationClass, funLocFac,  newIcfgIdentifier, transformer,  backtranslationTracker).getResult();
		System.out.println(mResultIcfg);
	}
	
	private void createMatrix(Script script, IIcfg<OUTLOC> loop){
	}
	
	@Override
	public IIcfg<OUTLOC> getResult() {
		return mResultIcfg;
	}
}