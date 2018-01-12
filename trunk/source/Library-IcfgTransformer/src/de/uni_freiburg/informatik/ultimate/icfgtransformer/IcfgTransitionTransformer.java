package de.uni_freiburg.informatik.ultimate.icfgtransformer;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.ExampleLoopAccelerationTransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdgeFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <INLOC>
 * @param <OUTLOC>
 */
public abstract class IcfgTransitionTransformer<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>
	implements IIcfgTransformer<OUTLOC> {

	protected final CfgSmtToolkit mCsToolkit;

	protected final IcfgEdgeFactory mEdgeFactory;
	protected final ManagedScript mMgdScript;
	protected final ILogger mLogger;

	private final IIcfg<INLOC> mInputIcfg;

	private final TransformedIcfgBuilder<INLOC, OUTLOC> mTransformedIcfgBuilder;
	private final BasicIcfg<OUTLOC> mResult;

	public IcfgTransitionTransformer(final ILogger logger, final CfgSmtToolkit csToolkit, final String resultName,
			final Class<OUTLOC> outLocClazz, final IIcfg<INLOC> inputCfg, final ILocationFactory<INLOC, OUTLOC> funLocFac,
			final IBacktranslationTracker backtranslationTracker) {
		mCsToolkit = csToolkit;
		mLogger = logger;
		mInputIcfg = inputCfg;

		mMgdScript = csToolkit.getManagedScript();
		mEdgeFactory = csToolkit.getIcfgEdgeFactory();

		mResult = new BasicIcfg<>(resultName, mCsToolkit, outLocClazz);

		final ITransformulaTransformer noopTransformer =
				new ExampleLoopAccelerationTransformulaTransformer(mLogger, mCsToolkit.getManagedScript(),
						mCsToolkit.getSymbolTable(), new ReplacementVarFactory(mCsToolkit, false));
		mTransformedIcfgBuilder = new TransformedIcfgBuilder<>(funLocFac,
				backtranslationTracker, noopTransformer, mInputIcfg, mResult);
		computeResult();
	}

	private void computeResult() {
		// we need to create new return transitions after new call transitions have been created
		final List<Triple<OUTLOC, OUTLOC, IcfgEdge>> rtrTransitions = new ArrayList<>();

		final IcfgLocationIterator<INLOC> iter = new IcfgLocationIterator<>(mInputIcfg.getInitialNodes());
		while (iter.hasNext()) {
			final INLOC oldSource = iter.next();
			final OUTLOC newSource = mTransformedIcfgBuilder.createNewLocation(oldSource);
			for (final IcfgEdge oldTransition : oldSource.getOutgoingEdges()) {
				@SuppressWarnings("unchecked")
				final OUTLOC newTarget = mTransformedIcfgBuilder.createNewLocation((INLOC) oldTransition.getTarget());

				final IcfgEdge transformedTransition = transform(oldTransition, newSource, newTarget);

				if (oldTransition instanceof IIcfgReturnTransition<?, ?>) {
					rtrTransitions.add(new Triple<>(newSource, newTarget, transformedTransition));
				} else {
					mTransformedIcfgBuilder.createNewTransition(newSource, newTarget, transformedTransition);
				}
			}
		}

		rtrTransitions.forEach(
				a -> mTransformedIcfgBuilder.createNewTransition(a.getFirst(), a.getSecond(), a.getThird()));
	}

	protected abstract IcfgEdge transform(IcfgEdge oldTransition, OUTLOC newSource, OUTLOC newTarget);


	@Override
	public final IIcfg<OUTLOC> getResult() {
		return mResult;
	}
}
