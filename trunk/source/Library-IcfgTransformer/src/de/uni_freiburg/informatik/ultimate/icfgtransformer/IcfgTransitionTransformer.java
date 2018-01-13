package de.uni_freiburg.informatik.ultimate.icfgtransformer;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.ExampleLoopAccelerationTransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdgeFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
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

	protected final CfgSmtToolkit mInputCfgCsToolkit;

	protected final IcfgEdgeFactory mEdgeFactory;
	protected final ManagedScript mMgdScript;
	protected final ILogger mLogger;

	/**
	 * TODO: it is important that any override of transform updates this map! (not nice, as it is now..)
	 */
	protected Map<IcfgCallTransition, IcfgCallTransition> mOldCallToNewCall;

	protected final IIcfg<INLOC> mInputIcfg;

	private final TransformedIcfgBuilder<INLOC, OUTLOC> mTransformedIcfgBuilder;
	private final BasicIcfg<OUTLOC> mResult;

	public IcfgTransitionTransformer(final ILogger logger, final String resultName,
			final Class<OUTLOC> outLocClazz, final IIcfg<INLOC> inputCfg,
			final ILocationFactory<INLOC, OUTLOC> funLocFac,
			final IBacktranslationTracker backtranslationTracker) {
		mInputCfgCsToolkit = inputCfg.getCfgSmtToolkit();
		mLogger = logger;
		mInputIcfg = inputCfg;

		mMgdScript = mInputCfgCsToolkit.getManagedScript();
		mEdgeFactory = mInputCfgCsToolkit.getIcfgEdgeFactory();

		/*
		 * the csToolkit will be replaced in mResult by mTransformedIcfgBuilder.finish() (not a fan of this solution..)
		 * the new csToolkit constructed there will get a new symbol table, too..
		 */
		mResult = new BasicIcfg<>(resultName, mInputCfgCsToolkit, outLocClazz);

		final ITransformulaTransformer noopTransformer =
				new ExampleLoopAccelerationTransformulaTransformer(mLogger, mInputCfgCsToolkit.getManagedScript(),
						mInputCfgCsToolkit.getSymbolTable(), new ReplacementVarFactory(mInputCfgCsToolkit, false));
		mTransformedIcfgBuilder = new TransformedIcfgBuilder<>(funLocFac,
				backtranslationTracker, noopTransformer, mInputIcfg, mResult);
		processGraph();
		mTransformedIcfgBuilder.finish();
	}

	private void processGraph() {
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

	/**
	 * Creates a new edge from newSource to newTarget with the unchanged transformula from the input icfg.
	 *
	 * @param oldTransition
	 * @param newSource
	 * @param newTarget
	 * @return
	 */
	protected IcfgEdge transform(final IcfgEdge oldTransition, final OUTLOC newSource, final OUTLOC newTarget) {
		final UnmodifiableTransFormula newTransformula = oldTransition.getTransformula();
		return transform(oldTransition, newSource, newTarget, newTransformula);
	}

	/**
	 *
	 * @param oldTransition
	 * @param newSource
	 * @param newTarget
	 * @param newTransformula
	 * @return
	 */
	protected IcfgEdge transform(final IcfgEdge oldTransition, final OUTLOC newSource, final OUTLOC newTarget,
			final UnmodifiableTransFormula newTransformula) {
		if (oldTransition instanceof IcfgInternalTransition) {
			// TODO: is this the right payload?
			return mEdgeFactory.createInternalTransition(newSource, newTarget, oldTransition.getPayload(),
					newTransformula);
		} else if (oldTransition instanceof IcfgCallTransition) {
			final IcfgCallTransition newCallTransition = mEdgeFactory.createCallTransition(newSource, newTarget,
					oldTransition.getPayload(), newTransformula);
			mOldCallToNewCall.put((IcfgCallTransition) oldTransition, newCallTransition);
			return newCallTransition;
		} else if (oldTransition instanceof IcfgReturnTransition) {
			final IcfgCallTransition correspondingNewCall =
					mOldCallToNewCall.get(((IcfgReturnTransition) oldTransition).getCorrespondingCall());
			assert correspondingNewCall != null;
			return mEdgeFactory.createReturnTransition(newSource, newTarget, correspondingNewCall,
					oldTransition.getPayload(), newTransformula, correspondingNewCall.getLocalVarsAssignment());
		} else {
			throw new IllegalArgumentException("unknown transition type");
		}
	}

	@Override
	public final IIcfg<OUTLOC> getResult() {
		return mResult;
	}
}
