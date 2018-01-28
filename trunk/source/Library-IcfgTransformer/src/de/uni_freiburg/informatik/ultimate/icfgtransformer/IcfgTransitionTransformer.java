package de.uni_freiburg.informatik.ultimate.icfgtransformer;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.ExampleLoopAccelerationTransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
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
	protected final Map<IIcfgCallTransition<INLOC>, IIcfgCallTransition<OUTLOC>> mOldCallToNewCall;

	protected final IIcfg<INLOC> mInputIcfg;

	private final TransformedIcfgBuilder<INLOC, OUTLOC> mTransformedIcfgBuilder;
	private final BasicIcfg<OUTLOC> mResult;

	private boolean mProcessed;

	public IcfgTransitionTransformer(final ILogger logger, final String resultName,
			final Class<OUTLOC> outLocClazz, final IIcfg<INLOC> inputCfg,
			final ILocationFactory<INLOC, OUTLOC> funLocFac,
			final IBacktranslationTracker backtranslationTracker) {
		assert logger != null;
		mInputCfgCsToolkit = inputCfg.getCfgSmtToolkit();
		mLogger = logger;
		mInputIcfg = inputCfg;

		mMgdScript = mInputCfgCsToolkit.getManagedScript();
		mEdgeFactory = mInputCfgCsToolkit.getIcfgEdgeFactory();

		mOldCallToNewCall = new HashMap<>();

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
	}


	private void process() {
		assert !mProcessed : "only call this once!";
		processGraph();
		mTransformedIcfgBuilder.finish();
		mProcessed = true;
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
					mTransformedIcfgBuilder.createNewTransitionWithNewProgramVars(newSource, newTarget,
							transformedTransition);
				}
			}
		}

		rtrTransitions.forEach(
				a -> mTransformedIcfgBuilder.createNewTransitionWithNewProgramVars(a.getFirst(), a.getSecond(), a.getThird()));
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
		if (oldTransition instanceof IIcfgInternalTransition) {
			// TODO: is this the right payload?
			final IcfgInternalTransition result = mEdgeFactory.createInternalTransition(newSource, newTarget, oldTransition.getPayload(),
					newTransformula);
			log(oldTransition, result);
			return result;
		} else if (oldTransition instanceof IIcfgCallTransition) {
			// TODO: this casting business is ugly like this
			final IIcfgCallTransition<OUTLOC> newCallTransition = (IIcfgCallTransition<OUTLOC>)
					mEdgeFactory.createCallTransition(newSource, newTarget, oldTransition.getPayload(), newTransformula);
			mOldCallToNewCall.put((IIcfgCallTransition<INLOC>) oldTransition, newCallTransition);
			final IcfgEdge result = (IcfgEdge) newCallTransition;
			return result;
		} else if (oldTransition instanceof IIcfgReturnTransition) {
			final IIcfgCallTransition<IcfgLocation> correspondingNewCall =
					(IIcfgCallTransition<IcfgLocation>) mOldCallToNewCall.get(((IIcfgReturnTransition) oldTransition).getCorrespondingCall());
			assert correspondingNewCall != null;
			final IcfgReturnTransition result = mEdgeFactory.createReturnTransition(newSource, newTarget, correspondingNewCall,
					oldTransition.getPayload(), newTransformula, correspondingNewCall.getLocalVarsAssignment());
			return result;
		} else {
			throw new IllegalArgumentException("unknown transition type");
		}
	}

	private void log(final IcfgEdge oldTransition, final IcfgEdge newTransition) {
		mLogger.debug("transformed oldTransition " + oldTransition);
		mLogger.debug("\t  to : " + newTransition);
		mLogger.debug("");
	}


	/**
	 * Triggers the necessary computations (once per instance) and returns the result
	 */
	@Override
	public final IIcfg<OUTLOC> getResult() {
		if (!mProcessed) {
			process();
		}
		return mResult;
	}
}
