package de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.loopaccelerator;

import java.util.ArrayDeque;
import java.util.Deque;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.werner.Backbone;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.werner.Loop;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.werner.LoopAcceleratorLite;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.werner.WernerLoopAccelerationIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.AcceleratedInterpolation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * A loop accelerator used in accelerated inteprolation using the {@link WernerLoopAccelerationIcfgTransformer} method
 * of acceleration.
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de) This class represents the loop accelerator needed for
 *         {@link AcceleratedInterpolation}
 */
public class AcceleratorWernerOverapprox implements IAccelerator {

	private final ILogger mLogger;
	private final ManagedScript mScript;
	private final IUltimateServiceProvider mServices;
	private boolean mFoundAcceleration;
	private final IIcfgSymbolTable mSymbolTable;
	private final boolean mIsOverapprox;

	/**
	 * Construct a new loop accelerator using {@link WernerLoopAccelerationIcfgTransformer}.
	 *
	 * @param logger
	 *            A {@link ILogger}
	 * @param managedScript
	 *            A {@link ManagedScript}
	 * @param services
	 *            {@link IUltimateServiceProvider}
	 * @param symbolTable
	 *            {@link IIcfgSymbolTable}
	 */
	public AcceleratorWernerOverapprox(final ILogger logger, final ManagedScript managedScript,
			final IUltimateServiceProvider services, final IIcfgSymbolTable symbolTable) {
		mLogger = logger;
		mScript = managedScript;
		mServices = services;
		mFoundAcceleration = false;
		mSymbolTable = symbolTable;
		mIsOverapprox = true;
	}

	@Override
	public UnmodifiableTransFormula accelerateLoop(final UnmodifiableTransFormula loopTf, final IcfgLocation loopHead) {
		final Loop loop = new Loop(loopHead, mScript);
		loop.setFormula(loopTf);
		final Backbone backbone = new Backbone(loopTf);
		final Deque<Backbone> backbones = new ArrayDeque<>();
		backbones.add(backbone);
		loop.setBackbones(backbones);
		loop.addExitCondition(loopTf);
		final UnmodifiableTransFormula guard = TransFormulaUtils.computeGuard(loopTf, mScript, mServices);
		loop.setCondition(guard.getFormula());

		final LoopAcceleratorLite lite = new LoopAcceleratorLite(mScript, mServices, mLogger, mSymbolTable);
		UnmodifiableTransFormula wernerAcceleration = lite.summarizeLoop(loop);

		final Term wernerAccelerationTerm = SmtUtils.quantifier(mScript.getScript(), QuantifiedFormula.EXISTS,
				wernerAcceleration.getAuxVars(), wernerAcceleration.getFormula());

		final TransFormulaBuilder tfb = new TransFormulaBuilder(wernerAcceleration.getInVars(),
				wernerAcceleration.getOutVars(), true, null, true, null, true);
		tfb.setFormula(wernerAccelerationTerm);
		tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
		wernerAcceleration = tfb.finishConstruction(mScript);
		mFoundAcceleration = true;
		mLogger.debug("Quantified Werner Acceleration");
		return wernerAcceleration;
	}

	@Override
	public boolean accelerationFinishedCorrectly() {
		return mFoundAcceleration;
	}

	@Override
	public boolean isOverapprox() {
		return mIsOverapprox;
	}

}
