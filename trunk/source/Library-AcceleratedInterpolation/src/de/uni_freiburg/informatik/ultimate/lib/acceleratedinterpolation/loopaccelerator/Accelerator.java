/*
 * Copyright (C) 2020 Jonas Werner (wernerj@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE accelerated interpolation library .
 *
 * The ULTIMATE framework is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE framework is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE accelerated interpolation library . If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PDR library , or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE accelerated interpolation library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.loopaccelerator;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.FastUPRCore;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.werner.Backbone;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.werner.Loop;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.werner.LoopAcceleratorLite;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.AcceleratedInterpolation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
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
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de) This class represents the loop accelerator needed for
 *         {@link AcceleratedInterpolation}
 */
public class Accelerator<LETTER extends IIcfgTransition<?>> {
	private final ILogger mLogger;
	private final ManagedScript mScript;
	private final IUltimateServiceProvider mServices;
	private boolean mFoundAcceleration;
	private final IIcfgSymbolTable mSymbolTable;

	public Accelerator(final ILogger logger, final ManagedScript managedScript, final IUltimateServiceProvider services,
			final IIcfgSymbolTable symbolTable) {
		mLogger = logger;
		mScript = managedScript;
		mServices = services;
		mFoundAcceleration = false;
		mSymbolTable = symbolTable;
	}

	/**
	 * Given a loop in form of an {@link UnmodifiableTransFormula} and specifiying which acceleration method, return a
	 * loop acceleration.
	 *
	 * @param loop
	 * @param accelerationMethod
	 * @return
	 */
	public UnmodifiableTransFormula accelerateLoop(final UnmodifiableTransFormula loop, final IcfgLocation loopHead,
			final AcceleratedInterpolation.AccelerationMethod accelerationMethod) {
		switch (accelerationMethod) {
		case NONE:
			break;
		case FAST_UPR:
			return fastUprAcceleration(loop);
		case OVERAPPROXIMATION_WERNER:
			return overapproximationWernerAcceleration(loop, loopHead);
		case UNDERAPPROXIMATION:
			mLogger.warn("Not implmented yet");
			throw new UnsupportedOperationException();
		}
		return loop;
	}

	/**
	 * Accelerate a loop using FastUPR
	 *
	 * @param loop
	 * @return
	 */
	private UnmodifiableTransFormula fastUprAcceleration(final UnmodifiableTransFormula loop) {
		UnmodifiableTransFormula acceleratedLoop;
		try {
			mLogger.debug("Accelerating Loop using FastUPR");
			final FastUPRCore uprCore = new FastUPRCore(loop, mScript, mLogger, mServices);
			acceleratedLoop = uprCore.getResult();
			mFoundAcceleration = true;
			mLogger.debug("Done.");
			return acceleratedLoop;
		} catch (final UnsupportedOperationException ue) {
			/*
			 * Unsupported Operation error because FastUPR could not accelerate the loop. Either return null, to make
			 * the program unknown, or just return the loop for possible worse performance.
			 */
			mFoundAcceleration = false;
			mLogger.info("FastUPR could not accelerate loop because " + ue);
			return loop;
		}
	}

	private UnmodifiableTransFormula overapproximationWernerAcceleration(final UnmodifiableTransFormula loopTf,
			final IcfgLocation loopHead) {
		final Loop loop = new Loop(loopHead, mScript);
		loop.setFormula(loopTf);
		final Backbone backbone = new Backbone(loopTf);
		final Deque<Backbone> backbones = new ArrayDeque<>();
		backbones.add(backbone);
		loop.setBackbones(backbones);

		loop.addExitCondition(loopTf);

		final UnmodifiableTransFormula guard = TransFormulaUtils.computeGuard(loopTf, mScript, mServices, mLogger);
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

	private void underApproxAcceleration(final Map<IcfgLocation, List<LETTER>> loops) {
		throw new UnsupportedOperationException("There is no such acceleration method yet");
	}

	private void overApproxAcceleration(final Map<IcfgLocation, List<LETTER>> loops) {
		throw new UnsupportedOperationException("There is no such acceleration method yet");
	}

	public boolean accelerationFinishedCorrectly() {
		return mFoundAcceleration;
	}
}
