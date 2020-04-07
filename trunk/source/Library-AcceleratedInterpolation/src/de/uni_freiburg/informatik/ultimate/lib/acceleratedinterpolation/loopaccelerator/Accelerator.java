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

import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.FastUPRCore;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.AcceleratedInterpolation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.NotAffineException;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de) This class represents the loop accelerator needed for
 *         {@link AcceleratedInterpolation}
 */
public class Accelerator<LETTER extends IIcfgTransition<?>> {
	/**
	 * How to deal with procedures.
	 */
	public enum AccelerationMethod {
		NONE, FAST_UPR, OVERAPPROXIMATION, UNDERAPPROXIMATION
	}

	private final ILogger mLogger;
	private final ManagedScript mScript;
	private final IUltimateServiceProvider mServices;

	public Accelerator(final ILogger logger, final ManagedScript managedScript,
			final IUltimateServiceProvider services) {
		mLogger = logger;
		mScript = managedScript;
		mServices = services;
	}

	public UnmodifiableTransFormula accelerateLoop(final UnmodifiableTransFormula loop,
			final AccelerationMethod accelerationMethod) {
		switch (accelerationMethod) {
		case NONE:
			break;
		case FAST_UPR:
			return fastUprAcceleration(loop);
		case OVERAPPROXIMATION:
			break;
		case UNDERAPPROXIMATION:
			break;
		}
		return loop;
	}

	private UnmodifiableTransFormula fastUprAcceleration(final UnmodifiableTransFormula loop) {
		try {
			mLogger.debug("Accelerating Loop using FastUPR");
			final FastUPRCore uprCore = new FastUPRCore(loop, mScript, mLogger, mServices);
			final UnmodifiableTransFormula acceleratedLoop = uprCore.getResult();
			mLogger.debug("Done.");
			return acceleratedLoop;
		} catch (final NotAffineException e) {
			e.printStackTrace();
		}
		return loop;
	}

	private void underApproxAcceleration(final Map<IcfgLocation, List<LETTER>> loops) {
		throw new UnsupportedOperationException("There is no such acceleration method yet");
	}

	private void overApproxAcceleration(final Map<IcfgLocation, List<LETTER>> loops) {
		throw new UnsupportedOperationException("There is no such acceleration method yet");
	}
}
