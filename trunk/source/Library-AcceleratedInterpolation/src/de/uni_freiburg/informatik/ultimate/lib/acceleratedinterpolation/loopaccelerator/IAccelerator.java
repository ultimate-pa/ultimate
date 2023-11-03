/*
 * Copyright (C) 2021 Jonas Werner (wernerj@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;

/**
 * Interface for a loop accelerator.
 *
 * @author Jonas Werner <wernerj@informatik.uni-freiburg.de>
 */
public interface IAccelerator {

	/**
	 * Compute a loop acceleration.
	 *
	 * @param loop
	 *            The loop's {@link UnmodifiableTransFormula}
	 * @param loopHead
	 *            The location in the program's {@link IIcfg} where the loop begins.
	 * @return A loop acceleration in form of a {@link UnmodifiableTransFormula}
	 */
	UnmodifiableTransFormula accelerateLoop(UnmodifiableTransFormula loop, final IcfgLocation loopHead);

	/**
	 * Signals the correct exit of the acceleration method.
	 *
	 * @return True when the acceleration method successfully compute an adequate loop acceleration.
	 */
	boolean accelerationFinishedCorrectly();

	/**
	 * Signals whether the computed acceleration is an overapproximation.
	 *
	 * @return
	 */
	boolean isOverapprox();
}
