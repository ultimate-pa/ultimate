/*
 * Copyright (C) 2021 Jonas Werner (wernerj@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.qvasr;

import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;

/**
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de) This class represents a rational vaector addition system
 *         with resets abstraction (Q-Vasr-abstraction). It is used to overapproximate changes to variables by a
 *         transition formula by linear simulating the formula onto a {@link Qvasr}.
 *
 */

public class QvasrAbstraction {

	private final Rational[][] mSimulationMatrix;
	private final Qvasr mQvasr;

	/**
	 * Construct a new Q-Vasr-abstraction (S, V), which overapproximates a {@link UnmodifiableTransFormula} F by using
	 * linear matrix S to simulate F to the {@link Qvasr} V.
	 *
	 * @param initialSimulationMatrix
	 * @param initialQvasr
	 */
	public QvasrAbstraction(final Rational[][] initialSimulationMatrix, final Qvasr initialQvasr) {
		mSimulationMatrix = initialSimulationMatrix;
		mQvasr = initialQvasr;
	}

	/**
	 * Return this abstractions simulation matrix.
	 *
	 * @return
	 */
	public Rational[][] getSimulationMatrix() {
		return mSimulationMatrix;
	}

	/**
	 * Return the Q-Vasr on to which a transition formula is simulated.
	 *
	 * @return
	 */
	public Qvasr getQvasr() {
		return mQvasr;
	}

	/**
	 * Beautify textual output.
	 */
	@Override
	public String toString() {
		return Arrays.toString(mSimulationMatrix) + "  " + mQvasr.toString();
	}
}
