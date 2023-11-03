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

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;

/**
 *
 * This class represents an integer vector addition system with resets abstraction (Intvasr-abstraction). It is used to
 * overapproximate changes to variables by a transition formula by linear simulating the formula onto a {@link Intvasr}.
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de)
 */

public class IntvasrAbstraction implements IVasrAbstraction<Integer> {

	private final Integer[][] mSimulationMatrix;
	private final Intvasr mIntvasr;

	/**
	 * Construct a new Integer-Vasr-abstraction (S, V), which overapproximates a {@link UnmodifiableTransFormula} F by
	 * using linear matrix S to simulate F to the {@link Qvasr} V.
	 *
	 * @param simulationMatrix
	 *            The initial simulation matrix S.
	 * @param intvasr
	 *            The initial {@link Intvasr} V.
	 */
	public IntvasrAbstraction(final Integer[][] simulationMatrix, final Intvasr intvasr) {
		mSimulationMatrix = simulationMatrix;
		mIntvasr = intvasr;
	}

	@Override
	public int getConcreteDimension() {
		return mSimulationMatrix[0].length;
	}

	/**
	 * Return this abstractions simulation matrix.
	 *
	 * @return
	 */
	@Override
	public Integer[][] getSimulationMatrix() {
		return mSimulationMatrix;
	}

	/**
	 * Return the Intvasr on to which a transition formula is simulated.
	 *
	 * @return
	 */
	@Override
	public IVasr<Integer> getVasr() {
		return mIntvasr;
	}

	/**
	 * Beautify textual output.
	 */
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("S: \n");
		for (int i = 0; i < mSimulationMatrix.length; i++) {
			sb.append("[");
			for (int j = 0; j < mSimulationMatrix[0].length; j++) {
				sb.append(" " + mSimulationMatrix[i][j].toString() + " ");
			}
			sb.append("]");
			sb.append("\n");
		}
		sb.append("\nV: \n");
		sb.append(mIntvasr.toString());
		return sb.toString();
	}
}
