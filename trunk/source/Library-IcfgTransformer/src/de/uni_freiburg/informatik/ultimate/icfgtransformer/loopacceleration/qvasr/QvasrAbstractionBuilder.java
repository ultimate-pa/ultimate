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
import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Class for constructing a Qvasrabstraction using computed bases of resets and additions.
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de)
 *
 */
public class QvasrAbstractionBuilder {
	private QvasrAbstractionBuilder() {
		// Prevent instantiation of this utility class
	}

	public static QvasrAbstraction constructQvasrAbstraction(final ManagedScript script,
			final List<Pair<Term[], Term>> resetsBasis, final List<Pair<Term[], Term>> additionsBasis) {

		final int resetBasisSize = resetsBasis.size();
		final int additionBasisSize = additionsBasis.size();

		/*
		 * abstraction dimension d
		 */
		final int d = resetBasisSize + additionBasisSize;
		/*
		 * Concrete dimension n
		 */
		final int n = resetsBasis.get(0).getFirst().length - 1;

		final Term[][] simulationMatrix = new Term[d][n];
		final Term[] abstractionResetVector = new Term[d];
		final Term[] abstractionAdditionVector = new Term[d];
		for (int i = 0; i < resetBasisSize; i++) {
			final Pair<Term[], Term> resetBasisVector = resetsBasis.get(i);
			simulationMatrix[i] = Arrays.copyOf(resetBasisVector.getFirst(), n);
			abstractionResetVector[i] = script.getScript().decimal("0");
			abstractionAdditionVector[i] = resetBasisVector.getSecond();
		}
		for (int i = resetBasisSize; i < d; i++) {
			final Pair<Term[], Term> additionsBasisVector = resetsBasis.get(i);
			simulationMatrix[i] = Arrays.copyOf(additionsBasisVector.getFirst(), n);
			abstractionResetVector[i] = script.getScript().decimal("1");
			abstractionAdditionVector[i] = additionsBasisVector.getSecond();
		}

		final Qvasr qvasr = new Qvasr(abstractionResetVector, abstractionAdditionVector);
		return new QvasrAbstraction(simulationMatrix, qvasr);
	}

}
