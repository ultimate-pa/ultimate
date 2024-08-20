/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE Proofs Library.
 *
 * The ULTIMATE Proofs Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Proofs Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Proofs Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Proofs Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Proofs Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.proofs.floydhoare;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;

/**
 * Bundles various settings related to the computation of Floyd/Hoare proofs.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public class HoareProofSettings {
	private final HoareAnnotationPositions mHoarePositions;
	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;

	public HoareProofSettings(final HoareAnnotationPositions hoarePositions,
			final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique) {
		mHoarePositions = hoarePositions;
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
	}

	/**
	 * @return whether or not a Floyd/Hoare proof should be computed at all
	 */
	public boolean computeHoareAnnotation() {
		return mHoarePositions != HoareAnnotationPositions.None;
	}

	/**
	 * @return a setting describing for which locations of an ICFG the annotation should be computed
	 */
	public HoareAnnotationPositions getHoarePositions() {
		return mHoarePositions;
	}

	public SimplificationTechnique getSimplificationTechnique() {
		return mSimplificationTechnique;
	}

	public XnfConversionTechnique getXnfConversionTechnique() {
		return mXnfConversionTechnique;
	}
}
