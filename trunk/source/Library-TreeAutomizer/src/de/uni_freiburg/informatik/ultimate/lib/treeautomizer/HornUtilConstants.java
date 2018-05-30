/*
 * Copyright (C) 2016 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Mostafa M.A. (mostafa.amin93@gmail.com)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.treeautomizer;

/**
 *
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public final class HornUtilConstants {

	/**
	 * A set of HornClauses does not have procedures. However, for fulfilling some interfaces we need
	 * to give a procedure name.
	 */
	public static final String HORNCLAUSEMETHODNAME = "dummy-HornClauseMethod";

	public static final String HORN_ANNOT_NAME = "HoRNClauses";

	public static final String DONTCARE = "DontCare";


	public static final String BODYVARPREFIX = "hbv";
	public static final String HEADVARPREFIX = "hhv";

	private HornUtilConstants() {
		// hides public constructor
	}

	public static String computeNameForHcVar(final String prefix, final String headPredSymProcName, final int index,
			final String sortStringRaw) {
		final String sortString = sortStringRaw.replaceAll(" ", "_").replaceAll("[()]", "");
		return String.format("%s_%s_%d_%s", prefix, headPredSymProcName, index, sortString);
	}


}
