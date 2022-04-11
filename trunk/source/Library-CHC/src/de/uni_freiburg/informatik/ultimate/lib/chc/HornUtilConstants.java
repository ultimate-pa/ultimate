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
package de.uni_freiburg.informatik.ultimate.lib.chc;

import de.uni_freiburg.informatik.ultimate.logic.Sort;

/**
 *
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public final class HornUtilConstants {

	/**
	 * A set of HornClauses does not have procedures. However, for fulfilling some interfaces we need to give a
	 * procedure name.
	 */
	public static final String HORNCLAUSEMETHODNAME = "dummy-HornClauseMethod";

	public static final String DONTCARE = "DontCare";

	public static final String BODYVARPREFIX = "hbv";
	public static final String HEADVARPREFIX = "hhv";

	public static final String HC_SSA_TERM = "HCsSATerm_";

	public static final String GOTO_PROC_NAME = "gotoProc";

	public static final String SSA_VAR_PREFIX = "ssa";

	private HornUtilConstants() {
		// hides public constructor
	}

	public static String computeNameForHcVar(final String prefix, final HcPredicateSymbol predSym, final int index,
			final String identifier) {

		final String name = HornUtilConstants.sanitzePredName(predSym.getName());
		final String identifierString = identifier.replaceAll(" ", "_").replaceAll("[()]", "");
		return String.format("%s_%s_%s_%d", prefix, name, identifierString, index);
	}

	/**
	 * The allowed characters for smt identifiers are not all allowed for Boogie idenifiers.
	 *
	 * @param headPredSymProcNameRaw
	 * @return
	 */
	public static String sanitzePredName(final String headPredSymProcNameRaw) {
		assert !headPredSymProcNameRaw.contains(".CLN") : "naming might clash";
		assert !headPredSymProcNameRaw.contains(".DLR") : "naming might clash";
		assert !headPredSymProcNameRaw.contains(".AT") : "naming might clash";
		assert !headPredSymProcNameRaw.contains(".HSH") : "naming might clash";
		assert !headPredSymProcNameRaw.contains(".DSH") : "naming might clash";
		return headPredSymProcNameRaw.replaceAll("@", ".AT").replaceAll("#", ".HSH").replaceAll("-", ".DSH")
				.replaceAll("\\$", ".DLR").replaceAll(":", ".CLN");
	}

	public static String sanitzeSortNameForBoogie(final Sort sort) {
		assert !sort.toString().contains(".OP") : "naming might clash";
		assert !sort.toString().contains(".CP") : "naming might clash";
		return sort.toString().replaceAll("\\(", ".OP").replaceAll("\\)", ".CP").replaceAll(" ", "_");
	}

}
