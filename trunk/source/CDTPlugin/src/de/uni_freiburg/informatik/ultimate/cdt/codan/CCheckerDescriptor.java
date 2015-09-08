/*
 * Copyright (C) 2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE CDTPlugin plug-in.
 * 
 * The ULTIMATE CDTPlugin plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE CDTPlugin plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CDTPlugin plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CDTPlugin plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE CDTPlugin plug-in grant you additional permission 
 * to convey the resulting work.
 */
/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.cdt.codan;

/**
 * Externalized Strings which are used in the checker, basically
 * for the preferences.
 * 
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 20.03.2012
 */
public interface CCheckerDescriptor {
	
	/**
	 * The Problem-Identifier for found Counterexamples.
	 */
	public static String CE_ID = "de.uni_freiburg.informatik.ultimate.cdt."
			+ "codan.CounterExampleResult";

	/**
	 * The Problem-Identifier for found Invariants.
	 */
	public static String IN_ID = "de.uni_freiburg.informatik.ultimate.cdt."
			+ "codan.InvariantResult";

	/**
	 * The Problem-Identifier for unproveable results.
	 */
	public static String UN_ID = "de.uni_freiburg.informatik.ultimate.cdt."
			+ "codan.UnproveableResult";

	/**
	 * The Problem-Identifier for positive results;
	 */
	public static String POS_ID = "de.uni_freiburg.informatik.ultimate.cdt."
			+ "codan.PositiveResult";
	
	/**
	 * The Problem-Identifier for syntax error results;
	 */
	public static String SYNERR_ID = "de.uni_freiburg.informatik.ultimate.cdt."
			+ "codan.SyntaxErrorResult";
	
	/**
	 * The Problem-Identifier for time outs;
	 */
	public static String TIMEOUT_ID = "de.uni_freiburg.informatik.ultimate.cdt."
			+ "codan.TimeoutResult";
	
	/**
	 * The Problem-Identifier for the generic info result;
	 */
	public static String GENERIC_INFO_RESULT_ID = "de.uni_freiburg.informatik.ultimate.cdt."
			+ "codan.GenericInfoResult";
	
	/**
	 * The Problem-Identifier for the generic warning result;
	 */
	public static String GENERIC_WARNING_RESULT_ID = "de.uni_freiburg.informatik.ultimate.cdt."
			+ "codan.GenericWarningResult";
	
	/**
	 * The Problem-Identifier for the generic error result;
	 */
	public static String GENERIC_ERROR_RESULT_ID = "de.uni_freiburg.informatik.ultimate.cdt."
			+ "codan.GenericErrorResult";
	
	/**
	 * Key for the Selection of Toolchains.
	 */
	public static String MAP_KEY = "TOOLCHAIN_SELECTION";
	/**
	 * Label Text for the Selection of Toolchains.
	 */
	public static String MAP_LABEL = "Please select one of the predefined toolchains";
}
