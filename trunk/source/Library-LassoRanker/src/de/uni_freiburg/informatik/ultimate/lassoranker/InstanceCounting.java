/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE LassoRanker Library.
 * 
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker;


/**
 * A superclass for all classes that need to keep track of their instance number
 * 
 * Various routines of the LassoRanker package generate SMTLib variables.
 * In order to make sure that the same variables are generated only once, each
 * generated variable will be annotated with the respective instance number.
 * 
 * @author Jan Leike
 */
public class InstanceCounting {
	
	/**
	 *  Global instance counter
	 */
	private static long s_instance_counter = 0;
	
	/**
	 *  Number of the current instance
	 */
	private final long minstance;
	
	public InstanceCounting() {
		/*
		 * This assertion is violated if ultimate runs for so long that the
		 * counter overflows.
		 */
		assert(s_instance_counter >= 0);
		
		minstance = s_instance_counter;
		s_instance_counter++;
	}
	
	/**
	 * @return the instance number
	 */
	public long getInstanceNumber() {
		return minstance;
	}
}
