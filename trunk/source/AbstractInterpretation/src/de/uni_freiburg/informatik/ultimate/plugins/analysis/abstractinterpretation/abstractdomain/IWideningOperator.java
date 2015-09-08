/*
 * Copyright (C) 2014-2015 Christopher Dillo
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE AbstractInterpretation plug-in.
 * 
 * The ULTIMATE AbstractInterpretation plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE AbstractInterpretation plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretation plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretation plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE AbstractInterpretation plug-in grant you additional permission 
 * to convey the resulting work.
 */
/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain;

/**
 * Widening operators of an absract domain system can be used to ensure termination by
 * over-approximating fixed points.
 * 
 * @author Christopher Dillo
 *
 */
public interface IWideningOperator<T> {
	
	/**
	 * Merges two given values while applying widening. The old and new value may not be
	 * treated equally and are thus not interchangable.
	 * @param oldValue The previous abstract value
	 * @param newValue The new abstract value
	 * @return A merged value which is greater than both given value wrt the complete lattice of abstract values
	 */
	public IAbstractValue<T> apply(IAbstractValue<?> oldValue, IAbstractValue<?> newValue);
	
	/**
	 * @return A copy of this widening operator
	 */
	public IWideningOperator<T> copy();
}
