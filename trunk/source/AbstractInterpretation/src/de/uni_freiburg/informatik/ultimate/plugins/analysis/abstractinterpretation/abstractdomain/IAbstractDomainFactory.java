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
 * An AbstractDomainFactory serves to create value, state, widening and merging classes belonging
 * to the same abstract domain system so they can all work together.
 * 
 * @author Christopher Dillo
 *
 */
public interface IAbstractDomainFactory<T> {
	
	/**
	 * @return A new abstract value object with the given value
	 */
	public IAbstractValue<T> makeValue(T value);
	
	/**
	 * @return A new abstract value object representing the top element of the abstract domain
	 */
	public IAbstractValue<T> makeTopValue();
	
	/**
	 * @return A new abstract value object representing the bottom element of the abstract domain
	 */
	public IAbstractValue<T> makeBottomValue();
	
	/**
	 * @param integer Given as a string to support arbitrarily large integers.
	 * @return An abstract value representing the given integer
	 */
	public IAbstractValue<T> makeIntegerValue(String integer);
	
	/**
	 * @param real Given as a string to support arbitrarily large reals.
	 * @return An abstract value representing the given real
	 */
	public IAbstractValue<T> makeRealValue(String real);

	/**
	 * @param bool
	 * @return An abstract value representing the given boolean value
	 */
	public IAbstractValue<T> makeBoolValue(boolean bool);

	/**
	 * @param bitvector Given as a string to support arbitrarily large BitVectors.
	 * @return An abstract value representing the given BitVector
	 */
	public IAbstractValue<T> makeBitVectorValue(String bitvector);

	/**
	 * @param value
	 * @return An abstract value representing the given String
	 */
	public IAbstractValue<T> makeStringValue(String value);
	
	/**
	 * @param value
	 * @return True iff the given value belongs to this factory's abstract domain system
	 */
	public boolean valueBelongsToDomainSystem(IAbstractValue<?> value);

	/**
	 * @return A widening operator object corresponding to the choice in the plugin preferences
	 */
	public IWideningOperator<T> getWideningOperator();

	/**
	 * @return A merge operator object corresponding to the choice in the plugin preferences
	 */
	public IMergeOperator<T> getMergeOperator();
	
}
