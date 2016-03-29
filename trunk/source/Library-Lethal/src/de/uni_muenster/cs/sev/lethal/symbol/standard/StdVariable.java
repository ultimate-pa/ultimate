/*
 * Copyright 2009 Dorothea Jansen <d.jansen@uni-muenster.de>, Martin Mohr <mohrfrosch@uni-muenster.de>, Irene Thesing <i_thes01@uni-muenster.de>, Anton Reis <antonreis@gmx.de>, Maria Schatz <m_scha17@uni-muenster.de>, Philipp Claves <philipp.claves@uni-muenster.de>, Sezar Jarrous <sezar.jarrous@gmail.com>
 *
 * This file is part of LETHAL.
 *
 * LETHAL is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * LETHAL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with LETHAL.  If not, see <http://www.gnu.org/licenses/>.
 */
/**
 * 
 */
package de.uni_muenster.cs.sev.lethal.symbol.standard;

import de.uni_muenster.cs.sev.lethal.symbol.common.Variable;


/**
 * Standard implementation of a homomorphism variable.
 * 
 * @see Variable
 * @author Anton, Dorothea, Irene, Maria, Martin, Sezar
 */
public class StdVariable implements Variable {


	/**
	 * Number of the homomorphism variable.
	 * 
	 * @see de.uni_muenster.cs.sev.lethal.symbol.common.Variable#getComponentNumber()
	 */
	private int number;

	
	/**
	 * @see de.uni_muenster.cs.sev.lethal.symbol.common.Variable#getComponentNumber()
	 */
	@Override
	public int getComponentNumber() {
		return number;
	}

	
	/**
	 * Constructs a new standard homomorphism variable with the given number. <br>
	 * The numbers begin at zero.
	 * 
	 * @param componentNumber number this variable is to be initialized with
	 */
	public StdVariable(int componentNumber){
		if (componentNumber <0){
			throw new IllegalArgumentException("Component numbers of variables begin at 0.");
		}
		number = componentNumber;
	}

	
	/**
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + this.number;
		return result;
	}

	
	/**
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		StdVariable other = (StdVariable) obj;
		if (this.number != other.number)
			return false;
		return true;
	}

	
	/**
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString(){
		return "var_"+number;
	}
	
}
