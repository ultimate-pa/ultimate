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
import de.uni_muenster.cs.sev.lethal.symbol.common.NamedSymbol;

/**
 * Implements a variable with a name.
 * 
 * @param <T> type of the name of the variable
 * 
 * @see Variable
 * 
 * @author Dorothea, Irene, Martin
 */
public class NamedVariable<T> extends StdVariable implements NamedSymbol<T>, Variable {


	/**
	 * Name of the symbol.
	 */
	private T name;


	/**
	 * Constructs a new named variable by a given name and a given number.
	 * 
	 * @param name name of the variable
	 * @param compNr number of the variable for replacing in {@link de.uni_muenster.cs.sev.lethal.hom.Hom homomorphism}
	 * @see Variable
	 */
	public NamedVariable(T name, int compNr) {
		super(compNr);
		this.name = name;
	}


	/**
	 * @see de.uni_muenster.cs.sev.lethal.symbol.common.NamedSymbol#getName()
	 */
	@Override
	public T getName() {
		return name;
	}


	/**
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString(){
		return name.toString()+ "_" + this.getComponentNumber(); 
	}

}
