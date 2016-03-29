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
package de.uni_muenster.cs.sev.lethal.utils;

/**
 * Implements the converter in the most trivial useful way - as identity function.
 * 
 * @param <T> type of objects to be converted
 * 
 * @author Martin
 */
public class IdentityConverter<T> implements Converter<T,T> {


	/**
	 * @see de.uni_muenster.cs.sev.lethal.utils.Converter#convert(java.lang.Object)
	 */
	@Override
	public T convert(T a) {
		return a;
	}

	/**
	 * Creates a new instance of IdentityConverter.
	 * 
	 * TODO (Martin?): Make this a singleton. 
	 * 
	 * @param <T> Type of the object to be converted
	 * @return Instance of IdentityConverter.
	 */
	public static <T> IdentityConverter<T> getInstance() {
		return new IdentityConverter<T>();
	}

}
