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
package de.uni_muenster.cs.sev.lethal.utils;

import java.util.HashMap;

/**
 * Converter extension that calls {ælink #uniqueConvert} only once for each object.
 * @author Philipp
 *
 * @param <A> type to be converted
 * @param <B> type to be converted into
 */
public abstract class CachedConverter<A,B> implements Converter<A,B> {

	/** Cache for already converted objects. */
	protected HashMap<A,B> cache = new HashMap<A,B>();

	/**
	 * @see de.uni_muenster.cs.sev.lethal.utils.Converter#convert(java.lang.Object)
	 */
	@Override
	public B convert(A a) {
		B res = cache.get(a);
		if (res == null){
			res = uniqueConvert(a);
			cache.put(a, res);
		}
		return res;
	}

	/**
	 * Returns the number of unique objects already converted.
	 * If this method is called from within {@link #uniqueConvert} the current object is not included in the count.
	 * @return the number of unique objects already converted.
	 */
	public int getConvertedObjectCount(){
		return cache.size();
	}

	/**
	 * Converts an object of type A into an object of type B.
	 * @param a object to be converted
	 * @return converted version of the given object
	 */
	public abstract B uniqueConvert(A a);

}
