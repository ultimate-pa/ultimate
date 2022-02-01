/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ReachingDefinitions plug-in.
 * 
 * The ULTIMATE ReachingDefinitions plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ReachingDefinitions plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ReachingDefinitions plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ReachingDefinitions plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE ReachingDefinitions plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.util;


public class Util {

	public static <T> String prettyPrintIterable(Iterable<T> remaining, ElemToString<T> converter) {
		final StringBuilder sb = new StringBuilder();
		for (final T e : remaining) {
			sb.append(converter.toString(e)).append(", ");
		}
		sb.delete(sb.length() - 2, sb.length());
		return sb.toString();
	}
	
	public static String repeat(int c, String r) {
		String rtr = "";
	
		while (c > 0) {
			rtr = rtr + r;
			c--;
		}
		return rtr;
	}
	
	public static <T> ElemToString<T> createHashCodePrinter(){
		return new ElemToString<T>() {
			@Override
			public String toString(T elem) {
				return String.valueOf(elem.hashCode());
			}
		};
	}
	
	public interface ElemToString<E>{
		public String toString(E elem);
	}

}


