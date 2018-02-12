/*
 * Copyright (C) 2008-2015 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BoogiePreprocessor plug-in.
 * 
 * The ULTIMATE BoogiePreprocessor plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BoogiePreprocessor plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogiePreprocessor plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogiePreprocessor plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE BoogiePreprocessor plug-in grant you additional permission 
 * to convey the resulting work.
 */
/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.boogie.typechecker;

import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;

public class TypeParameters {
	private final String[]     identifiers;
	private final boolean      preserveOrder;
	private final int[]        placeHolders;
	private int[]        order;
	private int          numUsed;
	
	public TypeParameters(String[] typeParams) {
		this(typeParams, false);
	}
	
	public TypeParameters(String[] typeParams, boolean preserveOrder) {
		identifiers = typeParams;
		this.preserveOrder = preserveOrder;
		numUsed = 0;
		placeHolders = new int[identifiers.length];
		for (int i = 0; i < placeHolders.length; i++) {
			placeHolders[i] = -1;
		}
		if (preserveOrder) {
			order = new int[identifiers.length];
		}
	}
	
	public BoogieType findType(String name, int increment, boolean markUsed) {
		for (int i = 0; i < identifiers.length; i++) {
			if (identifiers[i].equals(name)) {
				if (placeHolders[i] < 0) {
					/* We cannot know which place holder (if any) will be taken*/
					if (!markUsed) {
						return BoogieType.TYPE_ERROR;
					}
					placeHolders[i] = preserveOrder ? i : numUsed;
					if (preserveOrder) {
						order[numUsed] = i;
					}
					numUsed++;
				}
				return BoogieType.createPlaceholderType
					(placeHolders[i]+increment);
			}
		}
		return null;
	}
	
	public boolean fullyUsed() {
		return numUsed == identifiers.length;
	}
	
	public int[] getOrder() {
		return order;
	}
	public int getNumUsed() {
		return numUsed;
	}
	
	public int getCount() {
		return placeHolders.length;
	}
}
