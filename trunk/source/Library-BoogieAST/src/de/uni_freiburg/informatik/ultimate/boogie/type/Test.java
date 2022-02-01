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
package de.uni_freiburg.informatik.ultimate.boogie.type;

public class Test {
	public Test() {
		final int[] o0 = new int[0];
		final int[] o1 = new int[] { 0 };
		final BoogieTypeConstructor wicket = new BoogieTypeConstructor("Wicket", false, 0, o0);
		final BoogieTypeConstructor barrel = new BoogieTypeConstructor("Barrel", false, 1, o1);
		final BoogieTypeConstructor field = new BoogieTypeConstructor("Field", false, 1, o1);
		final BoogieType msetType = BoogieType.createArrayType
			(0, new BoogieType[] { BoogieType.createPlaceholderType(0) }, 
					BoogieType.TYPE_INT);
		System.err.println("Test1: "+msetType);
		final BoogieTypeConstructor multiSet = new BoogieTypeConstructor("MultiSet", true, 1, o1, msetType);
		BoogieType testType = BoogieType.createConstructedType(multiSet, 
				BoogieType.TYPE_INT);
		System.err.println("Test2: "+testType+ " = "+ testType.getUnderlyingType());
		
		final BoogieType heapType = BoogieType.createArrayType
		(1, new BoogieType[] { 
				BoogieType.TYPE_INT,
				BoogieType.createConstructedType(field, new BoogieType[] { BoogieType.createPlaceholderType(0) })
		}, BoogieType.createPlaceholderType(0));
		System.err.println("Test3: "+heapType+ " = "+ heapType.getUnderlyingType());
		final BoogieTypeConstructor heap  = new BoogieTypeConstructor("Heap", true, 0, o0, heapType);
		testType = BoogieType.createConstructedType(heap);
		System.err.println("Test4: "+testType+ " = "+ testType.getUnderlyingType());
		testType = BoogieType.createConstructedType(multiSet, testType);
		System.err.println("Test5: "+testType+ " = "+ testType.getUnderlyingType());
		
		final BoogieType w  = BoogieType.createConstructedType(wicket);
		final BoogieType bw = BoogieType.createConstructedType(barrel, w);
		final BoogieType bbw = BoogieType.createConstructedType(barrel, bw);
		System.err.println("Test6: "+w+", "+bw+", "+bbw);
		testType = BoogieType.createConstructedType(multiSet, bbw);
		System.err.println("Test7: "+testType+ " = "+ testType.getUnderlyingType());

		final BoogieType nestedType = BoogieType.createArrayType
			(1, new BoogieType[] { 
				BoogieType.createPlaceholderType(1),
				BoogieType.createConstructedType(field, new BoogieType[] { BoogieType.createPlaceholderType(0) })
			}, BoogieType.createPlaceholderType(0));
		final BoogieTypeConstructor genHeap  = new BoogieTypeConstructor("GenHeap", true, 1, o1, nestedType);
		System.err.println("Test8: "+w+", "+bw+", "+bbw);
		testType = BoogieType.createConstructedType(genHeap, BoogieType.createPlaceholderType(0));
		System.err.println("Test9: "+testType+ " = "+ testType.getUnderlyingType());
		testType = BoogieType.createConstructedType(genHeap, testType);
		System.err.println("TestA: "+testType+ " = "+ testType.getUnderlyingType());
		testType = testType.substitutePlaceholders(new BoogieType[] { BoogieType.TYPE_INT });
		System.err.println("TestB: "+testType+ " = "+ testType.getUnderlyingType());
		
		final BoogieFunctionSignature cm = new BoogieFunctionSignature(0, new String[] {"heap","this"}, 
				new BoogieType[] { heapType, BoogieType.TYPE_INT},
				null, BoogieType.TYPE_BOOL);
		System.err.println("function C.m"+cm+";");
	}
	

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		new Test();
	}

}
