package de.uni_freiburg.informatik.ultimate.boogie.type;

import static org.junit.Assert.* ;
import org.junit.Test;

public class BoogiePreprocessorTests {
	
	@Test
	public void testTypes() {
		int[] o0 = new int[0];
		int[] o1 = new int[] { 0 };
		TypeConstructor wicket = new TypeConstructor("Wicket", false, 0, o0);
		TypeConstructor barrel = new TypeConstructor("Barrel", false, 1, o1);
		TypeConstructor field = new TypeConstructor("Field", false, 1, o1);
		BoogieType msetType = BoogieType.createArrayType
			(0, new BoogieType[] { BoogieType.createPlaceholderType(0) }, 
					BoogieType.intType);
		System.err.println("Test1: "+msetType);
		TypeConstructor multiSet = new TypeConstructor("MultiSet", true, 1, o1, msetType);
		BoogieType testType = BoogieType.createConstructedType(multiSet, 
				BoogieType.intType);
		System.err.println("Test2: "+testType+ " = "+ testType.getUnderlyingType());
		
		BoogieType heapType = BoogieType.createArrayType
		(1, new BoogieType[] { 
				BoogieType.intType,
				BoogieType.createConstructedType(field, new BoogieType[] { BoogieType.createPlaceholderType(0) })
		}, BoogieType.createPlaceholderType(0));
		System.err.println("Test3: "+heapType+ " = "+ heapType.getUnderlyingType());
		TypeConstructor heap  = new TypeConstructor("Heap", true, 0, o0, heapType);
		testType = BoogieType.createConstructedType(heap);
		System.err.println("Test4: "+testType+ " = "+ testType.getUnderlyingType());
		testType = BoogieType.createConstructedType(multiSet, testType);
		System.err.println("Test5: "+testType+ " = "+ testType.getUnderlyingType());
		
		BoogieType w  = BoogieType.createConstructedType(wicket);
		BoogieType bw = BoogieType.createConstructedType(barrel, w);
		BoogieType bbw = BoogieType.createConstructedType(barrel, bw);
		System.err.println("Test6: "+w+", "+bw+", "+bbw);
		testType = BoogieType.createConstructedType(multiSet, bbw);
		System.err.println("Test7: "+testType+ " = "+ testType.getUnderlyingType());

		BoogieType nestedType = BoogieType.createArrayType
			(1, new BoogieType[] { 
				BoogieType.createPlaceholderType(1),
				BoogieType.createConstructedType(field, new BoogieType[] { BoogieType.createPlaceholderType(0) })
			}, BoogieType.createPlaceholderType(0));
		TypeConstructor genHeap  = new TypeConstructor("GenHeap", true, 1, o1, nestedType);
		System.err.println("Test8: "+w+", "+bw+", "+bbw);
		testType = BoogieType.createConstructedType(genHeap, BoogieType.createPlaceholderType(0));
		System.err.println("Test9: "+testType+ " = "+ testType.getUnderlyingType());
		testType = BoogieType.createConstructedType(genHeap, testType);
		System.err.println("TestA: "+testType+ " = "+ testType.getUnderlyingType());
		testType = testType.substitutePlaceholders(new BoogieType[] { BoogieType.intType });
		System.err.println("TestB: "+testType+ " = "+ testType.getUnderlyingType());
		
		FunctionSignature cm = new FunctionSignature(0, new String[] {"heap","this"}, 
				new BoogieType[] { heapType, BoogieType.intType},
				null, BoogieType.boolType);
		System.err.println("function C.m"+cm+";");
		assertTrue(true);
	}
}
