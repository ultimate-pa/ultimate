/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 * 
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler;

import java.math.BigInteger;
import java.util.LinkedHashMap;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.PRIMITIVE;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer;

/**
 * Provides the information if we want to use fixed sizes for types.
 * If yes an object of this class also provides the bytesize for each type.
 * @author Matthias Heizmann
 */
public class TypeSizes {
	private final boolean m_UseFixedTypeSizes;
	
	public final int sizeOfIntType;
	public final int sizeOfPointerType;
	public final int sizeOfFloatType;
	public final int sizeOfCharType;

//	for pointer arithmetic on a void pointer -- c standard disallows that, but gcc does not..
	private final int sizeOfVoidType; 

	private final int sizeOfBoolType;
	private final int sizeOfShortType;
	private final int sizeOfLongType;
	public final int sizeOfDoubleType;
	private final int sizeOfSCharType;
	private final int sizeOfUCharType;
	private final int sizeOfWCharType;
	private final int sizeOfChar16Type;
	private final int sizeOfChar32Type;
	private final int sizeOfUShortType;
	private final int sizeOfUIntType;
	private final int sizeOfULongType;
	private final int sizeOfLongLongType;
	private final int sizeOfULongLongType;
	private final int sizeOfComplexFloatType;
	private final int sizeOfComplexDoubleType;
	private final int sizeOfLongDoubleType;
	private final int sizeOfComplexLongDoubleType;
	final int sizeOfEnumType; //something like sizeof(enum s)
	/**
	 * Fixme: 2015-07-22 Matthias: I cannot find the default type size in the
	 * C standard. Before I set it to 23042 it was 0.
	 */
	public final int defaultTypeSize = 23042;
	
	private final LinkedHashMap<CPrimitive.PRIMITIVE, Integer> CPrimitiveToTypeSizeConstant = 
			new LinkedHashMap<>();
	

	public TypeSizes(UltimatePreferenceStore ups) {
		this. m_UseFixedTypeSizes = 
				ups.getBoolean(CACSLPreferenceInitializer.LABEL_USE_EXPLICIT_TYPESIZES);
		this.sizeOfVoidType = 
				ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_VOID);
		this.sizeOfBoolType = 
				ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_BOOL);
		this.sizeOfCharType = 
				ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_CHAR);
		this.sizeOfShortType = 
				ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_SHORT);
		this.sizeOfIntType = 
				ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_INT);
		this.sizeOfLongType = 
				ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_LONG);
		this.sizeOfFloatType = 
				ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_FLOAT);
		this.sizeOfDoubleType = 
				ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_DOUBLE);
		this.sizeOfPointerType = 
				ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_POINTER);
		this.sizeOfSCharType = 
				ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_SCHAR);
		this.sizeOfUCharType = 
				ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_UCHAR);
		this.sizeOfWCharType = 
				ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_WCHAR);
		this.sizeOfChar16Type = 
				ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_CHAR16);
		this.sizeOfChar32Type = 
				ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_CHAR32);
		this.sizeOfUShortType = 
				ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_USHORT);
		this.sizeOfUIntType = 
				ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_UINT);
		this.sizeOfULongType = 
				ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_ULONG);
		this.sizeOfLongLongType = 
				ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_LONGLONG);
		this.sizeOfULongLongType = 
				ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_ULONGLONG);
		this.sizeOfComplexFloatType = 
				ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_COMPLEXFLOAT);
		this.sizeOfComplexDoubleType = 
				ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_COMPLEXDOUBLE);
		this.sizeOfLongDoubleType = 
				ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_LONGDOUBLE);
		this.sizeOfComplexLongDoubleType = 
				ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_COMPLEXLONGDOUBLE);
		this.sizeOfEnumType = 
				ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_ENUM);
	
		CPrimitiveToTypeSizeConstant.put(PRIMITIVE.VOID, this.sizeOfVoidType);
		CPrimitiveToTypeSizeConstant.put(PRIMITIVE.BOOL, this.sizeOfBoolType);
		CPrimitiveToTypeSizeConstant.put(PRIMITIVE.CHAR, this.sizeOfCharType);
		CPrimitiveToTypeSizeConstant.put(PRIMITIVE.CHAR16, this.sizeOfChar16Type);
		CPrimitiveToTypeSizeConstant.put(PRIMITIVE.CHAR32, this.sizeOfChar32Type);
		CPrimitiveToTypeSizeConstant.put(PRIMITIVE.COMPLEX_DOUBLE, this.sizeOfComplexDoubleType);
		CPrimitiveToTypeSizeConstant.put(PRIMITIVE.COMPLEX_FLOAT, this.sizeOfComplexFloatType);
		CPrimitiveToTypeSizeConstant.put(PRIMITIVE.COMPLEX_LONGDOUBLE, this.sizeOfComplexLongDoubleType);
		CPrimitiveToTypeSizeConstant.put(PRIMITIVE.DOUBLE, this.sizeOfDoubleType);
		CPrimitiveToTypeSizeConstant.put(PRIMITIVE.FLOAT, this.sizeOfFloatType);
		CPrimitiveToTypeSizeConstant.put(PRIMITIVE.INT, this.sizeOfIntType);
		CPrimitiveToTypeSizeConstant.put(PRIMITIVE.LONG, this.sizeOfLongType);
		CPrimitiveToTypeSizeConstant.put(PRIMITIVE.LONGDOUBLE, this.sizeOfLongDoubleType);
		CPrimitiveToTypeSizeConstant.put(PRIMITIVE.LONGLONG, this.sizeOfLongLongType);
		CPrimitiveToTypeSizeConstant.put(PRIMITIVE.SCHAR, this.sizeOfSCharType);
		CPrimitiveToTypeSizeConstant.put(PRIMITIVE.SHORT, this.sizeOfShortType);
		CPrimitiveToTypeSizeConstant.put(PRIMITIVE.UCHAR, this.sizeOfUCharType);
		CPrimitiveToTypeSizeConstant.put(PRIMITIVE.UINT, this.sizeOfUIntType);
		CPrimitiveToTypeSizeConstant.put(PRIMITIVE.ULONG, this.sizeOfULongType);
		CPrimitiveToTypeSizeConstant.put(PRIMITIVE.ULONGLONG, this.sizeOfULongLongType);
		CPrimitiveToTypeSizeConstant.put(PRIMITIVE.USHORT, this.sizeOfUShortType);
		CPrimitiveToTypeSizeConstant.put(PRIMITIVE.WCHAR, this.sizeOfWCharType);
	}
	

	public boolean useFixedTypeSizes() {
		return m_UseFixedTypeSizes;
	}
	
	
	public Integer getSize(PRIMITIVE cPrimitive) {
		Integer result = CPrimitiveToTypeSizeConstant.get(cPrimitive);
		if (result == null) {
			throw new IllegalArgumentException("unknown type " + cPrimitive);
		} else {
			return result;
		}
	}
	
	public BigInteger getMaxValueOfPrimitiveType(CPrimitive cPrimitive) {
		int byteSize = getSize(cPrimitive.getType());
		BigInteger maxValue;
		if (cPrimitive.isUnsigned()) {
			maxValue = new BigInteger("2").pow(byteSize * 8);
		} else {
			maxValue = new BigInteger("2").pow(byteSize * 8 - 1);
		}
		maxValue = maxValue.subtract(BigInteger.ONE);
		return maxValue;
	}
	
	public BigInteger getMinValueOfPrimitiveType(CPrimitive cPrimitive) {
		int byteSize = getSize(cPrimitive.getType());
		BigInteger minValue;
		if (cPrimitive.isUnsigned()) {
			minValue = BigInteger.ZERO;
		} else {
			minValue = (new BigInteger("2").pow(byteSize * 8 - 1)).negate();
		}
		return minValue;
	}
	
	public BigInteger getMaxValueOfPointer() {
		int byteSize = sizeOfPointerType;
		BigInteger maxValue = new BigInteger("2").pow(byteSize * 8);
		maxValue = maxValue.subtract(BigInteger.ONE);
		return maxValue;
	}
}
