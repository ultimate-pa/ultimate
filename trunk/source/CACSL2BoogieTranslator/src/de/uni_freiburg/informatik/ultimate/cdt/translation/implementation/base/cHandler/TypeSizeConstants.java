package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler;

import java.util.LinkedHashMap;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.PRIMITIVE;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer;

public class TypeSizeConstants {
	public int sizeOfIntType;
	public int sizeOfPointerType;
	public int sizeOfFloatType;
	public int sizeOfCharType;

//	for pointer arithmetic on a void pointer -- c standard disallows that, but gcc does not..
	public int sizeOfVoidType; 

	public int sizeOfBoolType;
	public int sizeOfShortType;
	public int sizeOfLongType;
	public int sizeOfDoubleType;
	public int sizeOfSCharType;
	public int sizeOfUCharType;
	public int sizeOfWCharType;
	public int sizeOfChar16Type;
	public int sizeOfChar32Type;
	public int sizeOfUShortType;
	public int sizeOfUIntType;
	public int sizeOfULongType;
	public int sizeOfLongLongType;
	public int sizeOfULongLongType;
	public int sizeOfComplexFloatType;
	public int sizeOfComplexDoubleType;
	public int sizeOfLongDoubleType;
	public int sizeOfComplexLongDoubleType;
	public int sizeOfEnumType; //something like sizeof(enum s)
	public int defaultTypeSize;
	
	public LinkedHashMap<CPrimitive.PRIMITIVE, Integer> CPrimitiveToTypeSizeConstant = new LinkedHashMap<>();

	public TypeSizeConstants(UltimatePreferenceStore ups) {
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
		this.sizeOfBoolType = 
				ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_BOOL);
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
		this.sizeOfEnumType = 
				ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_DEFAULT);

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
}