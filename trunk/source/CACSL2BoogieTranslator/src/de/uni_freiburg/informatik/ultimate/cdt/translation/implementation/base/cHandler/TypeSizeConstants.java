package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer;

public class TypeSizeConstants {
	public int sizeOfIntType;
	public int sizeOfPointerType;
	public int sizeOfFloatType;
	public int sizeOfCharType;
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
	public int defaultTypeSize;

	public TypeSizeConstants(UltimatePreferenceStore ups) {
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

	}
}