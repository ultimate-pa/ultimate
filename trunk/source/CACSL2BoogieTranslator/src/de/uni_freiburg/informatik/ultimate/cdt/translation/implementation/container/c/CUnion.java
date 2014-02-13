package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c;

public class CUnion extends CStruct {

	public CUnion(String[] fNames, CType[] fTypes) {
		super(fNames, fTypes);
	}

	public CUnion(String incompleteName) {
//	public CUnion(boolean isIncomplete) {
		super(incompleteName);
	}
}
