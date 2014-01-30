package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

//import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;

public class CDeclaration {
	CType  mType;
	String mName;
	ResultExpression mInitializer;
	
	boolean mIsOnHeap;
	
	public CDeclaration(CType type, String name, ResultExpression initializer, boolean onHeap) {
		mType = type;
		mName = name;
		mInitializer = initializer;
		mIsOnHeap = onHeap;//TODO actually make use of this constructor/flag
	}
	
	public CDeclaration(CType type, String name, ResultExpression initializer) {
		this(type, name, initializer, false);
	}
	
	public CDeclaration(CType type, String name) {
		this(type, name, null);
	}

	public CType getType() {
//		if (mIsOnHeap)
//			return new CPointer(mType);
//		else
			return mType;
	}
	public String getName() {
		return mName;
	}
	public ResultExpression getInitializer() {
		return mInitializer;
	}
	
	public boolean isOnHeap() {
		return mIsOnHeap;
	}
	
	public String toString() {
		return "" + mType + " " + mName + " = " + mInitializer;
	}
}