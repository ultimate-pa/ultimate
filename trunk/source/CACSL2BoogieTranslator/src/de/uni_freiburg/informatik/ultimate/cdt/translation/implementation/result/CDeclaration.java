package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import org.eclipse.cdt.core.dom.ast.IASTInitializer;


//import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;

public class CDeclaration {
	CType  mType;
	String mName;
	ResultExpression mInitializer;
	IASTInitializer mCAstInitializer;

	boolean mIsOnHeap;
	boolean mIsInitializerTranslated;

	//	public CDeclaration(CType type, String name, ResultExpression initializer, boolean onHeap) {
	public CDeclaration(CType type, String name, IASTInitializer cAstInitializer, boolean onHeap) {
		mType = type;
		mName = name;
		mCAstInitializer = cAstInitializer;
//		mInitializer = initializer;
		mIsOnHeap = onHeap;//TODO actually make use of this constructor/flag
		mIsInitializerTranslated = false;
	}
	
//	public CDeclaration(CType type, String name, ResultExpression initializer) {
	public CDeclaration(CType type, String name, IASTInitializer cAstInitializer) {
		this(type, name, cAstInitializer, false);
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
		if (!mIsInitializerTranslated)
			throw new AssertionError("Initializer must have been translated (with method CDeclaration.translateInitializer()) before this is called.");
		return mInitializer;
	}
	
	public boolean hasInitializer() {
		return mCAstInitializer != null;
	}

	
	public boolean isOnHeap() {
		return mIsOnHeap;
	}
	
	public String toString() {
		return "" + mType + " " + mName + " = " + mInitializer;
	}
	
	/**
	 * Triggers the translation of the untranslated initializer from the CAST into a ResultDeclaration
	 * that we work with.
	 * (Earlier this was done in visit IASTDeclarator, i.e. where the declarator was dispatched, but 
	 * this is too early when we have something like struct list myList = { &myList}, because we need to
	 * have some symbolTable entry for translating this initializer, see visit ISimpleDeclaraton for this, too.)
	 */
	public void translateInitializer(Dispatcher main) {
		assert !mIsInitializerTranslated : "initializer has already been translated";
		if (mCAstInitializer != null)
			mInitializer = (ResultExpression) main.dispatch(mCAstInitializer);
		mIsInitializerTranslated = true;
	}
}