package de.uni_freiburg.informatik.ultimate.cookiefy.ltl.model;

public class Literal extends Formula {

	private String mName;
	private LiteralType mLiteralType;

	public Literal(String name, LiteralType literalType) {
		mName = name;
		mLiteralType = literalType;
	}

	public String getName() {
		return mName;
	}

	@Override
	public String toString() {
		return mLiteralType + mName;
	}

	@Override
	public void acceptPreOrder(Visitor visitor) {
		visitor.visit(this);
	}
	
	@Override
	public void acceptInOrder(Visitor visitor) {
		visitor.visit(this);
	}

	@Override
	public void acceptPostOrder(Visitor visitor) {
		visitor.visit(this);
	}

}
