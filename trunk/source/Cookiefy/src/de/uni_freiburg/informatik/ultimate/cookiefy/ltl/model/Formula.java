package de.uni_freiburg.informatik.ultimate.cookiefy.ltl.model;

public abstract class Formula {

	public abstract void acceptPreOrder(Visitor visitor);
	public abstract void acceptInOrder(Visitor visitor);
	public abstract void acceptPostOrder(Visitor visitor);

}
