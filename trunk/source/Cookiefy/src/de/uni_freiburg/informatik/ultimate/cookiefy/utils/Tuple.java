package de.uni_freiburg.informatik.ultimate.cookiefy.utils;

public class Tuple<X, Y> {
	public final X x;
	public final Y y;

	public Tuple(X x, Y y) {
		this.x = x;
		this.y = y;
	}

	@Override
	public String toString() {
		return "[" + x.toString() + "," + y.toString() + "]";
	}
}
