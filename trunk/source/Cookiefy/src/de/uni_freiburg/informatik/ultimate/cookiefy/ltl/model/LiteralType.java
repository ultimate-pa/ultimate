package de.uni_freiburg.informatik.ultimate.cookiefy.ltl.model;
public enum LiteralType {
	INPUT {
		@Override
		public String toString() {
			return "i";
		}
	},
	OUTPUT {
		@Override
		public String toString() {
			return "o";
		}
	}
}
