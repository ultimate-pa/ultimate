package de.uni_freiburg.informatik.ultimate.cookiefy.ltl.model;
public enum UnOp {
	FINALLY {
		@Override
		public String toString() {
			return "F";
		}
	},
	GLOBALLY {
		@Override
		public String toString() {
			return "G";
		}
	},
	NOT {
		@Override
		public String toString() {
			return "!";
		}
	},
	NEXT {
		@Override
		public String toString() {
			return "X";
		}
	}
}
