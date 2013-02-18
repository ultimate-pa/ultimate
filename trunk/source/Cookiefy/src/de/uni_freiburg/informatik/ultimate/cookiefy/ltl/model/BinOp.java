package de.uni_freiburg.informatik.ultimate.cookiefy.ltl.model;
public enum BinOp {
	WEAKUNTIL {
		@Override
		public String toString() {
			return "WU";
		}
	},
	UNTIL {
		@Override
		public String toString() {
			return "U";
		}
	},
	RELEASE {
		@Override
		public String toString() {
			return "R";
		}
	},
	OR {
		@Override
		public String toString() {
			return "|";
		}
	},
	AND {
		@Override
		public String toString() {
			return "&";
		}
	}
}
