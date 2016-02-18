package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public enum BoolValue {

	// Ordinal numbers of constants are a bitfields, describing a powerset of {true, false}.
	BOT,   // 00 = {    ,      }
	FALSE, // 01 = {    , false}
	TRUE,  // 10 = {true,      }
	TOP;   // 11 = {true, false}
	
	public static BoolValue get(boolean value) {
		return value ? TRUE : FALSE;
	}
	
	public BoolValue union(BoolValue other) {
		return values()[this.ordinal() | other.ordinal()];
	}
	
	public BoolValue intersect(BoolValue other) {
		return values()[this.ordinal() & other.ordinal()];
	}
	
	public BoolValue and(BoolValue other) {
		if (this == BOT || other == BOT) {
			return BOT;
		}
		int x = this.ordinal();
		int y = other.ordinal();
		int xAndY = (x & y) | ((x | y) & 0b01);
		return values()[xAndY];
	}
	
	public BoolValue or(BoolValue other) {
		if (this == BOT || other == BOT) {
			return BOT;
		}
		int x = this.ordinal();
		int y = other.ordinal();
		int xOrY = ((x | y) & 0b10) | (x & y);
		return values()[xOrY];
	}

	public BoolValue not() {
		switch (this) {
		case BOT:
			return BOT;
		case FALSE:
			return TRUE;
		case TRUE:
			return FALSE;
		default: // TOP
			return TOP;
		}
		// alternative:
//		int x = ordinal();
//		int notX = ((x << 1) & 0b11) | (x >> 1); // swap the two lowest bits
//		return values()[notX];
	}
	
	public Term getTerm(Script script, Sort sort, Term var) {
		switch (this) {
		case BOT:
			return script.term("false");
		case FALSE:
//			return script.term("=", var, script.term("false"));
			return script.term("not", var);
		case TRUE:
//			return script.term("=", var, script.term("true"));
			return var;
		default: // TOP
			return script.term("true");
		}
	}
}
