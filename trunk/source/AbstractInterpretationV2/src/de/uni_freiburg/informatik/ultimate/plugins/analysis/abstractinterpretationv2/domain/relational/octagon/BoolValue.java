/*
 * Copyright (C) 2015-2016 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2016 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Powerset of boolean values true and false.
 * This enum can be used to build a non-relational powerset abstract domain for booleans.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public enum BoolValue {

	// Ordinal numbers of constants are a bit fields, describing a subset of {true, false}.
	BOT,   // 00 = {    ,      }
	FALSE, // 01 = {    , false}
	TRUE,  // 10 = {true,      }
	TOP;   // 11 = {true, false}
	
	/**
	 * Constructs the set that contains exactly the given value.
	 * @param value Only element of the set.
	 * @return Unit set {value}
	 */
	public static BoolValue get(final boolean value) {
		return value ? TRUE : FALSE;
	}
	
	/**
	 * Creates the union of this and another set of booleans.
	 * @param other Set of booleans.
	 * @return Union
	 */
	public BoolValue union(final BoolValue other) {
		return values()[ordinal() | other.ordinal()];
	}
	
	/**
	 * Creates the intersection of this and another set of booleans.
	 * @param other Set of booleans.
	 * @return Intersection
	 */
	public BoolValue intersect(final BoolValue other) {
		return values()[ordinal() & other.ordinal()];
	}

	/**
	 * Indicates whether some other set of booleans is equal to this one.
	 * Equal sets contain exactly the same elements.
	 * @param other Set of booleans.
	 * @return Both sets are equal
	 */
	public boolean isSubsetEqual(final BoolValue other) {
		return this == BOT || other == TOP || this == other;
	}

	/**
	 * Computes the logical conjunction {@code and}.
	 * {@code and} is applied to each pair of values from the cartesian product of both sets.
	 * @param other Set of booleans.
	 * @return Logical conjunction
	 */
	public BoolValue and(final BoolValue other) {
		if (this == BOT || other == BOT) {
			return BOT;
		}
		final int thisBitField = ordinal();
		final int otherBitField = other.ordinal();
		final int xAndY = (thisBitField & otherBitField) | ((thisBitField | otherBitField) & 0b01);
		return values()[xAndY];
	}
	
	/**
	 * Computes the logical disjunction {@code or}.
	 * {@code or} is applied to each pair of values from the cartesian product of both sets.
	 * @param other Set of booleans.
	 * @return Logical disjunction
	 */
	public BoolValue or(final BoolValue other) {
		if (this == BOT || other == BOT) {
			return BOT;
		}
		final int thisBitField = ordinal();
		final int otherBitField = other.ordinal();
		final int xOrY = ((thisBitField | otherBitField) & 0b10) | (thisBitField & otherBitField);
		return values()[xOrY];
	}

	/**
	 * Computes the logical negation {@code not}.
	 * {@code not} is applied to each value of this set.
	 * @return Logical negation
	 */
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
//		final int x = ordinal();
//		final int notX = ((x << 1) & 0b11) | (x >> 1); // swap the two lowest bits
//		return values()[notX];
	}
	
	/**
	 * Constructs an SMT Term which restricts a variable to have values from this set.
	 * @param script Script to use.
	 * @param sort Sort to use.
	 * @param var Variable to be restricted.
	 * @return SMT term
	 */
	public Term getTerm(final Script script, final Sort sort, final Term var) {
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
