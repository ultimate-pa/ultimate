/*
 * Copyright (C) 2015 Christian Schilling <schillic@informatik.uni-freiburg.de>
 * Copyright (C) 2009-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automaton Delta Debugger.
 * 
 * The ULTIMATE Automaton Delta Debugger is free software: you can redistribute
 * it and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * The ULTIMATE Automaton Delta Debugger is distributed in the hope that it will
 * be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser
 * General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automaton Delta Debugger. If not, see
 * <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7: If you modify the
 * ULTIMATE Automaton Delta Debugger, or any covered work, by linking or
 * combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automaton Delta Debugger grant you additional
 * permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatondeltadebugger.utils;

/**
 * Wraps a letter together with its type (internal, call, return).
 * 
 * @author Christian Schilling <schillic@informatik.uni-freiburg.de>
 */
public class TypedLetter<LETTER> {
	public final LETTER mLetter;
	public final ELetterType mType;

	public TypedLetter(final LETTER letter, final ELetterType type) {
		this.mLetter = letter;
		this.mType = type;
	}

	@Override
	public String toString() {
		final StringBuilder b = new StringBuilder();
		b.append(mLetter);
		b.append("(");
		b.append(mType);
		b.append(")");
		return b.toString();
	}

	@Override
	public int hashCode() {
		return mLetter.hashCode() + mType.hashCode();
	}

	@SuppressWarnings("unchecked")
	@Override
	public boolean equals(Object o) {
		if (!(o instanceof TypedLetter)) {
			return false;
		}
		final TypedLetter<LETTER> other = (TypedLetter<LETTER>) o;
		return (other.mLetter.equals(this.mLetter)) &&
				(other.mType == this.mType);
	}
}