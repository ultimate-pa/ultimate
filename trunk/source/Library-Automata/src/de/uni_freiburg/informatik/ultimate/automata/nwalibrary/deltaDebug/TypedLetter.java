/*
 * Copyright (C) 2015 Christian Schilling <schillic@informatik.uni-freiburg.de>
 * Copyright (C) 2009-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.deltaDebug;

/**
 * Wraps a letter together with its type (internal, call, return).
 * 
 * @author Christian Schilling <schillic@informatik.uni-freiburg.de>
 */
class TypedLetter<LETTER> {
	final LETTER m_letter;
	final ELetterType m_type;
	
	public TypedLetter(final LETTER letter, final ELetterType type) {
		this.m_letter = letter;
		this.m_type = type;
	}
	
	@Override
	public String toString() {
		final StringBuilder b = new StringBuilder();
		b.append(m_letter);
		b.append("(");
		b.append(m_type);
		b.append(")");
		return b.toString();
	}
	
	@Override
	public int hashCode() {
		return m_letter.hashCode() + m_type.hashCode();
	}
	
	@SuppressWarnings("unchecked")
	@Override
	public boolean equals(Object o) {
		if (! (o instanceof TypedLetter)) {
			return false;
		}
		final TypedLetter<LETTER> other = (TypedLetter<LETTER>) o;
		return (other.m_letter.equals(this.m_letter)) &&
				(other.m_type == this.m_type);
	}
}