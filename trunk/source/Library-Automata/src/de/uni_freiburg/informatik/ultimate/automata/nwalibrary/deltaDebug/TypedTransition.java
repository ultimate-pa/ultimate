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
 * Wraps a transition together with its type (internal, call, return).
 * 
 * @author Christian Schilling <schillic@informatik.uni-freiburg.de>
 */
class TypedTransition<LETTER, STATE> {
	final STATE m_pred;
	final STATE m_succ;
	final STATE m_hier;
	final TypedLetter<LETTER> m_letter;
	
	public TypedTransition(final STATE pred, final STATE succ,
			final STATE hier, final TypedLetter<LETTER> letter) {
		this.m_pred = pred;
		this.m_succ = succ;
		this.m_hier = hier;
		this.m_letter = letter;
	}
	
	@Override
	public int hashCode() {
		final int hashCode = (m_hier == null ? 0 : m_hier.hashCode());
		return hashCode + m_pred.hashCode() + m_succ.hashCode() +
				m_letter.hashCode();
	}
	
	@SuppressWarnings("unchecked")
	@Override
	public boolean equals(Object o) {
		if (! (o instanceof TypedTransition)) {
			return false;
		}
		final TypedTransition<LETTER, STATE> other =
				(TypedTransition<LETTER, STATE>) o;
		if (this.m_hier == null) {
			if (other.m_hier != null) {
				return false;
			}
		} else if (other.m_hier == null) {
			return false;
		}
		return (other.m_pred.equals(this.m_pred)) &&
				(other.m_succ.equals(this.m_succ)) &&
				(other.m_letter.equals(this.m_letter));
	}
	
	@Override
	public String toString() {
		final StringBuilder b = new StringBuilder();
		b.append("<");
		b.append(m_pred);
		b.append(", ");
		b.append(m_letter);
		if (m_hier != null) {
			b.append(m_hier);
			b.append(", ");
		}
		b.append(", ");
		b.append(m_succ);
		b.append(">");
		return b.toString();
	}
}