/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.util;

import java.util.ArrayList;
import java.util.Iterator;


/**
 * A version of java.util.ArrayList that supports scoping.
 * @author Juergen Christ
 */
@SuppressWarnings("serial")
public class ScopedArrayList<E> extends ArrayList<E> {
	int[] levels = new int[ScopeUtils.NUM_INITIAL_SCOPES];
	int curscope = -1;
	
	public void clear() {
		levels = new int[ScopeUtils.NUM_INITIAL_SCOPES];
		curscope = -1;
		super.clear();
	}
	public void beginScope() {
		if (++curscope == levels.length)
			levels = ScopeUtils.grow(levels);
		levels[curscope] = size();		
	}
	public void endScope() {
		int oldsize = levels[curscope];
		super.removeRange(oldsize, size());
		if (ScopeUtils.shouldShrink(--curscope, levels.length))
			levels = ScopeUtils.shrink(levels);
	}
	public int getLastScopeSize() {
		return levels[curscope];
	}
	public void addToLevel(E obj, int level) {
		if (level > curscope)
			add(obj);
		else {
			int pos = levels[level];
			add(pos, obj);
			for (int i = level; i <= curscope; ++i)
				levels[level] += 1;
		}
	}
	public Iterable<E> currentScope() {
		return new Iterable<E>() {

			@Override
			public Iterator<E> iterator() {
				return listIterator(levels[curscope]);
			}
			
		};
	}
}
