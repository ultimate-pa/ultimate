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
package de.uni_freiburg.informatik.ultimate.util.datastructures;

import java.util.ArrayList;
import java.util.Iterator;

import de.uni_freiburg.informatik.ultimate.util.ScopeUtils;


/**
 * A version of java.util.ArrayList that supports scoping.
 * @author Juergen Christ
 */
@SuppressWarnings("serial")
public class ScopedArrayList<E> extends ArrayList<E> {
	int[] mLevels = new int[ScopeUtils.NUM_INITIAL_SCOPES];
	int mCurscope = -1;
	
	@Override
	public void clear() {
		mLevels = new int[ScopeUtils.NUM_INITIAL_SCOPES];
		mCurscope = -1;
		super.clear();
	}
	public void beginScope() {
		if (++mCurscope == mLevels.length) {
			mLevels = ScopeUtils.grow(mLevels);
		}
		mLevels[mCurscope] = size();		
	}
	public void endScope() {
		final int oldsize = mLevels[mCurscope];
		super.removeRange(oldsize, size());
		if (ScopeUtils.shouldShrink(--mCurscope, mLevels.length)) {
			mLevels = ScopeUtils.shrink(mLevels);
		}
	}
	public int getLastScopeSize() {
		return mLevels[mCurscope];
	}
	public void addToLevel(E obj, int level) {
		if (level > mCurscope) {
			add(obj);
		} else {
			final int pos = mLevels[level];
			add(pos, obj);
			for (int i = level; i <= mCurscope; ++i) {
				mLevels[level] += 1;
			}
		}
	}
	public Iterable<E> currentScope() {
		return new Iterable<E>() {

			@Override
			public Iterator<E> iterator() {
				return listIterator(mLevels[mCurscope]);
			}
			
		};
	}
}
