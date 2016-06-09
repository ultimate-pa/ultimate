/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Jürgen Christ (christj@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Util Library.
 * 
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Util Library grant you additional permission 
 * to convey the resulting work.
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
