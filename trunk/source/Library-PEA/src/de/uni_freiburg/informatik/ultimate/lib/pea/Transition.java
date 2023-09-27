/*
 *
 * This file is part of the PEA tool set
 *
 * The PEA tool set is a collection of tools for
 * Phase Event Automata (PEA). See
 * http://csd.informatik.uni-oldenburg.de/projects/peatools.html
 * for more information.
 *
 * Copyright (C) 2005-2006, Department for Computing Science,
 *                          University of Oldenburg
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA
 */
package de.uni_freiburg.informatik.ultimate.lib.pea;

public class Transition<T> {
	private final Phase<T> mSrc;
	private final Phase<T> mDest;
	private final String[] mResets;
	private T mGuard;

	public Transition(final Phase<T> src, final T guard, final String[] resets, final Phase<T> dest) {
		mSrc = src;
		mGuard = guard;
		mResets = resets;
		mDest = dest;
	}

	@Override
	public String toString() {
		String destName = mDest.toString();
		if (destName.length() < 33) {
			destName = (destName + "                                 ").substring(0, 33);
		}
		final StringBuffer result = new StringBuffer(" -> ").append(destName).append(" guard ").append(mGuard);

		if (getResets().length > 0) {
			result.append(" resets {");
			String comma = "";
			for (int i = 0; i < getResets().length; i++) {
				result.append(comma).append(getResets()[i]);
				comma = ",";
			}
			result.append("}");
		}
		return result.toString();
	}

	public Phase<T> getDest() {
		return mDest;
	}

	public String[] getResets() {
		return mResets;
	}

	public Phase<T> getSrc() {
		return mSrc;
	}

	public T getGuard() {
		return mGuard;
	}

	public void setGuard(final T guard) {
		mGuard = guard;
	}
}
