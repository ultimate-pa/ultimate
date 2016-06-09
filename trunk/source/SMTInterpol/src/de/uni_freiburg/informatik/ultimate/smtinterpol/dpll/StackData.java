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
package de.uni_freiburg.informatik.ultimate.smtinterpol.dpll;

/**
 * This class is used to record undo data on the assertion stack.  It provides
 * the basic fields needed by the DPLL engine and stores data for satellite
 * theories.
 * @author Juergen Christ
 */
public class StackData {
	/// The completeness flag known at this level.
	int mCompleteness;
	/// Data for the satelite theories.
	Object[] mSatelliteData;
	/// The previous element of the stack
	StackData mPrev;
	
	public StackData() {
		this(null);
	}
	
	protected StackData(StackData prev) {
		mPrev = prev;
	}
	/**
	 * Add an atom to this stack level.
	 * @param atom The atom to add.
	 */
	public void addAtom(DPLLAtom atom) {
		// At root level we never need to remove an atom.  So we don't remember
		// it.
	}
	
	public StackData save(DPLLEngine engine) {
		mCompleteness = engine.getCompleteness();
		final ITheory[] satellites = engine.getAttachedTheories();
		mSatelliteData = new Object[satellites.length];
		for (int i = 0; i < mSatelliteData.length; ++i) {
			mSatelliteData[i] = satellites[i].push();
		}
		return new NonRootLvlStackData(this);
	}
	
	public StackData restore(DPLLEngine engine, int targetlevel) {
		final ITheory[] satellites = engine.getAttachedTheories();
		for (int i = 0; i < mPrev.mSatelliteData.length; ++i) {
			satellites[i].pop(mPrev.mSatelliteData[i], targetlevel);
		}
		engine.setCompleteness(mPrev.mCompleteness);
		return mPrev;
	}
}
