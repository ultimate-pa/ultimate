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

import java.util.ArrayList;
import java.util.List;
import java.util.ListIterator;

/**
 * Stack data once we leave the root level of the assertion stack.  In this
 * case, we collect the atoms added to this level and remove them when we
 * restore to this level.
 * @author Juergen Christ
 */
public class NonRootLvlStackData extends StackData {
	/// All atoms added on this level.
	List<DPLLAtom> mAtoms;
	public NonRootLvlStackData(StackData prev) {
		super(prev);
		mAtoms = new ArrayList<DPLLAtom>();
	}
	
	@Override
	public void addAtom(DPLLAtom atom) {
		mAtoms.add(atom);
	}
	
	@Override
	public StackData restore(DPLLEngine engine, int targetlevel) {
		final ListIterator<DPLLAtom> it = mAtoms.listIterator(mAtoms.size());
		while (it.hasPrevious()) {
			engine.removeAtom(it.previous());
		}
		mAtoms.clear();
		return super.restore(engine, targetlevel);
	}
}
