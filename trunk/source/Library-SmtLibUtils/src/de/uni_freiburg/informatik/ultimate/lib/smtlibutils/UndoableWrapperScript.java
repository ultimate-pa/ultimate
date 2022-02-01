/*
 * Copyright (C) 2018 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.WrapperScript;

/**
 * An {@link UndoableWrapperScript} allows you to wrap some {@link Script} and track the push/pop operations performed
 * after wrapping. If you want to restore the stack level to the point of creation of this script, call
 * {@link #restore()}.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class UndoableWrapperScript extends WrapperScript {

	private int mDirtyStackLevels;

	public UndoableWrapperScript(final Script wrappedScript) {
		super(wrappedScript);
		mDirtyStackLevels = 0;
		push(1);
	}

	@Override
	public void push(final int levels) throws SMTLIBException {
		super.push(levels);
		mDirtyStackLevels += levels;
	}

	@Override
	public void pop(final int levels) throws SMTLIBException {
		super.pop(levels);
		mDirtyStackLevels -= levels;
		if (mDirtyStackLevels < 0) {
			throw new AssertionError("You removed more stack levels than tracked by UndoableWrapperScript");
		}
	}

	@Override
	public void resetAssertions() {
		throw new UnsupportedOperationException(UndoableWrapperScript.class
				+ " cannot restore anymore because it does not know what was on the stack before its creation");
	}

	@Override
	public void reset() {
		throw new UnsupportedOperationException(UndoableWrapperScript.class
				+ " cannot restore anymore because it does not know what was on the stack before its creation");
	}

	/**
	 * Pops as many stack levels as where pushed since this wrapper script was created.
	 *
	 * @return The number of dirty stack levels
	 */
	public int restore() {
		final int rtr = mDirtyStackLevels - 1;
		pop(mDirtyStackLevels);
		return rtr;
	}

}
