/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE BuchiAutomizer plug-in.
 * 
 * The ULTIMATE BuchiAutomizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BuchiAutomizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BuchiAutomizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BuchiAutomizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BuchiAutomizer plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.BuchiAutomizerPreferenceInitializer.BuchiInterpolantAutomaton;

/**
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
class BuchiInterpolantAutomatonConstructionStyle {
	private final BuchiInterpolantAutomaton mInterpolantAutomaton;
	private final boolean mBouncerStem;
	private final boolean mBouncerLoop;
	private final boolean mScroogeNondeterminismStem;
	private final boolean mScroogeNondeterminismLoop;
	private final boolean mCannibalizeLoop;

	public BuchiInterpolantAutomatonConstructionStyle(final BuchiInterpolantAutomaton interpolantAutomaton, final boolean bouncerStem, final boolean bouncerLoop,
			final boolean scroogeNondeterminismStem, final boolean scroogeNondeterminismLoop, final boolean cannibalizeLoop) {
		super();
		mInterpolantAutomaton = interpolantAutomaton;
		mBouncerStem = bouncerStem;
		mBouncerLoop = bouncerLoop;
		mScroogeNondeterminismStem = scroogeNondeterminismStem;
		mScroogeNondeterminismLoop = scroogeNondeterminismLoop;
		mCannibalizeLoop = cannibalizeLoop;
	}

	public BuchiInterpolantAutomaton getInterpolantAutomaton() {
		return mInterpolantAutomaton;
	}

	public boolean isBouncerStem() {
		return mBouncerStem;
	}

	public boolean isBouncerLoop() {
		return mBouncerLoop;
	}

	public boolean isScroogeNondeterminismStem() {
		return mScroogeNondeterminismStem;
	}

	public boolean isScroogeNondeterminismLoop() {
		return mScroogeNondeterminismLoop;
	}

	public boolean cannibalizeLoop() {
		return mCannibalizeLoop;
	}
	
	public boolean isAlwaysSemiDeterministic() {
		return !isScroogeNondeterminismLoop();
	}
	
	@Override
	public String toString() {
		return "RefinementSetting [mInterpolantAutomaton="
				+ mInterpolantAutomaton + ", mBouncerStem="
				+ mBouncerStem + ", mBouncerLoop=" + mBouncerLoop
				+ ", mScroogeNondeterminismStem="
				+ mScroogeNondeterminismStem
				+ ", mScroogeNondeterminismLoop="
				+ mScroogeNondeterminismLoop + ", mCannibalizeLoop="
				+ mCannibalizeLoop + "]";
	}


}