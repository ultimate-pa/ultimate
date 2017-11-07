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

import java.util.Arrays;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.BuchiAutomizerPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.BuchiAutomizerPreferenceInitializer.BuchiInterpolantAutomaton;

/**
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public enum BuchiInterpolantAutomatonConstructionStrategy {
	
	// @formatter:off
	
	FIXED_PREFERENCES {
		@Override
		public List<BuchiInterpolantAutomatonConstructionStyle> getBiaConstrucionStyleSequence(final IPreferenceProvider pp) {
			final BuchiInterpolantAutomaton mInterpolantAutomaton = 
					pp.getEnum(BuchiAutomizerPreferenceInitializer.LABEL_BUCHI_INTERPOLANT_AUTOMATON, BuchiInterpolantAutomaton.class);
			final boolean mScroogeNondeterminismStem = 
					pp.getBoolean(BuchiAutomizerPreferenceInitializer.LABEL_SCROOGE_NONDETERMINISM_STEM);
			final boolean mScroogeNondeterminismLoop = 
					pp.getBoolean(BuchiAutomizerPreferenceInitializer.LABEL_SCROOGE_NONDETERMINISM_LOOP);
			if ((mScroogeNondeterminismStem || mScroogeNondeterminismLoop)
					&& mInterpolantAutomaton != BuchiInterpolantAutomaton.ScroogeNondeterminism) {
				throw new IllegalArgumentException("illegal combination of settings");
			}
			if ((!mScroogeNondeterminismStem && !mScroogeNondeterminismLoop)
					&& mInterpolantAutomaton == BuchiInterpolantAutomaton.ScroogeNondeterminism) {
				throw new IllegalArgumentException("illegal combination of settings");
			}
			final boolean mBouncerStem = pp.getBoolean(BuchiAutomizerPreferenceInitializer.LABEL_BOUNCER_STEM);
			final boolean mBouncerLoop = pp.getBoolean(BuchiAutomizerPreferenceInitializer.LABEL_BOUNCER_LOOP);
			final boolean mCannibalizeLoop = pp.getBoolean(BuchiAutomizerPreferenceInitializer.LABEL_CANNIBALIZE_LOOP);
			return Arrays.asList(new BuchiInterpolantAutomatonConstructionStyle[] {
					new BuchiInterpolantAutomatonConstructionStyle(mInterpolantAutomaton, mBouncerStem, mBouncerLoop,
							mScroogeNondeterminismStem, mScroogeNondeterminismLoop, mCannibalizeLoop) });
		}
	},
	
	RHODODENDRON {
		@Override
		public List<BuchiInterpolantAutomatonConstructionStyle> getBiaConstrucionStyleSequence(final IPreferenceProvider pp) {
			return Arrays.asList(new BuchiInterpolantAutomatonConstructionStyle[] {
					new BuchiInterpolantAutomatonConstructionStyle(BuchiInterpolantAutomaton.Deterministic,
							true, false, false, false, false),
					new BuchiInterpolantAutomatonConstructionStyle(BuchiInterpolantAutomaton.Deterministic,
							true, true, false, false, false),
					new BuchiInterpolantAutomatonConstructionStyle(BuchiInterpolantAutomaton.ScroogeNondeterminism, 
							true, false, true, false, false),
					new BuchiInterpolantAutomatonConstructionStyle(BuchiInterpolantAutomaton.ScroogeNondeterminism, 
							true, true, true, false, false),
					new BuchiInterpolantAutomatonConstructionStyle(BuchiInterpolantAutomaton.ScroogeNondeterminism, 
							false, false, true, true, false),
			});
		}
	},
	
	ASTER {
		@Override
		public List<BuchiInterpolantAutomatonConstructionStyle> getBiaConstrucionStyleSequence(final IPreferenceProvider pp) {
			return Arrays.asList(new BuchiInterpolantAutomatonConstructionStyle[] {
					new BuchiInterpolantAutomatonConstructionStyle(BuchiInterpolantAutomaton.ScroogeNondeterminism, 
							true, false, true, false, false),
					new BuchiInterpolantAutomatonConstructionStyle(BuchiInterpolantAutomaton.ScroogeNondeterminism, 
							true, true, true, false, false),
					new BuchiInterpolantAutomatonConstructionStyle(BuchiInterpolantAutomaton.ScroogeNondeterminism, 
							false, false, true, true, false),
			});
		}
	},
	
	
	SUNFLOWER {
		@Override
		public List<BuchiInterpolantAutomatonConstructionStyle> getBiaConstrucionStyleSequence(final IPreferenceProvider pp) {
			return Arrays.asList(new BuchiInterpolantAutomatonConstructionStyle[] {
					new BuchiInterpolantAutomatonConstructionStyle(BuchiInterpolantAutomaton.ScroogeNondeterminism, 
							false, false, true, false, true),
					new BuchiInterpolantAutomatonConstructionStyle(BuchiInterpolantAutomaton.ScroogeNondeterminism, 
							false, true, true, false, false),
					new BuchiInterpolantAutomatonConstructionStyle(BuchiInterpolantAutomaton.ScroogeNondeterminism, 
							false, false, true, true, true),
			});
		}
	},
	
	ROSE { // only NBA
		@Override
		public List<BuchiInterpolantAutomatonConstructionStyle> getBiaConstrucionStyleSequence(final IPreferenceProvider pp) {
			return Arrays.asList(new BuchiInterpolantAutomatonConstructionStyle[] {
					new BuchiInterpolantAutomatonConstructionStyle(BuchiInterpolantAutomaton.ScroogeNondeterminism, 
							false, false, true, true, false), //NBA
			});
		}
	},
	
	DAISY { // CAV14 strategy
		@Override
		public List<BuchiInterpolantAutomatonConstructionStyle> getBiaConstrucionStyleSequence(final IPreferenceProvider pp) {
			return Arrays.asList(new BuchiInterpolantAutomatonConstructionStyle[] {
					new BuchiInterpolantAutomatonConstructionStyle(BuchiInterpolantAutomaton.Deterministic,
							true, false, false, false, false), //DBA
					new BuchiInterpolantAutomatonConstructionStyle(BuchiInterpolantAutomaton.Deterministic,
							true, true, false, false, false),  //DBA
					new BuchiInterpolantAutomatonConstructionStyle(BuchiInterpolantAutomaton.ScroogeNondeterminism, 
							false, false, true, true, false),  //NBA
			});
		}
	},
	
	DANDELION {
		@Override
		public List<BuchiInterpolantAutomatonConstructionStyle> getBiaConstrucionStyleSequence(final IPreferenceProvider pp) {
			return Arrays.asList(new BuchiInterpolantAutomatonConstructionStyle[] {
					new BuchiInterpolantAutomatonConstructionStyle(BuchiInterpolantAutomaton.ScroogeNondeterminism, 
							true, false, true, false, true),
					new BuchiInterpolantAutomatonConstructionStyle(BuchiInterpolantAutomaton.ScroogeNondeterminism, 
							true, true, true, false, false),
					new BuchiInterpolantAutomatonConstructionStyle(BuchiInterpolantAutomaton.ScroogeNondeterminism, 
							false, false, true, true, true),
			});
		}
	},
	
	;
	
	// @formatter:on
	
	public abstract List<BuchiInterpolantAutomatonConstructionStyle> getBiaConstrucionStyleSequence(final IPreferenceProvider pp);

}
