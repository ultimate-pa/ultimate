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
package de.uni_freiburg.informatik.ultimate.smtinterpol;

import java.util.Random;

public final class RandomSeedFinder {
	
	private RandomSeedFinder() {
		// Hide constructor
	}
	
	private static boolean testSeed(long seed, int timesTillRandomSplit) {
		final Random random = new Random(seed);
		for (int i = 0; i < timesTillRandomSplit; ++i) {
			final int val = random.nextInt(Config.RANDOM_SPLIT_BASE);
			if (val <= Config.RANDOM_SPLIT_FREQ) {
				return false;
			}
		}
		return true;
	}

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		if (args.length == 1) {
			final int timesTillRandomSplit = Integer.parseInt(args[0]);
			if (testSeed(Config.RANDOM_SEED, timesTillRandomSplit)) {
				System.out.println("Current seed is good...");
			} else {
				System.out.println("Current seed is bad...");
			}
			// This might take a while...
			for (long seed = 0; seed < Long.MAX_VALUE; ++seed) {
				if (testSeed(seed, timesTillRandomSplit)) {
					System.out.println("Good seed: " + seed);
					return;
				}
			}
			System.out.println("Could not find a good seed...");
		} else {
			System.out.println("Nothing to do...");
		}
	}

}
