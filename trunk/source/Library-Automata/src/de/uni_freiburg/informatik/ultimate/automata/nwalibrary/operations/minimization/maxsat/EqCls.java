/*
 * Copyright (C) 2016 Jens Stimpfle <stimpflj@informatik.uni-freiburg.de>

 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.maxsat;

import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.io.Writer;

/**
 * A partition of a number of (integer) states into equivalence classes.
 *
 * <p>There is a static <code>checkConsistency()</code> method.
 *
 * @author stimpflj
 *
 */
public class EqCls {
	/** Number of equivalence classes */
	int numClasses;

	/** For each old state, to what equivalence class it belongs */
	int[] classOf;


	/** Convenience creator which also asserts consistency */
	public static EqCls createConsistent(int numClasses, int[] classOf) {
		EqCls result = new EqCls();
		result.numClasses = numClasses;
		result.classOf = classOf;
		assert EqCls.checkConsistency(result);
		return result;
	}

	/**
	 * Check consistency of equivalence classes:
	 *
	 * <ul>
	 * <li><code>0 <= numClasses</code>
	 * <li><code>0 <= x < numClasses</code> for all <code>x</code> in <code>classOf</code>
	 * <li><code>x</code> in <code>classOf</code> for each <code>x</code> in [0, <code>numClasses</code>)
	 * </ul>
	 *
	 * @param eq the NiceClasses whose consistency should be checked
	 * @return <code>true</code> iff the input NiceClasses is consistent
	 */
	public static boolean checkConsistency(EqCls eq) {
		if (eq.numClasses < 0)
			return false;

		for (int x : eq.classOf)
			if (x < 0 || x >= eq.numClasses)
				return false;

		boolean[] hasMembers = new boolean[eq.numClasses];

		for (int x : eq.classOf)
			hasMembers[x] = true;

		for (boolean x : hasMembers)
			if (!x)
				return false;

		return true;
	}

	/**
	 * This static utility method is useful for making a NiceClasses structure
	 * from a root node array as returned by NiceUnionFind.
	 *
	 * It creates a copy of the input array with the values renamed to fit in
	 * the range <code>[0, numClasses)</code> where <code>numClasses</code>
	 * is the number of distinct values in the array.
	 *
     * <p>This "compressed" array is returned together with
     * the <code>numClasses</code> value as a NiceClasses structure.
	 *
	 * @param root Represents equivalence classes. <code>0 <= root[x] < root.length</code> for all x.
	 * @return a NiceClasses structure carrying the compressed array
	 */
	public static EqCls compress(int[] root) {
		for (int i = 0; i < root.length; i++)
			assert 0 <= root[i] && root[i] < root.length;

		int numClasses = 0;
		int[] classOf = new int[root.length];
		int[] newName = new int[root.length];
		boolean[] seen = new boolean[root.length];

		for (int i = 0; i < root.length; i++)
			if (!seen[root[i]]) {
				seen[root[i]] = true;
				newName[root[i]] = numClasses++;
			}

		for (int i = 0; i < root.length; i++)
			classOf[i] = newName[root[i]];

		return EqCls.createConsistent(numClasses, classOf);
	}

	/** "test" the thing */
	public static void main(String[] args) {
		Writer writer = new PrintWriter(new OutputStreamWriter(System.err));
		EqCls cls;

		cls = EqCls.compress(new int[] { 1, 1, 0, 5, 0, 0 });
		Print.printClasses(writer, cls);
		assert cls.numClasses == 3;
		assert cls.classOf[0] == cls.classOf[1];
		assert cls.classOf[2] == cls.classOf[4] && cls.classOf[2] == cls.classOf[5];
		for (int i = 0; i < cls.classOf.length; i++)
			assert(i == 3 || cls.classOf[i] != cls.classOf[3]);

		cls = EqCls.compress(new int[] { 1, 1, 1, 1 });
		Print.printClasses(writer, cls);
		assert cls.numClasses == 1;
		assert cls.classOf.length == 4;
		for (int c : cls.classOf)
			assert c == 0;
	}
}