/*
 * Copyright (C) 2016 Mostafa M.A. (mostafa.amin93@gmail.com)
 * Copyright (C) 2014-2016 University of Freiburg
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
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
package de.uni_freiburg.informatik.ultimate.automata.tree;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;

/**
 * 
 * @author Mostafa M.A. (mostafa.amin93@gmail.com)
 *
 * @param <LETTER>
 * @param <STATE>
 */
public class PostfixTree<LETTER, STATE> {

	private final ArrayList<LETTER> postFix;
	private final ArrayList<STATE> postFixStates;
	private final ArrayList<Integer> depths;

	private final ArrayList<Integer> startIdx;

	private final HashMap<Integer, Integer> mBeg;

	public List<LETTER> getPostFix() {
		return postFix;
	}

	public List<Integer> getStartIdx() {
		return startIdx;
	}

	public List<STATE> getPostFixStates() {
		return postFixStates;
	}

	/***
	 * Construct a postfix Tree from a treeRun
	 * @param run
	 */
	public PostfixTree(final TreeRun<LETTER, STATE> run) {
		postFix = new ArrayList<>();
		postFixStates = new ArrayList<>();
		startIdx = new ArrayList<>();
		depths = new ArrayList<>();
		mBeg = new HashMap<>();
		constructTree(run, 0);
	}

	private void addSymbol(final LETTER lt, final STATE st, final int depth) {
		if (!mBeg.containsKey(depth)) {
			mBeg.put(depth, depths.size());
		}
		startIdx.add(mBeg.get(depth));
		postFix.add(lt);
		postFixStates.add(st);
		depths.add(depth);
	}

	private void constructTree(final TreeRun<LETTER, STATE> run, final int depth) {

		constructSubtrees(run.getChildren().iterator(), depth);
		if (run.getRootSymbol() != null) {
			addSymbol(run.getRootSymbol(), run.getRoot(), depth);
		}
	}

	private void constructSubtrees(final Iterator<TreeRun<LETTER, STATE>> it, final int depth) {
		if (!it.hasNext()) {
			return;
		}
		constructTree(it.next(), depth);
		constructSubtrees(it, depth + 1);
	}

	public static void main(String[] args) {

		TreeRun<Character, Integer> r9 = new TreeRun<Character, Integer>(9);
		TreeRun<Character, Integer> r10 = new TreeRun<Character, Integer>(10);
		TreeRun<Character, Integer> r11 = new TreeRun<Character, Integer>(11);
		TreeRun<Character, Integer> r12 = new TreeRun<Character, Integer>(12);

		ArrayList<TreeRun<Character, Integer>> rr3 = new ArrayList<>();
		rr3.add(r9);
		TreeRun<Character, Integer> r3 = new TreeRun<Character, Integer>(3, 'y', rr3);

		ArrayList<TreeRun<Character, Integer>> rr5 = new ArrayList<>();
		rr5.add(r10);
		TreeRun<Character, Integer> r5 = new TreeRun<Character, Integer>(5, 'z', rr5);

		ArrayList<TreeRun<Character, Integer>> rr7 = new ArrayList<>();
		rr7.add(r11);
		TreeRun<Character, Integer> r7 = new TreeRun<Character, Integer>(7, 'u', rr7);

		ArrayList<TreeRun<Character, Integer>> rr8 = new ArrayList<>();
		rr8.add(r12);
		TreeRun<Character, Integer> r8 = new TreeRun<Character, Integer>(8, 'v', rr8);

		ArrayList<TreeRun<Character, Integer>> rr6 = new ArrayList<>();
		rr6.add(r7);
		rr6.add(r8);
		TreeRun<Character, Integer> r6 = new TreeRun<Character, Integer>(6, 'a', rr6);

		ArrayList<TreeRun<Character, Integer>> rr4 = new ArrayList<>();
		rr4.add(r5);
		TreeRun<Character, Integer> r4 = new TreeRun<Character, Integer>(4, 'b', rr4);

		ArrayList<TreeRun<Character, Integer>> rr2 = new ArrayList<>();
		rr2.add(r3);
		TreeRun<Character, Integer> r2 = new TreeRun<Character, Integer>(2, 'c', rr2);

		ArrayList<TreeRun<Character, Integer>> rr1 = new ArrayList<>();
		rr1.add(r2);
		rr1.add(r4);
		rr1.add(r6);
		TreeRun<Character, Integer> r1 = new TreeRun<Character, Integer>(1, 'x', rr1);

		PostfixTree<Character, Integer> tt = new PostfixTree<>(r1);
		System.out.println(r1.toString());
		System.out.println(tt.postFix);
		System.out.println(tt.depths);
		System.out.println(tt.startIdx);
		System.out.println(tt.postFixStates);

		HashMap<Integer, Integer> map = new HashMap<>();
		for (int i = 1; i <= 12; ++i)
			map.put(i, i * i + 1000);

		PostfixTree<Character, Integer> tt2 = new PostfixTree<>(r1.reconstruct(map));

		System.out.println(r1.reconstruct(map).toString());
		System.out.println(tt2.postFix);
		System.out.println(tt2.depths);
		System.out.println(tt2.startIdx);
		System.out.println(tt2.postFixStates);

	}
}
