package de.uni_freiburg.informatik.ultimate.util;


import java.util.HashSet;
import java.util.Set;

import org.junit.Assert;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.DisjointSets;

public class DisjointSetsTest {
	
	@Test
	public void test1() {
		final Set<Integer> elements = new HashSet<>();
		final Set<Integer> odds = new HashSet<>();
		final Set<Integer> evens = new HashSet<>();
		for (int i = 1; i <= 10; ++i) {
			elements.add(i);
			if (i % 2 == 0) {
				evens.add(i);
			} else {
				odds.add(i);
			}
		}
		final DisjointSets<Integer> ints = new DisjointSets<>(elements);
		for (int i = 1; i <= 10; ++i) {
			for (int j = 1; j <= 10; ++j) {	
				if (i != j) {
					Assert.assertFalse(ints.equiv(i, j));
				}
			}
		}
		System.out.println(ints.toString());
		Assert.assertEquals(10, ints.size());
		Assert.assertEquals(10, elements.size());
		Assert.assertEquals(5,  odds.size());
		Assert.assertEquals(5,  evens.size());
		
		for (int i = 2; i < 10; i += 2) {
			if (i % 2 == 0) {
				ints.union(i, i + 2);
			}
		}

		for (int i = 1; i < 9; i += 2) {
			if (i % 2 == 1) {
				ints.union(i, i + 2);
			}
		}

		System.out.println(ints.toString());
		Assert.assertEquals(2, ints.size());
		Assert.assertEquals(odds, ints.getPartition(1));
		Assert.assertEquals(evens, ints.getPartition(2));
		
		for (int i = 1; i < 10; ++i) {
			ints.union(i, 10);
		}

		System.out.println(ints.toString());
		Assert.assertEquals(elements, ints.getPartition(1));
	}
}
