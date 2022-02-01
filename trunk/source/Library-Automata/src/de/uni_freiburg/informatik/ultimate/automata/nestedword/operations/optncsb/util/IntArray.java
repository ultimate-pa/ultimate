/*
 * Copyright (C) 2017 Yong Li (liyong@ios.ac.cn)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util;

import java.util.BitSet;

public class IntArray implements Cloneable {
	private int[] data;
	private int size;
	private BitSet bits;
	
	public IntArray() {
		final int INITIAL_CAPACITY = 30;
		data = new int[INITIAL_CAPACITY];
		size = 0;
		bits = new BitSet();
	}

	public IntArray(int initialCapacity) {
		if (initialCapacity < 0)
			throw new IllegalArgumentException("Negative initialCapacity " + initialCapacity);
		data = new int[initialCapacity];
		size = 0;
		bits = new BitSet();
	}

	public Object clone() {
		IntArray result;
		try {
			result = (IntArray) super.clone();
		} catch (CloneNotSupportedException e) {
			throw new RuntimeException("This class does not implement Cloneable");
		}
		result.data = (int[]) data.clone();
		result.size = size;
		result.bits = (BitSet) bits.clone();
		return result;
	}

	public void ensureCapacity(int minimumCapacity) {
		int biggerArray[];

		if (data.length < minimumCapacity) {
			biggerArray = new int[minimumCapacity];
			System.arraycopy(data, 0, biggerArray, 0, size);
			data = biggerArray;
		}
	}

	public boolean isEmpty() {
		return (size == 0);
	}

	public void set(int index, int item) {
		if(index != size) throw new RuntimeException("Index should be increasing");
		while(index > data.length) {
			ensureCapacity((int)(data.length * 1.5) + 1);
		}
		bits.set(size);
		data[size ++] = item;
	}
	
	public void clear(int index) {
		if(index < 0 || index >= size) throw new RuntimeException("Index out of bound: index " + index + " size" + size);
		bits.clear(index); 
	}
	
	public boolean isDefined(int index) {
		if(index < 0 || index >= size) throw new RuntimeException("Index out of bound: index " + index + " size" + size);
		return bits.get(index);
	}
	
	public int get(int index) {
		if(index >= size) throw new RuntimeException("Index should be increasing");
		return data[index];
	}
	
	public int peek() {
		if(size == 0) throw new RuntimeException("Empty array");
		return data[size - 1];
	}

	public void delete() {
		if(size == 0) throw new RuntimeException("Empty array");
		size --;
		bits.clear(size);
	}
	
	public int pop() {
		if(size == 0) throw new RuntimeException("Empty array");
		bits.clear(size - 1);
		return data[-- size];
	}
	
	public int size() {
		return size;
	}
	
	public int getCapacity() {
		return data.length;
	}
	
	public String toString() {
		if(size == 0) return "[]";
		StringBuilder sb = new StringBuilder();
		sb.append("[" + data[0]);
		for(int i = 1; i < size; i ++) {
			sb.append(", " + data[i]);
		}
		sb.append("]");
		return sb.toString();
	}
	
	public static void main(String[] args) {
		IntArray arr = new IntArray();
		arr.set(0, 1);
		arr.set(1, 3);
		arr.set(2, 2);
		arr.set(3, 4);
		arr.set(4, 6);
		
		System.out.println(arr + ", " + arr.getCapacity() + ","+ arr.size());
		
		System.out.println(arr.peek());
		arr.pop();
		System.out.println(arr.peek());
//		arr.set(0, 0);
	}
}
