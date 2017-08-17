package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util;

import java.util.BitSet;
import java.util.EmptyStackException;

// modified from https://www.cs.colorado.edu/~main/edu/colorado/collections/IntStack.java
public class IntStack implements Cloneable {

	private int[] data;
	private int top;
	private IntSet bits; // no duplicate elements

	public IntStack() {
		final int INITIAL_CAPACITY = 30;
		top = 0;
		data = new int[INITIAL_CAPACITY];
		bits = UtilIntSet.newIntSet();
	}

	public IntStack(int initialCapacity) {
		if (initialCapacity < 0)
			throw new IllegalArgumentException("Negative initialCapacity " + initialCapacity);
		top = 0;
		data = new int[initialCapacity];
		bits = UtilIntSet.newIntSet();
	}
	

	public Object clone() {
		IntStack result;

		try {
			result = (IntStack) super.clone();
		} catch (CloneNotSupportedException e) {
			throw new RuntimeException("This class does not implement Cloneable");
		}

		result.data = (int[]) data.clone();
		result.bits = bits.clone();
		return result;
	}

	public void ensureCapacity(int minimumCapacity) {
		int biggerArray[];

		if (data.length < minimumCapacity) {
			biggerArray = new int[minimumCapacity];
			System.arraycopy(data, 0, biggerArray, 0, top);
			data = biggerArray;
		}
	}

	public int getCapacity() {
		return data.length;
	}

	public boolean isEmpty() {
		return (top == 0);
	}

	public int peek() {
		if (top == 0)
			throw new EmptyStackException();
		return data[top - 1];
	}

	public int pop() {
		if (top == 0)
			throw new EmptyStackException();
		bits.clear(data[top-1]);
		return data[--top];
	}

	public void push(int item) {
		if (top == data.length) {
			// may overflow
			ensureCapacity(top * 2 + 1);
		}
		data[top] = item;
		bits.set(item);
		++ top;
	}
	
	public boolean contains(int item) {
		return bits.get(item);
	}
	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		if(isEmpty()) return "[]";
		sb.append("[" + data[0]);
		for(int i = 1; i < top; i ++) {
			sb.append("," + data[i]);
		}
		sb.append("]");
		return sb.toString();
	}
	
	public IntSet getItems() {
		return bits.clone();
	}
	
	public int get(int index) {
		if(index < 0 || index >= top) throw new RuntimeException("Index out of boundary");
		return data[index];
	}


	public int size() {
		return top;
	}

}
