
package jdd.internal.hashtest;



import jdd.util.math.Chi2Test;

public class Histogram {
	private int size, count;
	private Chi2Test c2t;

	public Histogram(int size) {
		this.size = size;
		reset();
	}

	// -------------------------------------

	public void reset() {
		count = 0;
		c2t = new Chi2Test(size);
	}

	public void add(int n) {
		n %= size;
		if(n < 0 || n>= size) {
			System.out.println("SHIT: " + n);
		}
		c2t.add(n);
		count++;

	}

	public void resize(int new_size) {
		if(new_size < 1)
		 {
			return; // error ?
		}

		size = new_size;
		reset();
	}
	public double getChi2() { return c2t.getChi2(); }
	public double getStandardDeviation() { return c2t.getStandardDeviation(); }

	// -------------------------------------

	public int getSize() { return size; }
	public int getSamples() { return count; }
	public int getCount(int n) {
		if(n >= 0 && n < size) {
			return c2t.getDistibution()[n];
		}
		return 0;
	}

}