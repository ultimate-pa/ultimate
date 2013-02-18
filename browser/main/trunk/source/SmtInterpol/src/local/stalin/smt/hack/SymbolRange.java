package local.stalin.smt.hack;

public class SymbolRange {
	public int first,last;
	public SymbolRange(int fn) {
		first = last = fn;
	}
	public SymbolRange(SymbolRange other) {
		this(other.first,other.last);
	}
	private SymbolRange(int fn,int ln) {
		first = fn;
		last = ln;
	}
	public void update(int fn) {
		first = first > fn ? fn : first;
		last = last < fn ? fn : last;
	}
	public boolean isTheoryExtension() {
		return first == -1;
	}
	public final static SymbolRange THEORYEXTENSION = new SymbolRange(-1,Integer.MAX_VALUE);
	public String toString() {
		return isTheoryExtension() ? 
				"Theory Extension" : "[" + first + "," + last + "]";
	}
	public SymbolRange combine(SymbolRange range) {
		return new SymbolRange(Math.max(first,range.first),Math.min(last,range.last));
	}
}
