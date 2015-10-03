/**
 * 
 */
package soottocfg.util;

/**
 * @author schaef
 *
 */
public class Pair<A, B> {

	private final A first;
	private final B second;
	
	/**
	 * 
	 */
	public Pair(A first, B second) {
		this.first = first;
		this.second = second;
	}

	public A getFirst() {
		return first;
	}
	
	public B getSecond() {
		return second;
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("(");
		sb.append(first);
		sb.append(",");
		sb.append(second);
		sb.append(")");
		return sb.toString();
	}
}
