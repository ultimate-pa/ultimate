
package jdd.zdd;

import jdd.util.NodeName;

/*
 * Helper class for giving name to Z-BDD nodes.
 *
 * @see NodeName
 */

public class ZDDNames implements  NodeName {

	@Override
	public String zero() { return "emptyset"; }
	@Override
	public String one() { return "base"; }
	@Override
	public String zeroShort() { return "{}"; }
	@Override
	public String oneShort() { return "{{}}"; }

	@Override
	public String variable(int n) {
		if(n < 0) {
			return "(none)";
		}
		return "v" + (n + 1);
	}
}
