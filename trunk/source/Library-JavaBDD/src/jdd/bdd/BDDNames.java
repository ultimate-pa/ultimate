
package jdd.bdd;

import jdd.util.NodeName;

/** BDD-style node naming: v1..vn */
public class BDDNames implements NodeName {
	public BDDNames() { }

	@Override
	public String zero() { return "FALSE"; }
	@Override
	public String one() { return "TRUE"; }
	@Override
	public String zeroShort() { return "0"; }
	@Override
	public String oneShort() { return "1"; }

	@Override
	public String variable(int n) {
		if(n < 0) {
			return "(none)";
		}
		return "v" + (n + 1);
	}
}
