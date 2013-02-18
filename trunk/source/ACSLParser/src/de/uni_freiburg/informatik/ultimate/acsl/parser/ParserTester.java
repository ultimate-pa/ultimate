/**
 * Small test for the ACSL Parser.
 */
package de.uni_freiburg.informatik.ultimate.acsl.parser;

import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;

/**
 * Use this class only for testing purposes.
 * 
 * @author Stefan Wissert
 */
public class ParserTester {

	/**
	 * Main method.
	 * 
	 * @param args string arguments.
	 */
	public static void main(String[] args) {
		StringBuffer buf = new StringBuffer();
		buf.append("gstart ");
		buf.append("requires add[1] >= 0 ;");
		buf.append("assigns \\nothing;");
		buf.append("ensures -1 <= \\result <= n -1;");
		buf.append("behavior success:");
		buf.append("	ensures \\result >= 0 ;");
		buf.append("behavior failure:");
		buf.append("	assumes t_is_sorted : x > 0;");
		buf.append(" 	ensures \\result == -1; ");
		
		System.out.println(buf.toString());
		try {
			ACSLNode node = Parser.parseComment(buf.toString(), 0, 0);
			System.out.println(node);
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
}
