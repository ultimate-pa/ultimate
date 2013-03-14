/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.test.util;

import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;

/**
 * This is a static store, to share the generated RCFG with all test classes.
 * 
 * @author Stefan Wissert
 * 
 */
public class RCFGStore {

	private static RCFGNode rcfgNode;

	/**
	 * @param node
	 */
	public static void setRCFG(RCFGNode node) {
		rcfgNode = node;
	}

	/**
	 * @return
	 */
	public static RCFGNode getRCFG() {
		if (rcfgNode == null) {
			throw new IllegalArgumentException(
					"There is no RCFG-Node present (which is set by the Observer)"
							+ " , you cannot run the unit tests, without running"
							+ " Ultimate. To run Unit-Tests, you have to set the"
							+ " special observer in the settings.");
		}
		return rcfgNode;
	}

}
