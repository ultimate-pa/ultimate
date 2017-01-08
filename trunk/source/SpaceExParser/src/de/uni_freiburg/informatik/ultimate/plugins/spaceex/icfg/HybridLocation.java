/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.spaceex.icfg;

import de.uni_freiburg.informatik.ultimate.core.model.models.Payload;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

/**
 * @author Julian Loeffler (loefflju@informatik.uni-freiburg.de)
 *
 */
public class HybridLocation extends IcfgLocation {
	
	private static final long serialVersionUID = 6579275768598186922L;
	
	public HybridLocation(String debugIdentifier, String procedure, Payload payload) {
		super(debugIdentifier, procedure, payload);
	}
	
}
