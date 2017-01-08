/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.spaceex.icfg;

import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;

/**
 * @author Julian Loeffler (loefflju@informatik.uni-freiburg.de)
 *
 */
public class HybridEdge extends IcfgEdge {
	
	private static final long serialVersionUID = 4818538993200200344L;
	
	protected HybridEdge(IcfgLocation source, IcfgLocation target, IPayload payload) {
		super(source, target, payload);
	}
	
	@Override
	public UnmodifiableTransFormula getTransformula() {
		// TODO Auto-generated method stub
		return null;
	}
	
}
