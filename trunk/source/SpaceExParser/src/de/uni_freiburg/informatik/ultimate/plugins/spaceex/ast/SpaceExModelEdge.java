package de.uni_freiburg.informatik.ultimate.plugins.spaceex.ast;

import de.uni_freiburg.informatik.ultimate.model.structure.ModifiableMultigraphEdge;

public class SpaceExModelEdge extends ModifiableMultigraphEdge<SpaceExModel, SpaceExModelEdge> {

	protected SpaceExModelEdge(SpaceExModel source, SpaceExModel target) {
	    super(source, target);

	    setSource(source);
	    setTarget(target);
    }

	/**
	 * Serialization ID
	 */
	private static final long serialVersionUID = 1L;

}
