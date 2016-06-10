package de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.ast.SpaceExRootNode;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.HybridSystem;

/**
 * Constructs SpaceEx Ultimate model representation.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class SpaceExModelBuilder {

	private final ILogger mLogger;

	private final SpaceExRootNode mModel;

	public SpaceExModelBuilder(HybridSystem system, ILogger logger) {
		mLogger = logger;

		mModel = null;
	}

	public SpaceExRootNode getModel() {
		return mModel;
	}
}
