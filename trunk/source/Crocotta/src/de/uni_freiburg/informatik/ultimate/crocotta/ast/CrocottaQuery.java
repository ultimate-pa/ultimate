package de.uni_freiburg.informatik.ultimate.crocotta.ast;

import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.core.lib.models.BasePayloadContainer;
import de.uni_freiburg.informatik.ultimate.core.lib.models.VisualizationNode;
import de.uni_freiburg.informatik.ultimate.core.model.models.ISimpleAST;
import de.uni_freiburg.informatik.ultimate.core.model.models.IWalkable;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class CrocottaQuery extends BasePayloadContainer implements ISimpleAST<CrocottaQuery, VisualizationNode> {

	private static final long serialVersionUID = 1L;
	// do not rename this field as auto-generated subclasses depend on it
	protected static final Map<Class<?>, Predicate<CrocottaQuery>> VALIDATORS = new HashMap<>();

	@Override
	public VisualizationNode getVisualizationGraph() {
		throw new UnsupportedOperationException();
	}

	@Override
	public List<IWalkable> getSuccessors() {
		return Collections.unmodifiableList(getOutgoingNodes());
	}

	@Override
	public List<CrocottaQuery> getOutgoingNodes() {
		throw new UnsupportedOperationException();
	}
}
