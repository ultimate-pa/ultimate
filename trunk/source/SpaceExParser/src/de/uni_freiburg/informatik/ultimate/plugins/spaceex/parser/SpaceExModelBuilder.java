package de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.ast.SpaceExRootNode;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.automata.HybridAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.ComponentType;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.Sspaceex;

/**
 * Constructs SpaceEx Ultimate model representation.
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class SpaceExModelBuilder {

	private final ILogger mLogger;
	
	private final SpaceExRootNode mModel;
	
	public SpaceExModelBuilder(Sspaceex root, ILogger logger) {
		mLogger = logger;
	
		mModel = new SpaceExRootNode(root.getMath(), root.getVersion(), mLogger);
		
		parseComponents(root.getComponent());
	}
	
	public SpaceExRootNode getModel() {
		return mModel;
	}

	private void parseComponents(List<ComponentType> components) {
		for (final ComponentType c : components) {
			if (c.getBind().isEmpty()) {
				new HybridAutomaton(c, mLogger);
				addComponent(c);
			}
			else {
				addSystem(c);
			}
		}
	}
	
	private void addComponent(ComponentType component) {
		mModel.addComponent(component);
	}
	
	private void addSystem(ComponentType system) {
		mModel.addSystem(system);
	}
}
