/*
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE SpaceExParser plug-in.
 * 
 * The ULTIMATE SpaceExParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE SpaceExParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SpaceExParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SpaceExParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE SpaceExParser plug-in grant you additional permission 
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.spaceex.ast;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.ComponentType;

/**
 * This is the root node of any SpaceEx model. It contains all components, shared variables, etc.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class SpaceExRootNode extends SpaceExNode {

	/**
	 * Serialization ID.
	 */
	private static final long serialVersionUID = 1L;
	private final Map<String, ComponentType> mComponents;
	private final Map<String, ComponentType> mSystems;

	private final ILogger mLogger;

	public SpaceExRootNode(String math, String version, ILogger logger) {
		getPayload().getAnnotations().put("RootNodeAnnotation", new RootNodeAnnotation(math, version));

		mComponents = new HashMap<String, ComponentType>();
		mSystems = new HashMap<String, ComponentType>();
		mLogger = logger;
	}

	public void addComponent(ComponentType component) {

	}

	public void addSystem(ComponentType system) {
		if (system.getBind().isEmpty()) {
			throw new UnsupportedOperationException("A system component must contain at least one bind.");
		}

		mSystems.put(system.getId(), system);

		final SystemNode systemNode = new SystemNode(system, mLogger);
		final SpaceExRootEdge componentEdge = new SpaceExRootEdge(this, systemNode);
		addOutgoing(componentEdge);

	}

	public ComponentType getSystem(String name) {
		return mSystems.get(name);
	}

	public ComponentType getComponent(String name) {
		return mComponents.get(name);
	}

}
