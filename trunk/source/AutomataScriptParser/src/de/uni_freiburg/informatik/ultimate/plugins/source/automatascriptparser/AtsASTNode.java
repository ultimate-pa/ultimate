/*
 * Copyright (C) 2013-2015 Betim Musa (musab@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE AutomataScriptParser plug-in.
 * 
 * The ULTIMATE AutomataScriptParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE AutomataScriptParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AutomataScriptParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AutomataScriptParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AutomataScriptParser plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.lib.models.BaseAST;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/***
 * AST Node for AutomataScript parser.
 * 
 * @author musab@informatik.uni-freiburg.de
 */

public class AtsASTNode extends BaseAST<AtsASTNode> {

	private static final long serialVersionUID = 8077752308820134631L;
	protected List<AtsASTNode> mChildren;
	protected AtsASTNode mParent;
	// The type of the returned value
	protected Class<?> mReturnType;
	// The type the children of this node should have.
	protected Class<?> mExpectingType;

	private final Map<Class<?>, Class<?>> mPrimitiveToClassTypes;

	public AtsASTNode(final ILocation loc) {
		super();
		loc.annotate(this);
		mChildren = new ArrayList<>();
		mParent = null;
		mPrimitiveToClassTypes = new HashMap<>();
		mPrimitiveToClassTypes.put(int.class, Integer.class);
		mPrimitiveToClassTypes.put(boolean.class, Boolean.class);
	}

	@Override
	public AtsASTNode getIncomingNode() {
		return mParent;
	}

	@Override
	public List<AtsASTNode> getOutgoingNodes() {
		return mChildren;
	}

	public boolean addIncomingNode(final AtsASTNode par) {
		mParent = par;
		return true;
	}

	public boolean addOutgoingNode(final AtsASTNode element) {
		mChildren.add(element);
		if (element != null) {
			element.addIncomingNode(this);
		}
		return true;
	}

	public Class<?> getReturnType() {
		return mReturnType;
	}

	public Class<?> getExpectingType() {
		return mExpectingType;
	}

	public void setType(final Class<?> type) {
		Class<?> classType = type;
		if (mPrimitiveToClassTypes.containsKey(type)) {
			classType = mPrimitiveToClassTypes.get(type);
		}
		setReturnType(classType);
		setExpectingType(classType);
	}

	public void setReturnType(final Class<?> type) {
		mReturnType = type;
	}

	public void setExpectingType(final Class<?> type) {
		mExpectingType = type;
	}

	public ILocation getLocation() {
		return ILocation.getAnnotation(this);
	}

	/**
	 * 
	 * @return String representation of this AtsASTNode
	 */
	public String getAsString() {
		final StringBuilder builder = new StringBuilder();
		for (final AtsASTNode n : mChildren) {
			builder.append(n.getAsString());
		}
		return builder.toString();
	}

}
