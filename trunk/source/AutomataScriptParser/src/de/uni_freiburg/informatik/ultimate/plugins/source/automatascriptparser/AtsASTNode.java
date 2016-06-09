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
import de.uni_freiburg.informatik.ultimate.core.model.models.Payload;



/***
 * AST Node for AutomataScript parser.
 * @author musab@informatik.uni-freiburg.de
 */

public class AtsASTNode extends BaseAST<AtsASTNode> {

	
	private static final long serialVersionUID = 8077752308820134631L;
	protected List<AtsASTNode> mchildren;
	protected AtsASTNode mparent;
	// The type of the returned value
	protected Class<?> mreturnType;
	// The type the children of this node should have.
	protected Class<?> mexpectingType;

	private Map<Class<?>, Class<?>> mprimitiveToClassTypes;
	
 	public AtsASTNode(ILocation loc) {
 		super(new Payload(loc));
		mchildren = new ArrayList<AtsASTNode>();
		mparent = null;
		mprimitiveToClassTypes = new HashMap<Class<?>, Class<?>>();
		mprimitiveToClassTypes.put(int.class, Integer.class);
		mprimitiveToClassTypes.put(boolean.class, Boolean.class);
	}
	
//	public AtsASTNode(ILocation loc) {
//		super(new Payload(loc, "AtsASTNode"));
//		mchildren = new ArrayList<AtsASTNode>();
//		mparent = null;
//		mlocation = loc;
//	}
	
	public AtsASTNode(ILocation loc, AtsASTNode par) {
		super(new Payload(loc));
		mchildren = new ArrayList<AtsASTNode>();
		mparent = par;
	}

	
	@Override
	public AtsASTNode getIncomingNode() {
		return mparent;
	}

	@Override
	public List<AtsASTNode> getOutgoingNodes() {
		return mchildren;
	}
	
	
	public boolean addIncomingNode(AtsASTNode par) {
		mparent = par;
		return true;
	}

	
	public boolean addOutgoingNode(AtsASTNode element) {
		mchildren.add(element);
		if (element != null) {
			element.addIncomingNode(this);
		}
		return true;
	}
	
		
	public Class<?> getReturnType() {
		return mreturnType;
	}
	
	public Class<?> getExpectingType() {
		return mexpectingType;
	}

	public void setType(Class<?> type) {
		Class<?> classType = type;
		if (mprimitiveToClassTypes.containsKey(type)) {
			classType = mprimitiveToClassTypes.get(type);
		}
		setReturnType(classType);
		setExpectingType(classType);
	}
	
	public void setReturnType(Class<?> type) {
		mreturnType = type;
	}
	
	public void setExpectingType(Class<?> type) {
		mexpectingType = type;
	}
	
	
	public ILocation getLocation() {
		return getPayload().getLocation();
	}

	
	/**
	 * 
	 * @return String representation of this AtsASTNode
	 */
	public String getAsString() {
		final StringBuilder builder = new StringBuilder();
		for (final AtsASTNode n : mchildren) {
			builder.append(n.getAsString());
		}
		return builder.toString();
	}
	
}
