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
/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;


import de.uni_freiburg.informatik.ultimate.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

import java.util.ArrayList;
import java.util.List;


/**
 * @author musab@informatik.uni-freiburg.de
 *
 */

public class VariableDeclarationAST extends AtsASTNode {
    /**
	 * 
	 */
	private static final long serialVersionUID = 6868411705150725931L;
	private List<String> m_identifiers;
    
    public VariableDeclarationAST(ILocation loc, String identifier) {
    	super(loc);
    	m_identifiers = new ArrayList<String>();
    	m_identifiers.add(identifier);
    }
    
    public List<String> getIdentifiers() {
		return m_identifiers;
	}

	public void addVariable(String identifier) {
    	m_identifiers.add(identifier);
    }
	
	public void addVariables(List<String> identifiers) {
		for (String id : identifiers) {
			m_identifiers.add(id);
		}
	}

	@Override
	public String toString() {
		return "VariableDeclaration [Vars: " + m_identifiers + "]";
	}

	@Override
	public String getAsString() {
		StringBuilder builder = new StringBuilder();
		builder.append(m_returnType.getSimpleName());
		for (String id : m_identifiers) {
			builder.append(" " + id);
		}
		if (m_children.size() == 1) {
			builder.append(" = " + m_children.get(0).getAsString());
		}
		return builder.toString();
	}
	
	
}
