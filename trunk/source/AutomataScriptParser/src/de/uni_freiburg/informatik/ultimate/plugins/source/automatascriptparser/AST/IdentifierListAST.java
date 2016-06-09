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

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

/**
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class IdentifierListAST extends AtsASTNode {

	/**
	 * 
	 */
	private static final long serialVersionUID = -7741847124495330627L;
	private final List<String> midList;
	
	
	public IdentifierListAST(ILocation loc) {
		super(loc);
		midList = new ArrayList<String>();
	}
	
	public void addId(String id) {
		midList.add(id);
	}
	
	public List<String> getIdentifierList() {
		return midList;
	}
	
	/**
	 * Use at your own risk
	 * @param i this parameter is the index of the identifier you want to get
	 * @return the identifier at index i, or throws an exception
	 */
	public String getIdentifier(int i) {
		return midList.get(i);
	}
	
	// Some methods needed for petri nets
	/**
	 * Indicates whether this list contains 2 identifiers.
	 * @return true iff it contains exactly 2 identifiers, otherwise false.
	 */
	public boolean isPair() {
		return (midList.size() == 2);
	}

	@Override
	public String getAsString() {
		final StringBuilder builder = new StringBuilder();
		for (final String id : midList) {
			builder.append(id + " ");
		}
		return builder.toString();
	}
	
	
	
}
