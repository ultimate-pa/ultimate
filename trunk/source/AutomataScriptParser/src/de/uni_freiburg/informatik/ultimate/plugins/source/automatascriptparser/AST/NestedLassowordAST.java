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


import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

/**
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class NestedLassowordAST extends AtsASTNode {

	/**
	 * 
	 */
	private static final long serialVersionUID = -2004814510723903218L;
	private final NestedwordAST mnw1;
	private final NestedwordAST mnw2;
	
	public NestedLassowordAST(ILocation loc, NestedwordAST nw1, NestedwordAST nw2) {
		super(loc);
		mnw1 = nw1;
		mnw2 = nw2;
		setType(de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord.class);
	}

	@Override
	public String toString() {
		final StringBuilder b = new StringBuilder();
		b.append("NestedLassoword: [Nw1: ");
		b.append(mnw1);
		b.append(", Nw2: ");
		b.append(mnw2);
		b.append("]");
		return b.toString();
	}
	
	public NestedwordAST getStem() {
		return mnw1;
	}
	
	public NestedwordAST getLoop() {
		return mnw2;
	}

	@Override
	public String getAsString() {
		return mnw1.getAsString().substring(0, mnw1.getAsString().length() - 1) + 
				", " + mnw2.getAsString().substring(1);
	}
	
	
}
