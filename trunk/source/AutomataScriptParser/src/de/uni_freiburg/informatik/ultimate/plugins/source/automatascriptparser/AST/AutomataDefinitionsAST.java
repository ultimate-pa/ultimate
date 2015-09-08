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

import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

/**
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class AutomataDefinitionsAST extends AtsASTNode {

	/**
	 * 
	 */
	private static final long serialVersionUID = 302216547472553949L;
	
	private List<AutomatonAST> m_AutomataDefinitions;
	public AutomataDefinitionsAST() {
		super(null);
		m_AutomataDefinitions = new ArrayList<AutomatonAST>();
	}
	
	public AutomataDefinitionsAST(AutomatonAST a) {
		this();
		m_AutomataDefinitions.add(a);
	}

	public List<AutomatonAST> getListOfAutomataDefinitions() {
		return m_AutomataDefinitions;
	}

	public void addAutomaton(AutomatonAST a) {
		m_AutomataDefinitions.add(a);
		// I add the automaton also to the set of outgoing nodes, because of Jung Visualization
		addOutgoingNode(a);
	}
	
	public void addAutomata(List<AutomatonAST> atm) {
		m_AutomataDefinitions.addAll(atm);
	}
	public boolean hasAutomaton(AutomatonAST a) {
		return m_AutomataDefinitions.contains(a);
	}

	@Override
	public String toString() {
		StringBuilder builder = new StringBuilder();
		builder.append("AutomataDefinitions [");
		if (m_AutomataDefinitions != null) {
			builder.append("#AutomataDefinitions: ");
			builder.append(m_AutomataDefinitions.size());
		}
		builder.append("]");
		return builder.toString();
	}
	
	public boolean isEmpty() {
		return m_AutomataDefinitions.isEmpty();
	}
}
