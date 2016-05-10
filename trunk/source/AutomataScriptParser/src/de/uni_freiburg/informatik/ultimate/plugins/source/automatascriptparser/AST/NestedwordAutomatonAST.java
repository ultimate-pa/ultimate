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
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.TransitionListAST.Pair;



/**
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class NestedwordAutomatonAST extends AutomatonAST {

	/**
	 * 
	 */
	private static final long serialVersionUID = 2260897609736623517L;
	
	private List<String> m_CallAlphabet;
	private List<String> m_InternalAlphabet;
	private List<String> m_ReturnAlphabet;
	
	private List<String> m_States;
	private List<String> m_InitialStates;
	private List<String> m_FinalStates;
	
	private Map<Pair<String, String>, Set<String>> m_InternalTransitions;
	private Map<Pair<String, String>, Set<String>> m_CallTransitions;
	private Map<String, Map<String, Map<String, Set<String>>>> m_ReturnTransitions;
	
	public NestedwordAutomatonAST(ILocation loc, String name) {
		super(loc);
		m_CallAlphabet = new ArrayList<String>();
		m_InternalAlphabet = new ArrayList<String>();
		m_ReturnAlphabet = new ArrayList<String>();
		m_States = new ArrayList<String>();
		m_InitialStates = new ArrayList<String>();
		m_FinalStates = new ArrayList<String>();
		m_InternalTransitions = new HashMap<Pair<String,String>, Set<String>>();
		m_CallTransitions = new HashMap<Pair<String,String>, Set<String>>();
		m_ReturnTransitions = new HashMap<String, Map<String, Map<String, Set<String>>>>();
		m_Name = name;
		
	}

	public List<String> getCallAlphabet() {
		return m_CallAlphabet;
	}

	public void setCallAlphabet(List<String> m_CallAlphabet) {
		if (m_CallAlphabet != null)
			this.m_CallAlphabet = m_CallAlphabet;
	}

	public List<String> getInternalAlphabet() {
		return m_InternalAlphabet;
	}

	public void setInternalAlphabet(List<String> m_InternalAlphabet) {
		if (m_InternalAlphabet != null)
			this.m_InternalAlphabet = m_InternalAlphabet;
	}

	public List<String> getReturnAlphabet() {
		return m_ReturnAlphabet;
	}

	public void setReturnAlphabet(List<String> m_ReturnAlphabet) {
		if (m_ReturnAlphabet != null)
			this.m_ReturnAlphabet = m_ReturnAlphabet;
	}
	
	public void setStates(List<String> states) {
		if (states != null)
			m_States = states;
	}
	
	public void setInitialStates(List<String> initStates) {
		if (initStates != null)
			m_InitialStates = initStates;
	}
	public void setFinalStates(List<String> finStates) {
		if (finStates != null)
			m_FinalStates = finStates;
	}

	public List<String> getStates() {
		return m_States;
	}

	public List<String> getInitialStates() {
		return m_InitialStates;
	}

	public List<String> getFinalStates() {
		return m_FinalStates;
	}

	
	public Map<Pair<String, String>, Set<String>> getInternalTransitions() {
		return m_InternalTransitions;
	}

	public void setInternalTransitions(TransitionListAST internalTransitions) {
		if (internalTransitions != null)
			this.m_InternalTransitions = internalTransitions.getTransitions();
	}

	public Map<Pair<String, String>, Set<String>> getCallTransitions() {
		return m_CallTransitions;
	}

	public void setCallTransitions(TransitionListAST callTransitions) {
		if (callTransitions != null)
			this.m_CallTransitions = callTransitions.getTransitions();
	}

	public Map<String, Map<String, Map<String, Set<String>>>> getReturnTransitions() {
		return m_ReturnTransitions;
	}

	public void setReturnTransitions(TransitionListAST returnTransitions) {
		if (returnTransitions != null)
			this.m_ReturnTransitions = returnTransitions.getReturnTransitions();
	}

	@Override
	public String toString() {
		StringBuilder builder = new StringBuilder();
		builder.append("NestedwordAutomaton(" + m_Name + "): " + "[#call_alph: ");
		builder.append(m_CallAlphabet.size());
		builder.append(" #int_alph: ");
		builder.append(m_InternalAlphabet.size());
		builder.append(" #return_alph: ");
		builder.append(m_ReturnAlphabet.size());
		builder.append(" #States: ");
		builder.append(m_States.size());
		builder.append(" #init_states: ");
		builder.append(m_InitialStates.size());
		builder.append(" #final_states: ");
		builder.append(m_FinalStates.size());
		builder.append(" #int_trans: ");
		builder.append(m_InternalTransitions.size());
		builder.append(" #call_trans: ");
		builder.append(m_CallTransitions.size());
		builder.append(" #ret_trans: ");
		builder.append(m_ReturnTransitions.size());
		builder.append("]");
		return builder.toString();
	}

	

}
