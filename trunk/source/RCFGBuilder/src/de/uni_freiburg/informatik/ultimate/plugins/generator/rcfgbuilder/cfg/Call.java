/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE RCFGBuilder plug-in.
 * 
 * The ULTIMATE RCFGBuilder plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE RCFGBuilder plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE RCFGBuilder plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE RCFGBuilder plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE RCFGBuilder plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.ICallAction;

/**
 * Edge in a recursive control flow graph that represents a procedure call.
 * Opposed to a Summary this represents only the execution from the position
 * directly before the call statement to the initial position of the called
 * procedure. A Call object provides two auxiliary TransitionFormulas
 * m_OldVarsAssignment and m_GlobalVarsAssignment which are used for computing
 * nested interpolants. Let g_1,...,g_n be the global variables modified by the
 * called procedure, then m_OldVarsAssignment represents the update old(g_1),
 * ... old(g_n):=g_1,...,g_n and m_GlobalVarsAssignment represents the update
 * g_1,...,g_n:=old(g_1), ... old(g_n)
 * 
 * @author heizmann@informatik.uni-freiburg.de
 */
public class Call extends CodeBlock implements ICallAction {

	private static final long serialVersionUID = 5047439633229508126L;

	protected CallStatement m_CallStatement;
	protected String m_PrettyPrintedStatements;

	/**
	 * The published attributes. Update this and getFieldValue() if you add new
	 * attributes.
	 */
	private final static String[] s_AttribFields = { "CallStatement", "PrettyPrintedStatements", "TransitionFormula",
			"OccurenceInCounterexamples" };

	Call(int serialNumber, ProgramPoint source, ProgramPoint target, CallStatement st, Logger logger) {
		super(serialNumber, source, target, logger);
		m_CallStatement = st;
		m_PrettyPrintedStatements = BoogiePrettyPrinter.print(st);
	}
	
	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field == "CallStatement") {
			return m_CallStatement;
		} else if (field == "PrettyPrintedStatements") {
			return m_PrettyPrintedStatements;
		} else {
			return super.getFieldValue(field);
		}
	}

	public CallStatement getCallStatement() {
		return m_CallStatement;
	}

	public String getPrettyPrintedStatements() {
		return m_PrettyPrintedStatements;
	}

	@Override
	public String toString() {
		return BoogiePrettyPrinter.print(m_CallStatement);
	}

	@Override
	public TransFormula getLocalVarsAssignment() {
		return getTransitionFormula();
	}

}
