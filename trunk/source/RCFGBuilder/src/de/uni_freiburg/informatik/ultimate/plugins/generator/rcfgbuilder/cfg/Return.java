/*
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IReturnAction;

/**
 * Edge in a recursive control flow graph that represents the return from a
 * called procedure. This represents the execution starting from the position
 * directly before the return statement (resp. the last position of a procedure
 * if there is no return statement) to the position after the corresponding call
 * statement. The update of the variables of the calling procedure is defined in
 * the TransFormula.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class Return extends CodeBlock implements IReturnAction {

	private static final long serialVersionUID = 3561826943033450950L;

	private final Call m_CorrespondingCall;

	Return(int serialNumber, ProgramPoint source, ProgramPoint target, Call correspondingCall, Logger logger) {
		super(serialNumber, source, target, logger);
		m_CorrespondingCall = correspondingCall;
	}

	public Call getCorrespondingCall() {
		return m_CorrespondingCall;
	}

	public ProgramPoint getCallerProgramPoint() {
		return (ProgramPoint) getCorrespondingCall().getSource();
	}

	/**
	 * The published attributes. Update this and getFieldValue() if you add new
	 * attributes.
	 */
	private final static String[] s_AttribFields = { "CallStatement", "PrettyPrintedStatements", "TransitionFormula",
			"OccurenceInCounterexamples" };

	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field == "CallStatement") {
			return m_CorrespondingCall.getCallStatement();
		} else if (field == "PrettyPrintedStatements") {
			return m_CorrespondingCall.getPrettyPrintedStatements();
		} else {
			return super.getFieldValue(field);
		}
	}

	public String getPrettyPrintedStatements() {
		return "Return - Corresponding call: " + m_CorrespondingCall.getPrettyPrintedStatements();
	}

	public CallStatement getCallStatement() {
		return m_CorrespondingCall.getCallStatement();
	}

	@Override
	public String toString() {
		return "return;";
	}

	@Override
	public TransFormula getAssignmentOfReturn() {
		return getTransitionFormula();
	}

	@Override
	public TransFormula getLocalVarsAssignmentOfCall() {
		return getCorrespondingCall().getLocalVarsAssignment();
	}

}
