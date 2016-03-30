/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import de.uni_freiburg.informatik.ultimate.model.annotation.Visualizable;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IInternalAction;

/**
 * Edge in a recursive control flow graph that represents the call of a
 * procedure, including execution of the procedure, returning to the caller and
 * update of the left hand side of a call statement.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class Summary extends CodeBlock implements IInternalAction {

	/**
	 * 
	 */
	private static final long serialVersionUID = 6048827510357561291L;

	private final CallStatement m_CallStatement;
	private final String m_PrettyPrintedStatements;
	
	@Visualizable
	private final boolean m_CalledProcedureHasImplementation;

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
			return m_CallStatement;
		} else if (field == "PrettyPrintedStatements") {
			return m_PrettyPrintedStatements;
		} else {
			return super.getFieldValue(field);
		}
	}

	Summary(int serialNumber, ProgramPoint source, ProgramPoint target, CallStatement st,
			boolean calledProcedureHasImplementation, Logger logger) {
		super(serialNumber, source, target, logger);
		m_CallStatement = st;
		m_CalledProcedureHasImplementation = calledProcedureHasImplementation;
		m_PrettyPrintedStatements = BoogiePrettyPrinter.print(st);
	}

	public boolean calledProcedureHasImplementation() {
		return m_CalledProcedureHasImplementation;
	}

	public CallStatement getCallStatement() {
		return m_CallStatement;
	}

	public String getPrettyPrintedStatements() {
		return m_PrettyPrintedStatements;
	}

	@Override
	public String toString() {
		return "SUMMARY";
	}

	@Override
	public TransFormula getTransformula() {
		return getTransitionFormula();
	}

}
